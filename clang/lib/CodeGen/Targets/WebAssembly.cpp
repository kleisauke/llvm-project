//===- WebAssembly.cpp ----------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "ABIInfoImpl.h"
#include "TargetInfo.h"

using namespace clang;
using namespace clang::CodeGen;

//===----------------------------------------------------------------------===//
// WebAssembly ABI Implementation
//
// This is a very simple ABI that relies a lot on DefaultABIInfo.
//===----------------------------------------------------------------------===//

class WebAssemblyABIInfo final : public ABIInfo {
  DefaultABIInfo defaultInfo;
  WebAssemblyABIKind Kind;

public:
  explicit WebAssemblyABIInfo(CodeGen::CodeGenTypes &CGT,
                              WebAssemblyABIKind Kind)
      : ABIInfo(CGT), defaultInfo(CGT), Kind(Kind) {}

private:
  ABIArgInfo classifyReturnType(QualType RetTy) const;
  ABIArgInfo classifyArgumentType(QualType Ty) const;

  // DefaultABIInfo's classifyReturnType and classifyArgumentType are
  // non-virtual, but computeInfo and EmitVAArg are virtual, so we
  // overload them.
  void computeInfo(CGFunctionInfo &FI) const override {
    if (!getCXXABI().classifyReturnType(FI))
      FI.getReturnInfo() = classifyReturnType(FI.getReturnType());
    for (auto &Arg : FI.arguments())
      Arg.info = classifyArgumentType(Arg.type);
  }

  RValue EmitVAArg(CodeGenFunction &CGF, Address VAListAddr, QualType Ty,
                   AggValueSlot Slot) const override;
};

class WebAssemblyTargetCodeGenInfo final : public TargetCodeGenInfo {
public:
  explicit WebAssemblyTargetCodeGenInfo(CodeGen::CodeGenTypes &CGT,
                                        WebAssemblyABIKind K)
      : TargetCodeGenInfo(std::make_unique<WebAssemblyABIInfo>(CGT, K)) {
    SwiftInfo =
        std::make_unique<SwiftABIInfo>(CGT, /*SwiftErrorInRegister=*/false);
  }

  void setTargetAttributes(const Decl *D, llvm::GlobalValue *GV,
                           CodeGen::CodeGenModule &CGM) const override {
    TargetCodeGenInfo::setTargetAttributes(D, GV, CGM);
    if (const auto *FD = dyn_cast_or_null<FunctionDecl>(D)) {
      if (const auto *Attr = FD->getAttr<WebAssemblyImportModuleAttr>()) {
        llvm::Function *Fn = cast<llvm::Function>(GV);
        llvm::AttrBuilder B(GV->getContext());
        B.addAttribute("wasm-import-module", Attr->getImportModule());
        Fn->addFnAttrs(B);
      }
      if (const auto *Attr = FD->getAttr<WebAssemblyImportNameAttr>()) {
        llvm::Function *Fn = cast<llvm::Function>(GV);
        llvm::AttrBuilder B(GV->getContext());
        B.addAttribute("wasm-import-name", Attr->getImportName());
        Fn->addFnAttrs(B);
      }
      if (const auto *Attr = FD->getAttr<WebAssemblyExportNameAttr>()) {
        llvm::Function *Fn = cast<llvm::Function>(GV);
        llvm::AttrBuilder B(GV->getContext());
        B.addAttribute("wasm-export-name", Attr->getExportName());
        Fn->addFnAttrs(B);
      }
    }

    if (auto *FD = dyn_cast_or_null<FunctionDecl>(D)) {
      llvm::Function *Fn = cast<llvm::Function>(GV);
      if (!FD->doesThisDeclarationHaveABody() && !FD->hasPrototype())
        Fn->addFnAttr("no-prototype");
    }
  }

  /// Return the WebAssembly externref reference type.
  virtual llvm::Type *getWasmExternrefReferenceType() const override {
    return llvm::Type::getWasm_ExternrefTy(getABIInfo().getVMContext());
  }
  /// Return the WebAssembly funcref reference type.
  virtual llvm::Type *getWasmFuncrefReferenceType() const override {
    return llvm::Type::getWasm_FuncrefTy(getABIInfo().getVMContext());
  }

  llvm::Function *getOrCreateWasmFunctionPointerThunk(
      CodeGenFunction &CGF, llvm::Value *OriginalFnPtr, QualType SrcType,
      QualType DstType) const override {
    llvm::Module &M = CGF.CGM.getModule();

    // Get the signatures.
    const FunctionProtoType *DstProtoType = DstType->getAs<PointerType>()
                                                ->getPointeeType()
                                                ->getAs<FunctionProtoType>();
    const FunctionProtoType *SrcProtoType = SrcType->getAs<PointerType>()
                                                ->getPointeeType()
                                                ->getAs<FunctionProtoType>();

    // Get the llvm function types.
    llvm::FunctionType *DstFunctionType = llvm::cast<llvm::FunctionType>(
        CGF.ConvertType(QualType(DstProtoType, 0)));
    llvm::FunctionType *SrcFunctionType = llvm::cast<llvm::FunctionType>(
        CGF.ConvertType(QualType(SrcProtoType, 0)));

    llvm::Type *ExpectedRtnType = SrcFunctionType->getReturnType();
    llvm::Type *RtnType = DstFunctionType->getReturnType();

    // Skip thunk generation if function types are already compatible.
    if (SrcFunctionType->getNumParams() == DstFunctionType->getNumParams() &&
        SrcFunctionType->isVarArg() == DstFunctionType->isVarArg() &&
        ExpectedRtnType == RtnType) {
      return nullptr;
    }

    // Construct the thunk function with the target (destination) signature.
    std::string ThunkName = getThunkName(OriginalFnPtr->getName().str(),
                                         DstProtoType, CGF.CGM.getContext());
    llvm::Function *Thunk = llvm::Function::Create(
        DstFunctionType, llvm::Function::InternalLinkage, ThunkName, M);

    // Build the thunk body.
    llvm::IRBuilder<> Builder(
        llvm::BasicBlock::Create(M.getContext(), "entry", Thunk));

    // Gather the arguments for calling the original function.
    SmallVector<llvm::Value *, 4> Args;
    llvm::Function::arg_iterator AI = Thunk->arg_begin();
    llvm::Function::arg_iterator AE = Thunk->arg_end();
    llvm::FunctionType::param_iterator PI = SrcFunctionType->param_begin();
    llvm::FunctionType::param_iterator PE = SrcFunctionType->param_end();

    for (; AI != AE && PI != PE; ++AI, ++PI)
      Args.push_back(Builder.CreateAggregateCast(AI, *PI));

    for (; PI != PE; ++PI)
      Args.push_back(llvm::PoisonValue::get(*PI));
    if (SrcFunctionType->isVarArg())
      for (; AI != AE; ++AI)
        Args.push_back(&*AI);

    // Create the call to the original function pointer.
    llvm::CallInst *Call =
        Builder.CreateCall(SrcFunctionType, OriginalFnPtr, Args);

    // Determine what value to return.
    if (RtnType->isVoidTy()) {
      Builder.CreateRetVoid();
    } else if (ExpectedRtnType->isVoidTy()) {
      Builder.CreateRet(llvm::PoisonValue::get(RtnType));
    } else {
      Builder.CreateRet(Builder.CreateAggregateCast(Call, RtnType));
    }

    return Thunk;
  }

private:
  // Build the thunk name: "%s_{OrigName}_{WasmSig}"
  std::string getThunkName(std::string OrigName,
                           const FunctionProtoType *DstProto,
                           const ASTContext &Ctx) const;
  char getTypeSig(const QualType &Ty, const ASTContext &Ctx) const;
};

/// Classify argument of given type \p Ty.
ABIArgInfo WebAssemblyABIInfo::classifyArgumentType(QualType Ty) const {
  Ty = useFirstFieldIfTransparentUnion(Ty);

  if (isAggregateTypeForABI(Ty)) {
    // Records with non-trivial destructors/copy-constructors should not be
    // passed by value.
    if (auto RAA = getRecordArgABI(Ty, getCXXABI()))
      return getNaturalAlignIndirect(Ty, getDataLayout().getAllocaAddrSpace(),
                                     RAA == CGCXXABI::RAA_DirectInMemory);
    // Ignore empty structs/unions.
    if (isEmptyRecord(getContext(), Ty, true))
      return ABIArgInfo::getIgnore();
    // Lower single-element structs to just pass a regular value. TODO: We
    // could do reasonable-size multiple-element structs too, using getExpand(),
    // though watch out for things like bitfields.
    if (const Type *SeltTy = isSingleElementStruct(Ty, getContext()))
      return ABIArgInfo::getDirect(CGT.ConvertType(QualType(SeltTy, 0)));
    // For the experimental multivalue ABI, fully expand all other aggregates
    if (Kind == WebAssemblyABIKind::ExperimentalMV) {
      const RecordType *RT = Ty->getAs<RecordType>();
      assert(RT);
      bool HasBitField = false;
      for (auto *Field : RT->getDecl()->fields()) {
        if (Field->isBitField()) {
          HasBitField = true;
          break;
        }
      }
      if (!HasBitField)
        return ABIArgInfo::getExpand();
    }
  }

  // Otherwise just do the default thing.
  return defaultInfo.classifyArgumentType(Ty);
}

ABIArgInfo WebAssemblyABIInfo::classifyReturnType(QualType RetTy) const {
  if (isAggregateTypeForABI(RetTy)) {
    // Records with non-trivial destructors/copy-constructors should not be
    // returned by value.
    if (!getRecordArgABI(RetTy, getCXXABI())) {
      // Ignore empty structs/unions.
      if (isEmptyRecord(getContext(), RetTy, true))
        return ABIArgInfo::getIgnore();
      // Lower single-element structs to just return a regular value. TODO: We
      // could do reasonable-size multiple-element structs too, using
      // ABIArgInfo::getDirect().
      if (const Type *SeltTy = isSingleElementStruct(RetTy, getContext()))
        return ABIArgInfo::getDirect(CGT.ConvertType(QualType(SeltTy, 0)));
      // For the experimental multivalue ABI, return all other aggregates
      if (Kind == WebAssemblyABIKind::ExperimentalMV)
        return ABIArgInfo::getDirect();
    }
  }

  // Otherwise just do the default thing.
  return defaultInfo.classifyReturnType(RetTy);
}

RValue WebAssemblyABIInfo::EmitVAArg(CodeGenFunction &CGF, Address VAListAddr,
                                     QualType Ty, AggValueSlot Slot) const {
  bool IsIndirect = isAggregateTypeForABI(Ty) &&
                    !isEmptyRecord(getContext(), Ty, true) &&
                    !isSingleElementStruct(Ty, getContext());
  return emitVoidPtrVAArg(CGF, VAListAddr, Ty, IsIndirect,
                          getContext().getTypeInfoInChars(Ty),
                          CharUnits::fromQuantity(4),
                          /*AllowHigherAlign=*/true, Slot);
}

std::unique_ptr<TargetCodeGenInfo>
CodeGen::createWebAssemblyTargetCodeGenInfo(CodeGenModule &CGM,
                                            WebAssemblyABIKind K) {
  return std::make_unique<WebAssemblyTargetCodeGenInfo>(CGM.getTypes(), K);
}

// Returns a character that represents the given QualType in a wasm signature.
// See getInvokeSig() in WebAssemblyAsmPrinter for related logic.
char WebAssemblyTargetCodeGenInfo::getTypeSig(const QualType &Ty,
                                              const ASTContext &Ctx) const {
  if (Ty->isAnyPointerType()) {
    return Ctx.getTypeSize(Ctx.VoidPtrTy) == 32 ? 'i' : 'j';
  }
  if (Ty->isIntegerType()) {
    return Ctx.getTypeSize(Ty) <= 32 ? 'i' : 'j';
  }
  if (Ty->isFloatingType()) {
    return Ctx.getTypeSize(Ty) <= 32 ? 'f' : 'd';
  }
  if (Ty->isVectorType()) {
    return 'V';
  }
  if (Ty->isWebAssemblyTableType()) {
    return 'F';
  }
  if (Ty->isWebAssemblyExternrefType()) {
    return 'X';
  }

  llvm_unreachable("Unhandled QualType");
}

std::string
WebAssemblyTargetCodeGenInfo::getThunkName(std::string OrigName,
                                           const FunctionProtoType *DstProto,
                                           const ASTContext &Ctx) const {
  std::string ThunkName = "__" + OrigName + "_";
  QualType RetTy = DstProto->getReturnType();
  if (RetTy->isVoidType()) {
    ThunkName += 'v';
  } else {
    ThunkName += getTypeSig(RetTy, Ctx);
  }
  for (unsigned i = 0; i < DstProto->getNumParams(); ++i) {
    ThunkName += getTypeSig(DstProto->getParamType(i), Ctx);
  }
  return ThunkName;
}
