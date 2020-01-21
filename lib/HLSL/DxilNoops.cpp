///////////////////////////////////////////////////////////////////////////////
//                                                                           //
// DxilNoops.cpp                                                             //
// Copyright (C) Microsoft Corporation. All rights reserved.                 //
// This file is distributed under the University of Illinois Open Source     //
// License. See LICENSE.TXT for details.                                     //
//                                                                           //
// Passes to insert dx.noops() and replace them with llvm.donothing()        //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Support/raw_os_ostream.h"

#include "dxc/HLSL/DxilNoops.h"

using namespace llvm;

namespace {
StringRef kNoopName = "dx.noop";
StringRef kPreservePrefix = "dx.preserve.";
StringRef kNothingName = "dx.nothing";
StringRef kPreserveName = "dx.preserve.value";
}

bool hlsl::IsDxilPreserve(const Value *V) {
  if (const CallInst *CI = dyn_cast<CallInst>(V))
    if (Function *F = CI->getCalledFunction())
      return F->getName().startswith(kPreservePrefix);
  return false;
}

Value *hlsl::GetDxilPreserveSrc(Value *V) {
  assert(IsDxilPreserve(V));
  CallInst *CI = cast<CallInst>(V);
  return CI->getArgOperand(0);
}

//==========================================================
// Insertion pass
//

namespace {

Function *GetOrCreateNoopF(Module &M) {
  LLVMContext &Ctx = M.getContext();
  FunctionType *FT = FunctionType::get(Type::getVoidTy(Ctx), false);
  Function *NoopF = cast<Function>(M.getOrInsertFunction(::kNoopName, FT));
  NoopF->addFnAttr(Attribute::AttrKind::Convergent);
  return NoopF;
}

class DxilInsertNoops : public FunctionPass {
public:
  static char ID;
  DxilInsertNoops() : FunctionPass(ID) {
    initializeDxilInsertNoopsPass(*PassRegistry::getPassRegistry());
  }

  bool runOnFunction(Function &F) override;
  const char *getPassName() const override { return "Dxil Insert Noops"; }
};

char DxilInsertNoops::ID;
}

bool DxilInsertNoops::runOnFunction(Function &F) {
  Module &M = *F.getParent();
  Function *NoopF = nullptr;
  SmallDenseMap<Type *, Function *> PreserveFunctions;
  bool Changed = false;

  // Find instructions where we want to insert nops
  for (BasicBlock &BB : F) {
    for (BasicBlock::iterator It = BB.begin(), E = BB.end(); It != E;) {
      bool InsertNop = false;
      Value *CopySource = nullptr;
      Instruction &I = *(It++);
      Value *PrevValuePtr = nullptr;

      // If we are calling a real function, insert one
      // at the callsite.
      if (CallInst *Call = dyn_cast<CallInst>(&I)) {
        if (Function *F = Call->getCalledFunction()) {
          if (!F->isDeclaration())
            InsertNop = true;
        }
      }
      else if (MemCpyInst *MC = dyn_cast<MemCpyInst>(&I)) {
        InsertNop = true;
      }
      // If we have a copy, e.g:
      //     float x = 0;
      //     float y = x;    <---- copy
      // insert a nop there.
      else if (StoreInst *Store = dyn_cast<StoreInst>(&I)) {
        Value *V = Store->getValueOperand();
        if (isa<Constant>(V)) {
          InsertNop = true;
        }
        else {
          InsertNop = true;
          CopySource = V;
          PrevValuePtr = Store->getPointerOperand();
        }
      }
      // If we have a return, just to be safe.
      else if (ReturnInst *Ret = dyn_cast<ReturnInst>(&I)) {
        InsertNop = true;
      }

      // Do the insertion
      if (InsertNop) {
        if (CopySource &&
          !CopySource->getType()->isAggregateType() &&
          !CopySource->getType()->isPointerTy())
        {
          Type *Ty = CopySource->getType()->getScalarType();

          Function *PreserveF = PreserveFunctions[Ty];
          if (!PreserveF) {
            std::string str = kPreservePrefix;
            raw_string_ostream os(str);
            Ty->print(os);
            os.flush();

            FunctionType *FT = FunctionType::get(Ty, { Ty, Ty }, false);
            PreserveF = cast<Function>(M.getOrInsertFunction(str, FT));
            PreserveF->addFnAttr(Attribute::AttrKind::ReadNone);
            PreserveF->addFnAttr(Attribute::AttrKind::NoUnwind);
            PreserveFunctions[Ty] = PreserveF;
          }

          if (CopySource->getType()->isVectorTy()) {
            Type *VecTy = CopySource->getType();

            SmallVector<Value *, 4> Elements;
            IRBuilder<> B(&I);
            Instruction *Last_Value_Vec = B.CreateLoad(PrevValuePtr);

            for (unsigned i = 0; i < VecTy->getVectorNumElements(); i++) {
              auto *EE = B.CreateExtractElement(CopySource, i);
              Value *Last_Value = B.CreateExtractElement(Last_Value_Vec, i);
              Instruction *Preserve = CallInst::Create(PreserveF, ArrayRef<Value *> { EE, Last_Value }, "", &I);
              Preserve->setDebugLoc(I.getDebugLoc());
              Elements.push_back(Preserve);
            }

            Value *Vec = UndefValue::get(VecTy);
            for (unsigned i = 0; i < Elements.size(); i++) {
              Vec = B.CreateInsertElement(Vec, Elements[i], i);
            }

            I.replaceUsesOfWith(CopySource, Vec);
          }
          else {
            IRBuilder<> B(&I);
            Instruction *Last_Value = B.CreateLoad(PrevValuePtr);
            Instruction *Preserve = CallInst::Create(PreserveF, ArrayRef<Value *> { CopySource, Last_Value }, "", &I);
            Preserve->setDebugLoc(I.getDebugLoc());
            I.replaceUsesOfWith(CopySource, Preserve);
          }
        }
        else {
          if (!NoopF)
            NoopF = GetOrCreateNoopF(M);

          CallInst *Noop = CallInst::Create(NoopF, {}, &I);
          Noop->setDebugLoc(I.getDebugLoc());
        }
        Changed = true;
      }
    }
  }

  return Changed;
}

Pass *llvm::createDxilInsertNoopsPass() {
  return new DxilInsertNoops();
}

INITIALIZE_PASS(DxilInsertNoops, "dxil-insert-noops", "Dxil Insert Noops", false, false)


//==========================================================
// Finalize pass
//

namespace {

class DxilFinalizeNoops : public ModulePass {
public:
  static char ID;
  GlobalVariable *NothingGV = nullptr;

  DxilFinalizeNoops() : ModulePass(ID) {
    initializeDxilFinalizeNoopsPass(*PassRegistry::getPassRegistry());
  }

  Instruction *GetFinalNoopInst(Module &M, Instruction *InsertBefore) {
  if (!NothingGV) {
    NothingGV = M.getGlobalVariable(kNothingName);
    if (!NothingGV) {
      Type *i32Ty = Type::getInt32Ty(M.getContext());
      NothingGV = new GlobalVariable(M,
        i32Ty, true,
        llvm::GlobalValue::InternalLinkage,
        llvm::ConstantInt::get(i32Ty, 0), kNothingName);
    }
  }

  return new llvm::LoadInst(NothingGV, nullptr, InsertBefore);
}

  bool LowerPreserves(Module &M);
  bool runOnModule(Module &M) override;
  const char *getPassName() const override { return "Dxil Finalize Noops"; }
};

char DxilFinalizeNoops::ID;
}

bool DxilFinalizeNoops::LowerPreserves(Module &M) {
  SmallVector<Function *, 4> PreserveFunctions;

  for (Function &F : M) {
    if (!F.isDeclaration())
      continue;
    if (F.getName().startswith(kPreservePrefix)) {
      PreserveFunctions.push_back(&F);
    }
  }

  bool Changed = false;

  struct Function_Context {
    Function *F;
    LoadInst *Load;
    std::map<Type *, Value *> Values;
  };

  std::map<Function *, Function_Context> Contexts;
  auto GetValue = [&](Function *F, Type *Ty) -> Value* {
    Function_Context &ctx = Contexts[F];
    if (!ctx.F) {
      ctx.F = F;
      BasicBlock *BB = &F->getEntryBlock();
      IRBuilder<> B(&BB->front());

      GlobalVariable *GV = M.getGlobalVariable(kPreserveName);
      if (!GV) {
        Type *i32Ty = B.getInt32Ty();
        GV = new GlobalVariable(M,
          i32Ty, true,
          llvm::GlobalValue::InternalLinkage,
          llvm::ConstantInt::get(i32Ty, 0), kPreserveName);
      }

      ctx.Load = B.CreateLoad(GV);
    }

    Value *&V = ctx.Values[Ty];
    if (!V) {
      IRBuilder<> B(ctx.Load->getNextNode());
      if (Ty->isIntegerTy()) {
        V = B.CreateTruncOrBitCast(ctx.Load, Ty);
      }
      else if (Ty->isFloatingPointTy()) {
        V = B.CreateSIToFP(ctx.Load, Ty);
      }
    }

    return V;
  };

  for (Function *PreserveF : PreserveFunctions) {
    for (User *U : PreserveF->users()) {
      CallInst *Preserve = cast<CallInst>(U);
      Function *F = Preserve->getParent()->getParent();

      IRBuilder<> B(Preserve->getNextNode());

      Value *Src = Preserve->getOperand(0);
      Type *Ty = Preserve->getType();

      if (Value *NopV = GetValue(F, Ty)) {
        Value *NewSrc = nullptr;
        if (Ty->isIntegerTy()) {
          NewSrc = B.CreateOr(Src, NopV);
        }
        else if (Ty->isFloatingPointTy()) {
          NewSrc = B.CreateFAdd(Src, NopV);
        }

        if (NewSrc) {
          if (Instruction *SrcI = dyn_cast<Instruction>(NewSrc)) {
            SrcI->setDebugLoc(Preserve->getDebugLoc());
          }
          Src = NewSrc;
        }
      }

      Preserve->replaceAllUsesWith(Src);
      Preserve->eraseFromParent();
    }

    assert(PreserveF->use_empty() && "dx.preserve calls must be all removed now");
    PreserveF->eraseFromParent();

    Changed = true;
  }

  return Changed;
}

// Replace all @dx.noop's with @llvm.donothing
bool DxilFinalizeNoops::runOnModule(Module &M) {

  bool Changed = false;

  Changed |= LowerPreserves(M);

  Function *NoopF = nullptr;
  for (Function &F : M) {
    if (!F.isDeclaration())
      continue;
    if (F.getName() == kNoopName) {
      NoopF = &F;
    }
  }

  if (NoopF) {
    for (auto It = NoopF->user_begin(), E = NoopF->user_end(); It != E;) {
      User *U = *(It++);
      CallInst *CI = cast<CallInst>(U);

      Instruction *Nop = GetFinalNoopInst(M, CI);
      Nop->setDebugLoc(CI->getDebugLoc());

      CI->eraseFromParent();
      Changed = true;
    }

    assert(NoopF->user_empty() && "dx.noop calls must be all removed now");
    NoopF->eraseFromParent();

  }

  return Changed;
}

Pass *llvm::createDxilFinalizeNoopsPass() {
  return new DxilFinalizeNoops();
}

INITIALIZE_PASS(DxilFinalizeNoops, "dxil-finalize-noops", "Dxil Finalize Noops", false, false)

