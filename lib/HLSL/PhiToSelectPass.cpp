///////////////////////////////////////////////////////////////////////////////
//                                                                           //
// .cpp                                                         //
// Copyright (C) Microsoft Corporation. All rights reserved.                 //
// This file is distributed under the University of Illinois Open Source     //
// License. See LICENSE.TXT for details.                                     //
//                                                                           //
// .                              //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////

#include "dxc/HLSL/DxilGenerationPass.h"
#include "dxc/HLSL/DxilModule.h"
#include "dxc/HLSL/DxilOperations.h"

#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/PredIteratorCache.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/Local.h"

#include <unordered_set>

using namespace llvm;

static const unsigned NumPhiThreashold = 12;

class PhiToSelectPass : public FunctionPass {
  PredIteratorCache Preds;

public:
  static char ID;
  PhiToSelectPass() : FunctionPass(ID) {}
  bool runOnFunction(Function &F) override;
  //std::unordered_set<Value *> ConvertedSelects;

  bool DoBasicBlock(BasicBlock &BB);

  static bool HasUsesInBasicBlock(Value *V, BasicBlock *BB) {
    for (User *U : V->users())
      if (auto I = dyn_cast<Instruction>(U))
        if (I->getParent() == BB)
          return true;
    return false;
  }

  static BasicBlock *GetCommonSinglePredecessorAndCond(BasicBlock *A, BasicBlock *B, Value **cond, BranchInst **Br) {
    *cond = nullptr;
    *Br = nullptr;

    if (!A || !B)
      return nullptr;

    auto AP = A->getSinglePredecessor();
    auto BP = B->getSinglePredecessor();

    if (!AP || AP != BP) {
      return nullptr;
    }

    if (auto BranchI = dyn_cast<BranchInst>(AP->getTerminator())) {
      if (BranchI->isConditional()) {
        *cond = BranchI->getCondition();
        *Br = BranchI;
        return AP;
      }
    }

    return nullptr;
  }

  static bool OnlyBranchesTo(const BasicBlock *From, const BasicBlock *To) {
    auto TI = From->getTerminator();
    if (auto BranchI = dyn_cast<BranchInst>(TI)) {
      if (BranchI->isUnconditional() &&
        BranchI->getSuccessor(0) == To)
      {
        return true;
      }
    }
    return false;
  }

  Function *MyF = nullptr;
  void DebugPrint(const char *banner) {
#if 1
    dbgs() << ">>>>>>> " << banner << "<<<<<<<<<<" << "\n";
    MyF->print(dbgs());
#endif
  }

  struct CandidatePHI {
    PHINode *PN = nullptr;

    BasicBlock *BBs[4] = {};
    Value *Incoming[4] = {};
    SmallVector<Instruction *, 5> Trees[4];

    Value *MiddleConds[2] = {};
    BranchInst *MiddleBranches[2] = {};
    SmallVector<Instruction *, 5> MiddleCondTrees[2];
    BasicBlock *MiddleBBs[2] = {};

    Value *TopCond = nullptr;
    BranchInst *TopBranch = nullptr;
    BasicBlock *TopBB = nullptr;
  };

  void MoveInstructions(BasicBlock *BB, Instruction *InsertionPoint) {
    while (!isa<TerminatorInst>(BB->getInstList().begin())) {
      auto I = BB->getInstList().begin();
      I->removeFromParent();
      I->insertBefore(InsertionPoint);
    }
  }

  void ConvertPhi(CandidatePHI &C, bool MoveCond) {
    if (MoveCond) {
      for (int i = 0; i < 2; i++) {
        MoveInstructions(C.MiddleBBs[i], C.TopBB->getTerminator());
        MoveInstructions(C.BBs[i*2], C.TopBB->getTerminator());
        MoveInstructions(C.BBs[i*2+1], C.TopBB->getTerminator());
      }
    }

    IRBuilder<> Builder(C.PN);
    Value *Middle0 = Builder.CreateSelect(C.MiddleConds[0], C.Incoming[0], C.Incoming[1]);
    Value *Middle1 = Builder.CreateSelect(C.MiddleConds[1], C.Incoming[2], C.Incoming[3]);
    Value *Final = Builder.CreateSelect(C.TopCond, Middle0, Middle1);

    C.PN->replaceAllUsesWith(Final);
    C.PN->eraseFromParent();
  }

  typedef std::unordered_map<BasicBlock *, SmallPtrSet<Instruction *, 5> > BlockInstructions;

  bool MarkInstructions(Value *V, BasicBlock *BB, BlockInstructions &BIs) {
    if (auto I = dyn_cast<Instruction>(V)) {
      if (!BIs.count(BB)) {
        BIs[BB] = SmallPtrSet<Instruction *, 5>();
      }
      if (I->getParent() != BB) {
        return true;
      }
      BIs[BB].insert(I);

      for (unsigned j = 0; j < I->getNumOperands(); j++) {
        if (!MarkInstructions(I->getOperand(j), BB, BIs)) {
          return false;
        }
      }

      return true;
    }
    else if (auto C = dyn_cast<Argument>(V)) {
      return true;
    }
    else if (auto C = dyn_cast<Constant>(V)) {
      if (C->canTrap()) {
        return false;
      }

      return true;
    }

    return false;
  }

  bool GetCandidatePhi(PHINode *PN, CandidatePHI &C, BlockInstructions &BIs) {
    BasicBlock *TheBB = PN->getParent();
    C.PN = PN;

    if (PN->getNumIncomingValues() == 4) {
      if (Preds.get(TheBB).size() != 4) {
        return false;
      }

      for (unsigned i = 0; i < 4; i++) {
        C.BBs[i] = PN->getIncomingBlock(i);
        if (!C.BBs[i])
          return false;
        if (!OnlyBranchesTo(C.BBs[i], TheBB))
          return false;

        C.Incoming[i] = PN->getIncomingValue(i);

        if (!MarkInstructions(C.Incoming[i], C.BBs[i], BIs)) {
          return false;
        }
      }

      C.MiddleBBs[0] = GetCommonSinglePredecessorAndCond(C.BBs[0], C.BBs[1], &C.MiddleConds[0], &C.MiddleBranches[0]);
      C.MiddleBBs[1] = GetCommonSinglePredecessorAndCond(C.BBs[2], C.BBs[3], &C.MiddleConds[1], &C.MiddleBranches[1]);

      if (!C.MiddleBBs[0] || !C.MiddleBBs[1])
        return false;

      for (int i = 0; i < 2; i++) {
        if (!MarkInstructions(C.MiddleConds[i], C.MiddleBBs[i], BIs)) {
          return false;
        }
      }

      C.TopBB = GetCommonSinglePredecessorAndCond(C.MiddleBBs[0], C.MiddleBBs[1], &C.TopCond, &C.TopBranch);
      if (!C.TopBB)
        return false;

      return true;
    }
    else if (PN->getNumIncomingValues() == 2) {
      return false;
    }

    return false;
  }

};


bool PhiToSelectPass::DoBasicBlock(BasicBlock &BB) {
  SmallVector<CandidatePHI, NumPhiThreashold> Phis;
  BlockInstructions BIs;

  // Go through first few PHI's to see if we can
  // convert them.
  for (auto &BBI : BB) {
    Instruction &I = BBI;
    if (auto PN = dyn_cast<PHINode>(&I)) {
      if (Phis.size() >= NumPhiThreashold) {
        return false;
      }
      CandidatePHI Candidate;
      if (!GetCandidatePhi(PN, Candidate, BIs)) {
        return false;
      }
      Phis.push_back(Candidate);
    }
    else {
      break;
    }
  }

  // Don't have anythiung to combine.
  if (Phis.size() == 0) {
    return false;
  }
  if (BIs.size() > 6) {
    return false;
  }

  // If there are any instructions that we haven't marked
  // to pull out, then we can't actually get rid of any control
  // flow. Abort.
  for (auto It = BIs.begin(); It != BIs.end(); It++) {
    for (auto I = It->first->getInstList().begin(); !isa<TerminatorInst>(I); I++) {
      if (!It->second.count(I) && !isa<DbgInfoIntrinsic>(I)) {
        return false;
      }
    }
  }

  for (auto &C : Phis) {
    ConvertPhi(C, Phis.begin() == &C);
  }
  return true;

}

bool PhiToSelectPass::runOnFunction(Function &F) {
  if (F.getBasicBlockList().size() == 1 && (*F.begin()).getInstList().size() == 1) { return false; }
  this->MyF = &F;

  bool Changed = false;
  for (auto &FI : F) {
    BasicBlock &BB = FI;
    Changed |= DoBasicBlock(BB);
  }

  return Changed;
}

char PhiToSelectPass::ID = 0;

FunctionPass *llvm::createPhiToSelectPassPass() { return new PhiToSelectPass(); }


INITIALIZE_PASS(PhiToSelectPass, "phi-to-select-pass",
                "Pass to turn phi to selects", false, false)
