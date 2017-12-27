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
#include "llvm/IR/IRBuilder.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/Local.h"

#include <unordered_set>

using namespace llvm;

static const unsigned NumPhiThreashold = 3;

class PhiToSelectPass : public FunctionPass {
  PredIteratorCache Preds;

public:
  static char ID;
  PhiToSelectPass() : FunctionPass(ID) {}
  bool runOnFunction(Function &F) override;

  Function *MyF = nullptr;

  // - All values in tree defined in same BB.
  // - Tree is totally linear.
  static bool GetTrivialTree_(Value *V, BasicBlock *BB, std::unordered_set<User *> &Seen, SmallVector<Instruction *, 5> &Tree) {
    if (auto I = dyn_cast<Instruction>(V)) {
      if (I->getParent() != BB)
        return true;
      if (dyn_cast<PHINode>(I))
        return false;

      if (Tree.size() > 0) {
        for (auto Use : I->users()) {
          // If V is an instruction used by something
          // that's not part of the tree
          if (Seen.find(Use) == Seen.end()) {
            return false;
          }
        }
      }

      Tree.push_back(I);
      Seen.insert(I);
      for (Value *Op : I->operands()) {
        if (!GetTrivialTree_(Op, BB, Seen, Tree))
          return false;
      }

      return true;
    }
    else if (dyn_cast<Constant>(V)) {
      return true;
    }

    return false;
  }

  static bool HasUsesInBasicBlock(Value *V, BasicBlock *BB) {
    for (User *U : V->users())
      if (auto I = dyn_cast<Instruction>(U))
        if (I->getParent() == BB)
          return true;
    return false;
  }

  static bool GetTrivialTree(Value *V, BasicBlock *BB, SmallVector<Instruction *, 5> &Tree) {
    std::unordered_map<const Instruction *, unsigned> Order;
    std::unordered_set<User *> Seen;
    Tree.clear();

    unsigned i = 0;
    for (Instruction &I : BB->getInstList()) {
      Order[&I] = i++;
    }

    if (!GetTrivialTree_(V, BB, Seen, Tree)) {
      return false;
    }

    std::sort(Tree.begin(), Tree.end(), [&](const Instruction *A, const Instruction *B) {
      return Order[A] < Order[B];
    });
    return true;
  }

  static BasicBlock *GetCommonSinglePredecessorAndCond(BasicBlock *A, BasicBlock *B, Value **cond) {
    *cond = nullptr;

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

  template<unsigned N>
  static void MoveTreeBefore(SmallVector<Instruction *, N> &Tree, Instruction *InsertionPoint) {
      for (auto I : Tree) {
        I->removeFromParent();
        I->insertBefore(InsertionPoint);
      }
  }

  void DebugPrint(const char *banner) {
    dbgs() << ">>>>>>> " << banner << "<<<<<<<<<<" << "\n";
    MyF->print(dbgs());
  }

  bool ConvertPhi(PHINode *PN) {
    BasicBlock *TheBB = PN->getParent();

    if (PN->getNumIncomingValues() == 4) {
      if (Preds.get(TheBB).size() != 4) {
        return false;
      }

      BasicBlock *BBs[4] = {};
      Value *Incoming[4] = {};
      SmallVector<Instruction *, 5> Trees[4];
      for (unsigned i = 0; i < 4; i++) {
        BBs[i] = PN->getIncomingBlock(i);
        if (!BBs[i])
          return false;
        if (!OnlyBranchesTo(BBs[i], TheBB))
          return false;

        Incoming[i] = PN->getIncomingValue(i);
        // Get the use def chain that's in BB and results in 
        // the incoming value.
        if (!GetTrivialTree(Incoming[i], BBs[i], Trees[i])) {
          return false;
        }

        // Incoming value is used in the incoming BB
        if (HasUsesInBasicBlock(Incoming[i], BBs[i])) {
          return false;
        }
      }

      Value *NextConds[2] = {};
      SmallVector<Instruction *, 5> NextCondTrees[2];
      BasicBlock *NextBBs[2] = {
        GetCommonSinglePredecessorAndCond(BBs[0], BBs[1], &NextConds[0]),
        GetCommonSinglePredecessorAndCond(BBs[2], BBs[3], &NextConds[1]),
      };

      if (!NextBBs[0] || !NextBBs[1])
        return false;

      for (int i = 0; i < 2; i++) {
        // If the middle conds are not used just for
        // branching, then the graph is more complicated.
        // abort.
        if (NextConds[i]->getNumUses() > 1) {
          return false;
        }

        if (!GetTrivialTree(NextConds[i], NextBBs[i], NextCondTrees[i])) {
          return false;
        }
      }

      Value *TopCond = nullptr;
      BasicBlock *TopBB = GetCommonSinglePredecessorAndCond(NextBBs[0], NextBBs[1], &TopCond);
      if (!TopBB)
        return false;


      for (unsigned i = 0; i < 4; i++) {
        MoveTreeBefore(Trees[i], PN);
      }

      MoveTreeBefore(NextCondTrees[0], PN);
      MoveTreeBefore(NextCondTrees[1], PN);

      DebugPrint("After moving cond");

      IRBuilder<> Builder(PN);
      Value *Next0 = Builder.CreateSelect(NextConds[0], Incoming[0], Incoming[1]);
      Value *Next1 = Builder.CreateSelect(NextConds[1], Incoming[2], Incoming[3]);
      Value *Final = Builder.CreateSelect(TopCond, Next0, Next1);

      DebugPrint("After moving cond");

      PN->replaceAllUsesWith(Final);
      PN->eraseFromParent();

      return true;
    }
    else if (PN->getNumIncomingValues() == 2) {
      return false;
    }

    return false;
  }

};

bool PhiToSelectPass::runOnFunction(Function &F) {
  this->MyF = &F;

  bool Changed = false;
  for (auto &FI : F) {
    BasicBlock &BB = FI;
    SmallVector<PHINode *, NumPhiThreashold> Phis;

    int NumPhi = 0;
    for (auto &BBI : BB) {
      Instruction &I = BBI;
      if (auto PN = dyn_cast<PHINode>(&I)) {
        if (NumPhi >= NumPhiThreashold) {
          return false;
        }
        Phis.push_back(PN);
        NumPhi++;
      }
    }

    for (int i = Phis.size() - 1; i >= 0; i--) {
      auto PN = Phis[i];
      Changed |= ConvertPhi(PN);
    }
  }

  return Changed;
}

char PhiToSelectPass::ID = 0;

FunctionPass *llvm::createPhiToSelectPassPass() { return new PhiToSelectPass(); }


INITIALIZE_PASS(PhiToSelectPass, "phi-to-select-pass",
                "Pass to turn phi to selects", false, false)
