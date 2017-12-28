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

static const unsigned NumPhiThreashold = 12;

class PhiToSelectPass : public FunctionPass {
  PredIteratorCache Preds;

public:
  static char ID;
  PhiToSelectPass() : FunctionPass(ID) {}
  bool runOnFunction(Function &F) override;
  //std::unordered_set<Value *> ConvertedSelects;

  Function *MyF = nullptr;

  // - All values in tree defined in same BB.
  // - Tree is totally linear.
  static bool GetTrivialTree_(Value *V, BasicBlock *BB, std::unordered_set<User *> &Seen, SmallVector<Instruction *, 5> &Tree) {
    if (auto I = dyn_cast<Instruction>(V)) {
      auto opcode = I->getOpcode();
      if (I->getParent() != BB)
        return true;
      if (dyn_cast<PHINode>(I))
        return false;

      if (opcode == Instruction::InsertElement) {
        printf("AAAAYYY\n");
      }

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
    else if (dyn_cast<Argument>(V)) {
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
    auto name = V->getName();
    if (name == "add58.i") {
      printf("AY\n");
    }
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

  bool CondUsedElsewhere(Value *Cond, BranchInst *Br) {
#if 0
    for (User *U : Cond->users()) {
      if (ConvertedSelects.find(U) == ConvertedSelects.end() && U != Br) {
        return true;
      }
    }
    return false;
#else
    return Cond->getNumUses() > 1;
#endif
  }

  struct CandidatePHI {
    PHINode *PN = nullptr;

    BasicBlock *BBs[4] = {};
    Value *Incoming[4] = {};
    SmallVector<Instruction *, 5> Trees[4];

    Value *NextConds[2] = {};
    BranchInst *NextBranches[2] = {};
    SmallVector<Instruction *, 5> NextCondTrees[2];
    BasicBlock *NextBBs[2] = {};

    Value *TopCond = nullptr;
    SmallVector<Instruction *, 5> TopCondTree;
    BranchInst *TopBranch = nullptr;
    BasicBlock *TopBB = nullptr;
  };


  void ConvertPhi(CandidatePHI &C, bool MoveCond) {
    if (MoveCond) {
      //DebugPrint("Before moving cond");
      MoveTreeBefore(C.TopCondTree, C.PN);
      MoveTreeBefore(C.NextCondTrees[0], C.PN);
      MoveTreeBefore(C.NextCondTrees[1], C.PN);
      //DebugPrint("After moving cond");
    }

    for (int i = 0; i < 4; i++) {
      MoveTreeBefore(C.Trees[i], C.PN);
    }


    //DebugPrint("Before adding select");
    IRBuilder<> Builder(C.PN);
    Value *Next0 = Builder.CreateSelect(C.NextConds[0], C.Incoming[0], C.Incoming[1]);
    Value *Next1 = Builder.CreateSelect(C.NextConds[1], C.Incoming[2], C.Incoming[3]);
    Value *Final = Builder.CreateSelect(C.TopCond, Next0, Next1);
    //ConvertedSelects.insert(Next0);
    //ConvertedSelects.insert(Next1);
    //ConvertedSelects.insert(Final);


    C.PN->replaceAllUsesWith(Final);
    C.PN->eraseFromParent();
    //DebugPrint("After adding select");
  }

  bool GetCandidatePhi(PHINode *PN, CandidatePHI &C) {
    BasicBlock *TheBB = PN->getParent();
    C.PN = PN;

    if (PN->getNumIncomingValues() == 4) {
      if (Preds.get(TheBB).size() != 4) {
        return false;
      }

      //BasicBlock *BBs[4] = {};
      //Value *Incoming[4] = {};
      //SmallVector<Instruction *, 5> Trees[4];
      for (unsigned i = 0; i < 4; i++) {
        C.BBs[i] = PN->getIncomingBlock(i);
        if (!C.BBs[i])
          return false;
        if (!OnlyBranchesTo(C.BBs[i], TheBB))
          return false;

        C.Incoming[i] = PN->getIncomingValue(i);
        // Get the use def chain that's in BB and results in 
        // the incoming value.
        if (!GetTrivialTree(C.Incoming[i], C.BBs[i], C.Trees[i])) {
          return false;
        }

        // Incoming value is used in the incoming BB
        if (HasUsesInBasicBlock(C.Incoming[i], C.BBs[i])) {
          return false;
        }
      }

      //Value *NextConds[2] = {};
      //BranchInst *NextBranches[2] = {};
      //SmallVector<Instruction *, 5> NextCondTrees[2];
      //BasicBlock *NextBBs[2] = {
      C.NextBBs[0] = GetCommonSinglePredecessorAndCond(C.BBs[0], C.BBs[1], &C.NextConds[0], &C.NextBranches[0]);
      C.NextBBs[1] = GetCommonSinglePredecessorAndCond(C.BBs[2], C.BBs[3], &C.NextConds[1], &C.NextBranches[1]);

      if (!C.NextBBs[0] || !C.NextBBs[1])
        return false;

      for (int i = 0; i < 2; i++) {
        // If the middle conds are not used just for
        // branching, then the graph is more complicated.
        // abort.
        if (CondUsedElsewhere(C.NextConds[i], C.NextBranches[i])) {
          return false;
        }

        if (!GetTrivialTree(C.NextConds[i], C.NextBBs[i], C.NextCondTrees[i])) {
          return false;
        }
      }

      //Value *TopCond = nullptr;
      //BranchInst *TopBranch = nullptr;
      //BasicBlock *TopBB = GetCommonSinglePredecessorAndCond(C.NextBBs[0], C.NextBBs[1], &C.TopCond, &C.TopBranch);
      C.TopBB = GetCommonSinglePredecessorAndCond(C.NextBBs[0], C.NextBBs[1], &C.TopCond, &C.TopBranch);
      if (!C.TopBB)
        return false;

      if (CondUsedElsewhere(C.TopCond, C.TopBranch)) {
        return false;
      }

      if (!GetTrivialTree(C.TopCond, C.TopBB, C.TopCondTree)) {
        return false;
      }

      return true;
    }
    else if (PN->getNumIncomingValues() == 2) {
      return false;
    }

    return false;
  }

};

bool PhiToSelectPass::runOnFunction(Function &F) {
  if (F.getBasicBlockList().size() == 1 && (*F.begin()).getInstList().size() == 1) { return false; }
  this->MyF = &F;
  DebugPrint("Before anything");

  bool Changed = false;
  for (auto &FI : F) {
    BasicBlock &BB = FI;
    //SmallVector<PHINode *, NumPhiThreashold> Phis;
    SmallVector<CandidatePHI, NumPhiThreashold> Phis;

    for (auto &BBI : BB) {
      Instruction &I = BBI;
      if (auto PN = dyn_cast<PHINode>(&I)) {
        if (Phis.size() >= NumPhiThreashold) {
          return false;
        }
        CandidatePHI Candidate;
        if (!GetCandidatePhi(PN, Candidate)) {
          Phis.clear();
          break;
        }
        Phis.push_back(Candidate);
      }
      else {
        break;
      }
    }

    int i = 0;
    for (auto &C : Phis) {
      ConvertPhi(C, i == 0);
      Changed = true;
      i++;
    }
  }

  DebugPrint("After everything");
  return Changed;
}

char PhiToSelectPass::ID = 0;

FunctionPass *llvm::createPhiToSelectPassPass() { return new PhiToSelectPass(); }


INITIALIZE_PASS(PhiToSelectPass, "phi-to-select-pass",
                "Pass to turn phi to selects", false, false)
