
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/DivergenceAnalysis.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"

#include "dxc/HLSL/DxilGenerationPass.h"
#include "dxc/HLSL/DxilModule.h"

using namespace llvm;

class PhiToSelect : public FunctionPass
{
  DivergenceAnalysis *DA = nullptr;
  Module *M = nullptr;
public:
  static char ID;
  PhiToSelect() : FunctionPass(ID) {}
  bool runOnFunction(Function &F) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;

  bool DoBasicBlock(BasicBlock &);
};

char PhiToSelect::ID = 0;
void PhiToSelect::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<DivergenceAnalysis>();
}

static bool HintToPreserveCF(Module *M, BranchInst *Br) {
  return false;
  if (Br->hasMetadataOtherThanDebugLoc()) {
    return true;
  }
  return false;
}

static BasicBlock *GetCommonSinglePredecessorAndCond(BasicBlock *A, BasicBlock *B, Value **cond, BranchInst **Br) {
  *cond = nullptr;
  *Br = nullptr;

  if (!A || !B)
    return nullptr;

  auto AP = A->getSinglePredecessor();
  auto BP = B->getSinglePredecessor();

  BasicBlock *TopBB = nullptr;
  if (AP == B) {
    TopBB = B;
  }
  else if (BP == A) {
    TopBB = A;
  }
  else {
    if (!AP || AP != BP) {
      return nullptr;
    }
    TopBB = AP;
  }

  if (auto BranchI = dyn_cast<BranchInst>(TopBB->getTerminator())) {
    if (BranchI->isConditional()) {
      *cond = BranchI->getCondition();
      *Br = BranchI;
      return TopBB;
    }
  }

  return nullptr;
}

template<unsigned N>
bool CheckDom(Value *V, BasicBlock *BB, SmallPtrSet<Instruction *, N> &InstToMove) {
  if (auto I = dyn_cast<Instruction>(V)) {
    if (I->getParent() != BB)
      return true;
    for (unsigned i = 0; i < I->getNumOperands(); i++) {
      auto *Op = I->getOperand(i);
      if (!CheckDom(Op, BB, InstToMove))
        return false;
    }

    return true;
  }
  else if (auto CV = dyn_cast<Constant>(V)) {
    if (CV->canTrap())
      return false;
    return true;
  }
  else if (dyn_cast<Argument>(V)) {
    return true;
  }
  return false;
}

struct MergeCandidate {
  BasicBlock *BB[2] = {};
  BranchInst *Br = nullptr;
  Value *Cond = nullptr;
};

template<unsigned N>
static bool HasInstructionsMissing(BasicBlock *BB, SmallPtrSet<Instruction *, N> &InstToMove) {
  for (auto BBI = BB->begin(); !isa<TerminatorInst>(BBI); BBI++) {
    Instruction &I = *BBI;
    if (!InstToMove.count(&I)) {
      return false;
    }
  }
  return true;
}

static void MoveAllInstsTo(BasicBlock *BB, Instruction *InsertPoint) {
  while (&*BB->begin() != BB->getTerminator()) {
    auto I = BB->begin();
    I->removeFromParent();
    I->insertBefore(InsertPoint);
  }
}

// Diamond:
//    Top
//   /   |
// B[0] B[1]
//   |  /
//    BB
template<unsigned N>
bool TryMergeDiamond(BasicBlock &BB, MergeCandidate &Candidate, SmallVector<PHINode *, N> &Phis) {
  auto TopBB = Candidate.Br->getParent();

  if (Candidate.BB[0]->getSingleSuccessor() != &BB || Candidate.BB[1]->getSingleSuccessor() != &BB) {
    return false;
  }

  SmallPtrSet<Instruction *, 5> Insts;
  for (auto PN : Phis) {
    if (!CheckDom(PN->getIncomingValueForBlock(Candidate.BB[0]), Candidate.BB[0], Insts) ||
      !CheckDom(PN->getIncomingValueForBlock(Candidate.BB[1]), Candidate.BB[1], Insts))
    {
      return false;
    }
  }

  if (HasInstructionsMissing(Candidate.BB[0], Insts) || HasInstructionsMissing(Candidate.BB[1], Insts)) {
    return false;
  }

  MoveAllInstsTo(Candidate.BB[0], TopBB->getTerminator());
  MoveAllInstsTo(Candidate.BB[1], TopBB->getTerminator());

  for (auto PN : Phis) {
    Value *IV[] = {
      PN->getIncomingValueForBlock(Candidate.BB[0]),
      PN->getIncomingValueForBlock(Candidate.BB[1]),
    };
    auto Sel = SelectInst::Create(Candidate.Cond, IV[0], IV[1], "", TopBB->getTerminator());
    PN->addIncoming(Sel, TopBB);

    PN->removeIncomingValue(Candidate.BB[0]);
    PN->removeIncomingValue(Candidate.BB[1]);
  }

  BranchInst::Create(&BB, TopBB->getTerminator());
  TopBB->getTerminator()->eraseFromParent();

  Candidate.BB[0]->eraseFromParent();
  Candidate.BB[1]->eraseFromParent();

  return true;
}

// Triangle:
//    Top _ 
//    |    MidBB
//    |   /
//    |  /
//    BB
template<unsigned N>
bool TryMergeTriangle(BasicBlock &BB, MergeCandidate &Candidate, SmallVector<PHINode *, N> &Phis) {
  auto TopBB = Candidate.Br->getParent();
  auto MidBB = Candidate.BB[0] == TopBB ? Candidate.BB[1] : Candidate.BB[0];
  

  if (MidBB->getSingleSuccessor() != &BB) {
    return false;
  }

  SmallPtrSet<Instruction *, 5> Insts;
  for (PHINode *PN : Phis) {
    if (!CheckDom(PN->getIncomingValueForBlock(MidBB), MidBB, Insts)) {
      return false;
    }
  }

  if (HasInstructionsMissing(MidBB, Insts)) {
    return false;
  }

  MoveAllInstsTo(MidBB, TopBB->getTerminator());

  for (PHINode *PN : Phis) {
    Value *IV[] = {
      PN->getIncomingValueForBlock(TopBB),
      PN->getIncomingValueForBlock(MidBB),
    };

    PN->removeIncomingValue(TopBB);
    auto Sel = SelectInst::Create(Candidate.Cond, IV[0], IV[1], "", TopBB->getTerminator());
    PN->addIncoming(Sel, TopBB);

    PN->removeIncomingValue(MidBB);
  }

  BranchInst::Create(&BB, TopBB->getTerminator());
  TopBB->getTerminator()->eraseFromParent();

  MidBB->eraseFromParent();

  return true;
}

template<unsigned N>
static bool TryMergeCandidate(BasicBlock &BB, MergeCandidate &Candidate, SmallVector<PHINode *, N> &Phis) {
  auto TopBB = Candidate.Br->getParent();
  if (TopBB == Candidate.BB[0] || TopBB == Candidate.BB[1]) {
    return TryMergeTriangle(BB, Candidate, Phis);
  }
  else {
    return TryMergeDiamond(BB, Candidate, Phis);
  }
  return false;
}

bool PhiToSelect::DoBasicBlock(BasicBlock &BB) {
  SmallVector<PHINode *, 32> Phis;

  for (Instruction &I : BB) {
    if (auto PN = dyn_cast<PHINode>(&I)) {
      // Doens't matter how many phi's. If 
      // we're merging, it means the control flow
      // is divergent, which means it doesn't matter
      // how many instructions there are in there.
      Phis.push_back(PN);
    }
    else {
      break;
    }
  }

  if (Phis.size() == 0) {
    return false;
  }
  SmallVector<MergeCandidate, 4> Candidates;

  auto PN = Phis.front();
  for (unsigned i = 0; i < PN->getNumIncomingValues(); i++) {
    auto BB1 = PN->getIncomingBlock(i);
    for (unsigned j = i+1; j < PN->getNumIncomingValues(); j++) {
      auto BB2 = PN->getIncomingBlock(j);
      MergeCandidate Candidate;
      if (GetCommonSinglePredecessorAndCond(BB1, BB2, &Candidate.Cond, &Candidate.Br)) {
        if (DA->isDivergent(Candidate.Cond) && !HintToPreserveCF(M, Candidate.Br)) {
          Candidate.BB[0] = BB1;
          Candidate.BB[1] = BB2;
          Candidates.push_back(Candidate);
        }
      }
    }
  }

  bool Changed = false;
  for (auto &Candidate : Candidates) {
    Changed |= TryMergeCandidate(BB, Candidate, Phis);
  }

  return Changed;
}

bool PhiToSelect::runOnFunction(Function &F) {

  M = F.getParent();
  DA = &getAnalysis<DivergenceAnalysis>();
  bool Changed = false;
  for (auto &FI : F) {
    while (1) {
      bool LocalChanged = DoBasicBlock(FI);
      if (!LocalChanged)
        break;
      Changed |= LocalChanged;
    }
  }
  return Changed;
}

FunctionPass *llvm::createPhiToSelectPass() { return new PhiToSelect(); }

INITIALIZE_PASS_BEGIN(PhiToSelect, "phi-to-sel",
                      "Straight line strength reduction", false, false)
INITIALIZE_PASS_DEPENDENCY(DivergenceAnalysis)
INITIALIZE_PASS_END(PhiToSelect, "phi-to-sel",
                    "Straight line strength reduction", false, false)