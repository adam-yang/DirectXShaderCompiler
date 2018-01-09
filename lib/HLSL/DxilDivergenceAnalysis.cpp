//===- DxilDivergenceAnalysis.cpp ----- Divergence Analysis Implementation -==//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file is mostly copied over from Divergence analysis but having 
// replaced the TargetTransformInformation with a local DXIL specific
// definition.
//
// Ideally, we would be creating and registering a TargetMachine for DXIL,
// and implement a number of Target Information for it and use the default
// DivergenceAnalysis.
//
// The HLSL changes marked in the file are where it differs from the default
// Divergence analysis.
//
//===----------------------------------------------------------------------===//

//#include "llvm/Analysis/DivergenceAnalysis.h" // HLSL Change
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/PostDominators.h"
//#include "llvm/Analysis/TargetTransformInfo.h" // HLSL Change
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"
#include <vector>
#include "dxc/HLSL/DxilOperations.h" // HLSL Change
#include "dxc/HLSL/DxilDivergenceAnalysis.h" // HLSL Change
#include "llvm/IR/Module.h" // HLSL Change
using namespace llvm;
using namespace hlsl; // HLSL Change

// HLSL Change - Begin
bool IsDxilOpSourceOfDivergence(const CallInst *CI, const OP *hlslOP,
                                bool ThreadGroup) {

  DXIL::OpCode opcode = hlslOP->GetDxilOpFuncCallInst(CI);
  switch (opcode) {
  case DXIL::OpCode::AtomicBinOp:
  case DXIL::OpCode::AtomicCompareExchange:
  case DXIL::OpCode::LoadInput:
  case DXIL::OpCode::BufferUpdateCounter:
  case DXIL::OpCode::CycleCounterLegacy:
  case DXIL::OpCode::DomainLocation:
  case DXIL::OpCode::Coverage:
  case DXIL::OpCode::EvalCentroid:
  case DXIL::OpCode::EvalSampleIndex:
  case DXIL::OpCode::EvalSnapped:
  case DXIL::OpCode::FlattenedThreadIdInGroup:
  case DXIL::OpCode::GSInstanceID:
  case DXIL::OpCode::InnerCoverage:
  case DXIL::OpCode::LoadOutputControlPoint:
  case DXIL::OpCode::LoadPatchConstant:
  case DXIL::OpCode::OutputControlPointID:
  case DXIL::OpCode::PrimitiveID:
  case DXIL::OpCode::RenderTargetGetSampleCount:
  case DXIL::OpCode::RenderTargetGetSamplePosition:
  case DXIL::OpCode::ThreadId:
  case DXIL::OpCode::ThreadIdInGroup:
    return true;
  case DXIL::OpCode::GroupId:
    return !ThreadGroup;
  default:
    return false;
  }
}

// Override the actual TargetTransformInfo type.
//
//
class TargetTransformInfo {
  OP m_pHlslOP;
  bool m_isThreadGroup;
public:
  TargetTransformInfo(Module *M, bool isThreadGroup) :
    m_pHlslOP(M->getContext(), M),
    m_isThreadGroup(isThreadGroup)
  {}
  bool isSourceOfDivergence(const Value *V) const {
    if (const Argument *A = dyn_cast<Argument>(V))
      return true;

    // Atomics are divergent because they are executed sequentially: when an
    // atomic operation refers to the same address in each thread, then each
    // thread after the first sees the value written by the previous thread as
    // original value.
    if (isa<AtomicRMWInst>(V) || isa<AtomicCmpXchgInst>(V))
      return true;

    if (const CallInst *CI = dyn_cast<CallInst>(V)) {
      // Assume none dxil instrincis function calls are a source of divergence.
      if (!m_pHlslOP.IsDxilOpFuncCallInst(CI))
        return true;
      return IsDxilOpSourceOfDivergence(CI, &m_pHlslOP, m_isThreadGroup);
    }

    return false;
  }
  bool hasBranchDivergence() { return true; }
};
// HLSL Change - End

namespace {

class DivergencePropagator {
public:
  DivergencePropagator(Function &F, TargetTransformInfo &TTI, DominatorTree &DT,
                       PostDominatorTree &PDT, DenseSet<const Value *> &DV)
      : F(F), TTI(TTI), DT(DT), PDT(PDT), DV(DV) {}
  void populateWithSourcesOfDivergence();
  void propagate();

private:
  // A helper function that explores data dependents of V.
  void exploreDataDependency(Value *V);
  // A helper function that explores sync dependents of TI.
  void exploreSyncDependency(TerminatorInst *TI);
  // Computes the influence region from Start to End. This region includes all
  // basic blocks on any simple path from Start to End.
  void computeInfluenceRegion(BasicBlock *Start, BasicBlock *End,
                              DenseSet<BasicBlock *> &InfluenceRegion);
  // Finds all users of I that are outside the influence region, and add these
  // users to Worklist.
  void findUsersOutsideInfluenceRegion(
      Instruction &I, const DenseSet<BasicBlock *> &InfluenceRegion);

  Function &F;
  TargetTransformInfo &TTI;
  DominatorTree &DT;
  PostDominatorTree &PDT;
  std::vector<Value *> Worklist; // Stack for DFS.
  DenseSet<const Value *> &DV;   // Stores all divergent values.
};

void DivergencePropagator::populateWithSourcesOfDivergence() {
  Worklist.clear();
  DV.clear();
  for (auto &I : inst_range(F)) {
    if (TTI.isSourceOfDivergence(&I)) {
      Worklist.push_back(&I);
      DV.insert(&I);
    }
  }

  for (auto &Arg : F.args()) {
    if (TTI.isSourceOfDivergence(&Arg)) {
      Worklist.push_back(&Arg);
      DV.insert(&Arg);
    }
  }
}

void DivergencePropagator::exploreSyncDependency(TerminatorInst *TI) {
  // Propagation rule 1: if branch TI is divergent, all PHINodes in TI's
  // immediate post dominator are divergent. This rule handles if-then-else
  // patterns. For example,
  //
  // if (tid < 5)
  //   a1 = 1;
  // else
  //   a2 = 2;
  // a = phi(a1, a2); // sync dependent on (tid < 5)
  BasicBlock *ThisBB = TI->getParent();
  BasicBlock *IPostDom = PDT.getNode(ThisBB)->getIDom()->getBlock();
  if (IPostDom == nullptr)
    return;

  for (auto I = IPostDom->begin(); isa<PHINode>(I); ++I) {
    // A PHINode is uniform if it returns the same value no matter which path is
    // taken.
    if (!cast<PHINode>(I)->hasConstantValue() && DV.insert(&*I).second)
      Worklist.push_back(&*I);
  }

  // Propagation rule 2: if a value defined in a loop is used outside, the user
  // is sync dependent on the condition of the loop exits that dominate the
  // user. For example,
  //
  // int i = 0;
  // do {
  //   i++;
  //   if (foo(i)) ... // uniform
  // } while (i < tid);
  // if (bar(i)) ...   // divergent
  //
  // A program may contain unstructured loops. Therefore, we cannot leverage
  // LoopInfo, which only recognizes natural loops.
  //
  // The algorithm used here handles both natural and unstructured loops.  Given
  // a branch TI, we first compute its influence region, the union of all simple
  // paths from TI to its immediate post dominator (IPostDom). Then, we search
  // for all the values defined in the influence region but used outside. All
  // these users are sync dependent on TI.
  DenseSet<BasicBlock *> InfluenceRegion;
  computeInfluenceRegion(ThisBB, IPostDom, InfluenceRegion);
  // An insight that can speed up the search process is that all the in-region
  // values that are used outside must dominate TI. Therefore, instead of
  // searching every basic blocks in the influence region, we search all the
  // dominators of TI until it is outside the influence region.
  BasicBlock *InfluencedBB = ThisBB;
  while (InfluenceRegion.count(InfluencedBB)) {
    for (auto &I : *InfluencedBB)
      findUsersOutsideInfluenceRegion(I, InfluenceRegion);
    DomTreeNode *IDomNode = DT.getNode(InfluencedBB)->getIDom();
    if (IDomNode == nullptr)
      break;
    InfluencedBB = IDomNode->getBlock();
  }
}

void DivergencePropagator::findUsersOutsideInfluenceRegion(
    Instruction &I, const DenseSet<BasicBlock *> &InfluenceRegion) {
  for (User *U : I.users()) {
    Instruction *UserInst = cast<Instruction>(U);
    if (!InfluenceRegion.count(UserInst->getParent())) {
      if (DV.insert(UserInst).second)
        Worklist.push_back(UserInst);
    }
  }
}

// A helper function for computeInfluenceRegion that adds successors of "ThisBB"
// to the influence region.
static void
addSuccessorsToInfluenceRegion(BasicBlock *ThisBB, BasicBlock *End,
                               DenseSet<BasicBlock *> &InfluenceRegion,
                               std::vector<BasicBlock *> &InfluenceStack) {
  for (BasicBlock *Succ : successors(ThisBB)) {
    if (Succ != End && InfluenceRegion.insert(Succ).second)
      InfluenceStack.push_back(Succ);
  }
}

void DivergencePropagator::computeInfluenceRegion(
    BasicBlock *Start, BasicBlock *End,
    DenseSet<BasicBlock *> &InfluenceRegion) {
  assert(PDT.properlyDominates(End, Start) &&
         "End does not properly dominate Start");

  // The influence region starts from the end of "Start" to the beginning of
  // "End". Therefore, "Start" should not be in the region unless "Start" is in
  // a loop that doesn't contain "End".
  std::vector<BasicBlock *> InfluenceStack;
  addSuccessorsToInfluenceRegion(Start, End, InfluenceRegion, InfluenceStack);
  while (!InfluenceStack.empty()) {
    BasicBlock *BB = InfluenceStack.back();
    InfluenceStack.pop_back();
    addSuccessorsToInfluenceRegion(BB, End, InfluenceRegion, InfluenceStack);
  }
}

void DivergencePropagator::exploreDataDependency(Value *V) {
  // Follow def-use chains of V.
  for (User *U : V->users()) {
    Instruction *UserInst = cast<Instruction>(U);
    if (DV.insert(UserInst).second)
      Worklist.push_back(UserInst);
  }
}

void DivergencePropagator::propagate() {
  // Traverse the dependency graph using DFS.
  while (!Worklist.empty()) {
    Value *V = Worklist.back();
    Worklist.pop_back();
    if (TerminatorInst *TI = dyn_cast<TerminatorInst>(V)) {
      // Terminators with less than two successors won't introduce sync
      // dependency. Ignore them.
      if (TI->getNumSuccessors() > 1)
        exploreSyncDependency(TI);
    }
    exploreDataDependency(V);
  }
}

} /// end namespace anonymous

// Register this pass.
char DxilDivergenceAnalysis::ID = 0;
INITIALIZE_PASS_BEGIN(DxilDivergenceAnalysis, "dxil-divergence", "Divergence Analysis", // HLSL Change
//INITIALIZE_PASS_BEGIN(DivergenceAnalysis, "divergence", "Divergence Analysis", // HLSL Change
                      false, true)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(PostDominatorTree)
INITIALIZE_PASS_END(DxilDivergenceAnalysis, "dxil-divergence", "Divergence Analysis", // HLSL Change
//INITIALIZE_PASS_END(DivergenceAnalysis, "divergence", "Divergence Analysis", // HLSL Change
                    false, true)

//FunctionPass *llvm::createDivergenceAnalysisPass() { // HLSL Change
FunctionPass *llvm::createDxilDivergenceAnalysisPass() { // HLSL Change
  return new DxilDivergenceAnalysis();
}

void DxilDivergenceAnalysis::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<DominatorTreeWrapperPass>();
  AU.addRequired<PostDominatorTree>();
  AU.setPreservesAll();
}

bool DxilDivergenceAnalysis::runOnFunction(Function &F) {
#if 0 // HLSL Change
  auto *TTIWP = getAnalysisIfAvailable<TargetTransformInfoWrapperPass>();
  if (TTIWP == nullptr)
    return false;

  TargetTransformInfo &TTI = TTIWP->getTTI(F);
#endif // HLSL Change
  auto TTI = TargetTransformInfo(F.getParent(), false); // HLSL Change
  // Fast path: if the target does not have branch divergence, we do not mark
  // any branch as divergent.
  if (!TTI.hasBranchDivergence())
    return false;

  DivergentValues.clear();
  DivergencePropagator DP(F, TTI,
                          getAnalysis<DominatorTreeWrapperPass>().getDomTree(),
                          getAnalysis<PostDominatorTree>(), DivergentValues);
  DP.populateWithSourcesOfDivergence();
  DP.propagate();
  return false;
}

void DxilDivergenceAnalysis::print(raw_ostream &OS, const Module *) const {
  if (DivergentValues.empty())
    return;
  const Value *FirstDivergentValue = *DivergentValues.begin();
  const Function *F;
  if (const Argument *Arg = dyn_cast<Argument>(FirstDivergentValue)) {
    F = Arg->getParent();
  } else if (const Instruction *I =
                 dyn_cast<Instruction>(FirstDivergentValue)) {
    F = I->getParent()->getParent();
  } else {
    llvm_unreachable("Only arguments and instructions can be divergent");
  }

  // Dumps all divergent values in F, arguments and then instructions.
  for (auto &Arg : F->args()) {
    if (DivergentValues.count(&Arg))
      OS << "DIVERGENT:  " << Arg << "\n";
  }
  // Iterate instructions using inst_range to ensure a deterministic order.
  for (auto &I : inst_range(F)) {
    if (DivergentValues.count(&I))
      OS << "DIVERGENT:" << I << "\n";
  }
}