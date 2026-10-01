import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameShiftedProperties
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapPreservation

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Full HOL Alloc case of the native SSA program allocation/map invariant.
Retains the actual compiler-output equality and original map/allocation premises;
all counter/class/map conclusions are derived through the actual rename/cut flow.
No extra distinctness, tree validity, evaluation or output-map premise is assumed.
The original loop-table parameter is retained even though this case ignores it. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsAlloc {width : Nat} [NeZero width]
    (destination : Nat) (cutsets : WordLangCutsetsHOL) (ssa : Spt Nat) (next : Nat)
    (loopTables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.alloc destination cutsets) ssa next loopTables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  let allNames := sptUnion cutsets.1 cutsets.2
  let names := (sptToAList allNames).map Prod.fst
  generalize stackRename : listNextVarRenameMove (width := width) ssa (next + 2) names = stacked
  rcases stacked with ⟨stackMove, stackTree, stackCounter⟩
  have stackFrame := listNextVarRenameMoveProps2 names ssa next stackMove stackTree
    stackCounter stackRename ⟨Or.inl h.2, h.1⟩
  have stackClass := stackFrame.2.1 h.2
  have cutFrame := ssaMapOKInter stackCounter stackTree allNames stackFrame.2.2.2
  generalize returnRename : listNextVarRenameMove (width := width)
      (sptInter stackTree allNames) (stackCounter + 2) names = returned
  rcases returned with ⟨returnMove, returnTree, returnCounter⟩
  have returnFrame := listNextVarRenameMoveProps2 names (sptInter stackTree allNames)
    stackCounter returnMove returnTree returnCounter returnRename ⟨Or.inr stackClass, cutFrame⟩
  dsimp only [names, allNames] at stackRename returnRename
  simp only [ssaCcTrans, stackRename, returnRename, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨by have := stackFrame.1; have := returnFrame.1; omega,
    returnFrame.2.2.1 stackClass, returnFrame.2.2.2⟩

/-- Full HOL FFI case of the native SSA program allocation/map invariant.
Retains the actual compiler-output equality and original map/allocation premises;
all counter/class/map conclusions are derived through the actual rename/cut flow.
No extra distinctness, tree validity, evaluation or output-map premise is assumed.
The original loop-table parameter is retained even though this case ignores it. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsFFI {width : Nat} [NeZero width]
    (function : Flapjack.Basis.Pure.MlString.MlString)
    (configuration configurationLength array arrayLength : Nat) (cutsets : WordLangCutsetsHOL) (ssa : Spt Nat) (next : Nat)
    (loopTables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.ffi function configuration configurationLength array arrayLength cutsets) ssa next loopTables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  let allNames := sptUnion cutsets.1 cutsets.2
  let names := (sptToAList allNames).map Prod.fst
  generalize stackRename : listNextVarRenameMove (width := width) ssa (next + 2) names = stacked
  rcases stacked with ⟨stackMove, stackTree, stackCounter⟩
  have stackFrame := listNextVarRenameMoveProps2 names ssa next stackMove stackTree
    stackCounter stackRename ⟨Or.inl h.2, h.1⟩
  have stackClass := stackFrame.2.1 h.2
  have cutFrame := ssaMapOKInter stackCounter stackTree allNames stackFrame.2.2.2
  generalize returnRename : listNextVarRenameMove (width := width)
      (sptInter stackTree allNames) (stackCounter + 2) names = returned
  rcases returned with ⟨returnMove, returnTree, returnCounter⟩
  have returnFrame := listNextVarRenameMoveProps2 names (sptInter stackTree allNames)
    stackCounter returnMove returnTree returnCounter returnRename ⟨Or.inr stackClass, cutFrame⟩
  dsimp only [names, allNames] at stackRename returnRename
  simp only [ssaCcTrans, stackRename, returnRename, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨by have := stackFrame.1; have := returnFrame.1; omega,
    returnFrame.2.2.1 stackClass, returnFrame.2.2.2⟩

/-- Full HOL Install case of the native SSA program allocation/map invariant.
Retains the actual compiler-output equality and original map/allocation premises;
all counter/class/map conclusions are derived through the actual rename/cut flow.
No extra distinctness, tree validity, evaluation or output-map premise is assumed.
The original loop-table parameter is retained even though this case ignores it. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsInstall {width : Nat} [NeZero width]
    (codeBuffer codeLength dataBuffer dataLength : Nat) (cutsets : WordLangCutsetsHOL)
    (ssa : Spt Nat) (next : Nat) (loopTables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.install codeBuffer codeLength dataBuffer dataLength cutsets)
      ssa next loopTables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  let allNames := sptUnion cutsets.1 cutsets.2
  let names := (sptToAList allNames).map Prod.fst
  generalize stackRename : listNextVarRenameMove (width := width) ssa (next + 2) names = stacked
  rcases stacked with ⟨stackMove, stackTree, stackCounter⟩
  have stackFrame := listNextVarRenameMoveProps2 names ssa next stackMove stackTree
    stackCounter stackRename ⟨Or.inl h.2, h.1⟩
  have stackClass := stackFrame.2.1 h.2
  have cutFrame := ssaMapOKInter stackCounter stackTree allNames stackFrame.2.2.2
  have cutShifted := ssaMapOKLem stackCounter (sptInter stackTree allNames) cutFrame
  have allocated := isStackVarFlip stackCounter stackClass
  generalize freshRename : nextVarRename codeBuffer (sptInter stackTree allNames)
      (stackCounter + 2) = fresh
  rcases fresh with ⟨freshRegister, freshTree, freshCounter⟩
  have freshFrame := nextVarRenameProps codeBuffer (sptInter stackTree allNames)
    (stackCounter + 2) freshRegister freshTree freshCounter freshRename
      ⟨Or.inl allocated, cutShifted⟩
  have freshClass := freshFrame.2.1 allocated
  generalize returnRename : listNextVarRenameMove (width := width)
      freshTree freshCounter names = returned
  rcases returned with ⟨returnMove, returnTree, returnCounter⟩
  have returnFrame := listNextVarRenameMoveProps names freshTree freshCounter
    returnMove returnTree returnCounter returnRename ⟨Or.inl freshClass, freshFrame.2.2.2⟩
  dsimp only [names, allNames] at stackRename freshRename returnRename
  simp only [ssaCcTrans, stackRename, freshRename, returnRename, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨by have := stackFrame.1; have := freshFrame.1; have := returnFrame.1; omega,
    returnFrame.2.1 freshClass, returnFrame.2.2.2⟩

end Flapjack.Compiler.Backend.WordAlloc
