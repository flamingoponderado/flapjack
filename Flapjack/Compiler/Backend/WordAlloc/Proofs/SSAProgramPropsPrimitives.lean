import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenamePropertyWrappers
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAInstructionProps

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Full original Skip primitive case: original native compiler equality,
map/allocation premise and all three output invariants; no additional premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsSkip {width : Nat} [NeZero width]
    
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans .skip ssa next tables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  simp only [ssaCcTrans, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨Nat.le_refl _, h.2, h.1⟩

/-- Full original StoreConsts primitive case: original native compiler equality,
map/allocation premise and all three output invariants; no additional premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsStoreConsts {width : Nat} [NeZero width]
    (a b c d : Nat) (ws : List (Bool × BitVec width))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.storeConsts a b c d ws) ssa next tables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  generalize firstEq : nextVarRename d ssa next = first
  rcases first with ⟨freshD, firstTree, firstCounter⟩
  have firstFrame := nextVarRenameProps d ssa next freshD firstTree firstCounter
    firstEq ⟨Or.inl h.2, h.1⟩
  generalize secondEq : nextVarRename c firstTree firstCounter = second
  rcases second with ⟨freshC, secondTree, secondCounter⟩
  have secondFrame := nextVarRenameProps c firstTree firstCounter freshC secondTree secondCounter
    secondEq ⟨Or.inl (firstFrame.2.1 h.2), firstFrame.2.2.2⟩
  simp only [ssaCcTrans, firstEq, secondEq, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨Nat.le_trans firstFrame.1 secondFrame.1,
    secondFrame.2.1 (firstFrame.2.1 h.2), secondFrame.2.2.2⟩

/-- Full original Inst primitive case: original native compiler equality,
map/allocation premise and all three output invariants; no additional premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsInst {width : Nat} [NeZero width]
    (instruction : WordLangInst (BitVec width))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.inst instruction) ssa next tables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  simpa only [ssaCcTrans] using ssaCcTransInstProps instruction ssa next output ssaOut nextOut produced h

/-- Full original Assign primitive case: original native compiler equality,
map/allocation premise and all three output invariants; no additional premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsAssign {width : Nat} [NeZero width]
    (name : Nat) (exp : WordLangExpHOL (BitVec width))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.assign name exp) ssa next tables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  generalize renameEq : nextVarRename name ssa next = renamed
  rcases renamed with ⟨freshName, freshTree, freshCounter⟩
  have frame := nextVarRenameProps name ssa next freshName freshTree freshCounter
    renameEq ⟨Or.inl h.2, h.1⟩
  simp only [ssaCcTrans, renameEq, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨frame.1, frame.2.1 h.2, frame.2.2.2⟩

/-- Full original Get primitive case: original native compiler equality,
map/allocation premise and all three output invariants; no additional premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsGet {width : Nat} [NeZero width]
    (name : Nat) (store : WordStoreHOL)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.get name store) ssa next tables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  generalize renameEq : nextVarRename name ssa next = renamed
  rcases renamed with ⟨freshName, freshTree, freshCounter⟩
  have frame := nextVarRenameProps name ssa next freshName freshTree freshCounter
    renameEq ⟨Or.inl h.2, h.1⟩
  simp only [ssaCcTrans, renameEq, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨frame.1, frame.2.1 h.2, frame.2.2.2⟩

/-- Full original Store primitive case: original native compiler equality,
map/allocation premise and all three output invariants; no additional premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsStore {width : Nat} [NeZero width]
    (exp : WordLangExpHOL (BitVec width)) (name : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.store exp name) ssa next tables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  simp only [ssaCcTrans, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨Nat.le_refl _, h.2, h.1⟩

/-- Full original Raise primitive case: original native compiler equality,
map/allocation premise and all three output invariants; no additional premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsRaise {width : Nat} [NeZero width]
    (name : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.raise name) ssa next tables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  simp only [ssaCcTrans, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨Nat.le_refl _, h.2, h.1⟩

/-- Full original OpCurrHeap primitive case: original native compiler equality,
map/allocation premise and all three output invariants; no additional premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsOpCurrHeap {width : Nat} [NeZero width]
    (operator : BinOp) (destination source : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.opCurrHeap operator destination source) ssa next tables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  generalize renameEq : nextVarRename destination ssa next = renamed
  rcases renamed with ⟨freshName, freshTree, freshCounter⟩
  have frame := nextVarRenameProps destination ssa next freshName freshTree freshCounter
    renameEq ⟨Or.inl h.2, h.1⟩
  simp only [ssaCcTrans, renameEq, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨frame.1, frame.2.1 h.2, frame.2.2.2⟩

/-- Full original Return primitive case: original native compiler equality,
map/allocation premise and all three output invariants; no additional premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsReturn {width : Nat} [NeZero width]
    (label : Nat) (values : List Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.return label values) ssa next tables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  simp only [ssaCcTrans, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨Nat.le_refl _, h.2, h.1⟩

/-- Full original Tick primitive case: original native compiler equality,
map/allocation premise and all three output invariants; no additional premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsTick {width : Nat} [NeZero width]
    
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans .tick ssa next tables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  simp only [ssaCcTrans, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨Nat.le_refl _, h.2, h.1⟩

/-- Full original Set primitive case: original native compiler equality,
map/allocation premise and all three output invariants; no additional premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsSet {width : Nat} [NeZero width]
    (store : WordStoreHOL) (exp : WordLangExpHOL (BitVec width))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.set store exp) ssa next tables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  simp only [ssaCcTrans, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨Nat.le_refl _, h.2, h.1⟩

/-- Full original LocValue primitive case: original native compiler equality,
map/allocation premise and all three output invariants; no additional premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsLocValue {width : Nat} [NeZero width]
    (destination label : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.locValue destination label) ssa next tables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  generalize renameEq : nextVarRename destination ssa next = renamed
  rcases renamed with ⟨freshName, freshTree, freshCounter⟩
  have frame := nextVarRenameProps destination ssa next freshName freshTree freshCounter
    renameEq ⟨Or.inl h.2, h.1⟩
  simp only [ssaCcTrans, renameEq, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨frame.1, frame.2.1 h.2, frame.2.2.2⟩

/-- Full original CodeBufferWrite primitive case: original native compiler equality,
map/allocation premise and all three output invariants; no additional premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsCodeBufferWrite {width : Nat} [NeZero width]
    (address value : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.codeBufferWrite address value) ssa next tables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  simp only [ssaCcTrans, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨Nat.le_refl _, h.2, h.1⟩

/-- Full original DataBufferWrite primitive case: original native compiler equality,
map/allocation premise and all three output invariants; no additional premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsDataBufferWrite {width : Nat} [NeZero width]
    (address value : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.dataBufferWrite address value) ssa next tables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  simp only [ssaCcTrans, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨Nat.le_refl _, h.2, h.1⟩

/-- Full original ShareInst primitive case: original native compiler equality,
map/allocation premise and all three output invariants; no additional premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsShareInst {width : Nat} [NeZero width]
    (operator : WordMemOp) (destination : Nat) (exp : WordLangExpHOL (BitVec width))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.shareInst operator destination exp) ssa next tables = (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  generalize renameEq : nextVarRename destination ssa next = renamed
  rcases renamed with ⟨freshName, freshTree, freshCounter⟩
  have frame := nextVarRenameProps destination ssa next freshName freshTree freshCounter
    renameEq ⟨Or.inl h.2, h.1⟩
  simp only [ssaCcTrans] at produced
  split at produced
  · simp only [Prod.mk.injEq] at produced
    obtain ⟨_, rfl, rfl⟩ := produced
    exact ⟨Nat.le_refl _, h.2, h.1⟩
  · simp only [renameEq, Prod.mk.injEq] at produced
    obtain ⟨_, rfl, rfl⟩ := produced
    exact ⟨frame.1, frame.2.1 h.2, frame.2.2.2⟩

end Flapjack.Compiler.Backend.WordAlloc
