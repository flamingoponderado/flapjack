import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMap
import Flapjack.Pancake.WordConvs

/-! Primitive original cases of ssa_cc_trans_pre_alloc_conventions.
The complete recursive assembly remains open. -/
namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc

/-- Original Skip case with the original allocation-class/map hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocSkip {width : Nat} [NeZero width]
    
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : isAllocVar next ∧ ssaMapOK next ssa) :
    let (output, _, _) : WordLangProgHOL (BitVec width) × Spt Nat × Nat :=
      ssaCcTrans (.skip) ssa next tables
    preAllocConventionsHOL output = true := by
  simp [ssaCcTrans, preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]

/-- Original Move case with the original allocation-class/map hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocMove {width : Nat} [NeZero width]
    (priority : Nat) (moves : List (Nat × Nat))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : isAllocVar next ∧ ssaMapOK next ssa) :
    let (output, _, _) : WordLangProgHOL (BitVec width) × Spt Nat × Nat :=
      ssaCcTrans (.move priority moves) ssa next tables
    preAllocConventionsHOL output = true := by
  generalize hr : listNextVarRename (moves.map Prod.fst) ssa next = renamed
  rcases renamed with ⟨names, map, counter⟩
  simp [ssaCcTrans, hr, preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]

/-- Original StoreConsts case with the original allocation-class/map hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocStoreConsts {width : Nat} [NeZero width]
    (a b c d : Nat) (ws : List (Bool × BitVec width))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : isAllocVar next ∧ ssaMapOK next ssa) :
    let (output, _, _) : WordLangProgHOL (BitVec width) × Spt Nat × Nat :=
      ssaCcTrans (.storeConsts a b c d ws) ssa next tables
    preAllocConventionsHOL output = true := by
  simp [ssaCcTrans, preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]

/-- Original Assign case with the original allocation-class/map hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocAssign {width : Nat} [NeZero width]
    (name : Nat) (exp : WordLangExpHOL (BitVec width))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : isAllocVar next ∧ ssaMapOK next ssa) :
    let (output, _, _) : WordLangProgHOL (BitVec width) × Spt Nat × Nat :=
      ssaCcTrans (.assign name exp) ssa next tables
    preAllocConventionsHOL output = true := by
  simp [ssaCcTrans, nextVarRename, preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]

/-- Original Get case with the original allocation-class/map hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocGet {width : Nat} [NeZero width]
    (name : Nat) (store : WordStoreHOL)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : isAllocVar next ∧ ssaMapOK next ssa) :
    let (output, _, _) : WordLangProgHOL (BitVec width) × Spt Nat × Nat :=
      ssaCcTrans (.get name store) ssa next tables
    preAllocConventionsHOL output = true := by
  simp [ssaCcTrans, nextVarRename, preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]

/-- Original Store case with the original allocation-class/map hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocStore {width : Nat} [NeZero width]
    (exp : WordLangExpHOL (BitVec width)) (name : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : isAllocVar next ∧ ssaMapOK next ssa) :
    let (output, _, _) : WordLangProgHOL (BitVec width) × Spt Nat × Nat :=
      ssaCcTrans (.store exp name) ssa next tables
    preAllocConventionsHOL output = true := by
  simp [ssaCcTrans, preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]

/-- Original Raise case with the original allocation-class/map hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocRaise {width : Nat} [NeZero width]
    (name : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : isAllocVar next ∧ ssaMapOK next ssa) :
    let (output, _, _) : WordLangProgHOL (BitVec width) × Spt Nat × Nat :=
      ssaCcTrans (.raise name) ssa next tables
    preAllocConventionsHOL output = true := by
  simp [ssaCcTrans, preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]

/-- Original OpCurrHeap case with the original allocation-class/map hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocOpCurrHeap {width : Nat} [NeZero width]
    (op : BinOp) (dst src : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : isAllocVar next ∧ ssaMapOK next ssa) :
    let (output, _, _) : WordLangProgHOL (BitVec width) × Spt Nat × Nat :=
      ssaCcTrans (.opCurrHeap op dst src) ssa next tables
    preAllocConventionsHOL output = true := by
  simp [ssaCcTrans, nextVarRename, preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]

/-- Original Return case with the original allocation-class/map hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocReturn {width : Nat} [NeZero width]
    (label : Nat) (values : List Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : isAllocVar next ∧ ssaMapOK next ssa) :
    let (output, _, _) : WordLangProgHOL (BitVec width) × Spt Nat × Nat :=
      ssaCcTrans (.return label values) ssa next tables
    preAllocConventionsHOL output = true := by
  simp [ssaCcTrans, preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]

/-- Original Tick case with the original allocation-class/map hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocTick {width : Nat} [NeZero width]
    
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : isAllocVar next ∧ ssaMapOK next ssa) :
    let (output, _, _) : WordLangProgHOL (BitVec width) × Spt Nat × Nat :=
      ssaCcTrans (.tick) ssa next tables
    preAllocConventionsHOL output = true := by
  simp [ssaCcTrans, preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]

/-- Original Set case with the original allocation-class/map hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocSet {width : Nat} [NeZero width]
    (store : WordStoreHOL) (exp : WordLangExpHOL (BitVec width))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : isAllocVar next ∧ ssaMapOK next ssa) :
    let (output, _, _) : WordLangProgHOL (BitVec width) × Spt Nat × Nat :=
      ssaCcTrans (.set store exp) ssa next tables
    preAllocConventionsHOL output = true := by
  simp [ssaCcTrans, preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]

/-- Original LocValue case with the original allocation-class/map hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocLocValue {width : Nat} [NeZero width]
    (dst src : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : isAllocVar next ∧ ssaMapOK next ssa) :
    let (output, _, _) : WordLangProgHOL (BitVec width) × Spt Nat × Nat :=
      ssaCcTrans (.locValue dst src) ssa next tables
    preAllocConventionsHOL output = true := by
  simp [ssaCcTrans, nextVarRename, preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]

/-- Original CodeBufferWrite case with the original allocation-class/map hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocCodeBufferWrite {width : Nat} [NeZero width]
    (addr value : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : isAllocVar next ∧ ssaMapOK next ssa) :
    let (output, _, _) : WordLangProgHOL (BitVec width) × Spt Nat × Nat :=
      ssaCcTrans (.codeBufferWrite addr value) ssa next tables
    preAllocConventionsHOL output = true := by
  simp [ssaCcTrans, preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]

/-- Original DataBufferWrite case with the original allocation-class/map hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocDataBufferWrite {width : Nat} [NeZero width]
    (addr value : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : isAllocVar next ∧ ssaMapOK next ssa) :
    let (output, _, _) : WordLangProgHOL (BitVec width) × Spt Nat × Nat :=
      ssaCcTrans (.dataBufferWrite addr value) ssa next tables
    preAllocConventionsHOL output = true := by
  simp [ssaCcTrans, preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]

/-- Original ShareInst case with the original allocation-class/map hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocShareInst {width : Nat} [NeZero width]
    (op : WordMemOp) (name : Nat) (exp : WordLangExpHOL (BitVec width))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (_h : isAllocVar next ∧ ssaMapOK next ssa) :
    let (output, _, _) : WordLangProgHOL (BitVec width) × Spt Nat × Nat :=
      ssaCcTrans (.shareInst op name exp) ssa next tables
    preAllocConventionsHOL output = true := by
  cases op <;> simp [ssaCcTrans, nextVarRename, preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL]

end Flapjack.WordAlloc
