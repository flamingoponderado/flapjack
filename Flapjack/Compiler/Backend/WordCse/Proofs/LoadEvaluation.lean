import Flapjack.Compiler.Backend.WordCse.Proofs.AssignmentResults
import Flapjack.Compiler.Backend.WordCse.RegisterUses

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack Compiler.Encoders.Asm WordSemStateFiniteExact AssignmentResults

/-! Full original load-evaluation transport group. The proof-only value factoring
has no separate HOL declaration: it is proved to agree with the actual native
`inst` clauses below. Public statements use the faithful clocked evaluator. -/

namespace LoadEvaluationSupport

def loadValue {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : HolMemop) (a : Nat) (ofs : BitVec width) (s : WordSemStateFiniteExact width C F) :
    Option (WordLocW width) :=
  match op with
  | .load =>
    match wordExp s (.op .add [.var a, .const ofs]) with
    | some (.word addr) => memLoad addr s
    | _ => none
  | .load8 =>
    match wordExp s (.op .add [.var a, .const ofs]) with
    | some (.word addr) =>
      (memLoadByteAuxExact s.memory s.mdomain s.be addr).map (fun w => .word (w.setWidth width))
    | _ => none
  | .load32 =>
    match wordExp s (.op .add [.var a, .const ofs]) with
    | some (.word addr) =>
      (memLoad32Exact s.memory s.mdomain s.be addr).map (fun w => .word (w.setWidth width))
    | _ => none
  | _ => none

theorem instLoadMap {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : HolMemop) (d a : Nat) (ofs : BitVec width) (s : WordSemStateFiniteExact width C F)
    (h : isStore op = false) :
    inst (.mem op d (.addr a ofs)) s = (loadValue op a ofs s).map (fun v => setVar d v s) := by
  cases op <;> simp [isStore] at h
  all_goals try rfl
  all_goals
    simp only [inst]
    split <;> simp_all [loadValue, Option.map]
  all_goals
    split <;> simp_all

end LoadEvaluationSupport
open LoadEvaluationSupport

private theorem addressSetVar {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a n : Nat) (ofs : BitVec width) (u : WordLocW width)
    (s : WordSemStateFiniteExact width C F) (h : a ≠ n) :
    wordExp (setVar n u s) (.op .add [.var a, .const ofs]) =
      wordExp s (.op .add [.var a, .const ofs]) := by
  simp [wordExp, getVar, setVar, sptLookup_sptInsert_ne, h]

private theorem loadValueSetVar {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : HolMemop) (a n : Nat) (ofs : BitVec width) (u : WordLocW width)
    (s : WordSemStateFiniteExact width C F) (h : a ≠ n) :
    loadValue op a ofs (setVar n u s) = loadValue op a ofs s := by
  cases op <;> simp only [loadValue, addressSetVar a n ofs u s h]
  all_goals rfl

private theorem addressCongr {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a a' : Nat) (ofs : BitVec width) (s : WordSemStateFiniteExact width C F)
    (h : sptLookup a' s.locals = sptLookup a s.locals) :
    wordExp s (.op .add [.var a', .const ofs]) =
      wordExp s (.op .add [.var a, .const ofs]) := by
  simp [wordExp, getVar, h]

private theorem loadValueAddressCongr {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : HolMemop) (a a' : Nat) (ofs : BitVec width) (s : WordSemStateFiniteExact width C F)
    (h : sptLookup a' s.locals = sptLookup a s.locals) :
    loadValue op a' ofs s = loadValue op a ofs s := by
  cases op <;> simp [loadValue, addressCongr a a' ofs s h]

namespace LoadEvaluationWitness

theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end LoadEvaluationWitness

/-- Full original destination transport. Load16 remains quantified; its
successful-evaluation premise is impossible under the faithful semantics. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_load_any_dest"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem evaluateLoadAnyDest {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : HolMemop) (r0 a : Nat) (ofs : BitVec width) (w : WordLocW width)
    (s : WordSemStateFiniteExact width C F) (r : Nat)
    (h : isStore op = false ∧
      evaluate (.inst (.mem op r0 (.addr a ofs))) s = (none, setVar r0 w s)) :
    evaluate (.inst (.mem op r (.addr a ofs))) s = (none, setVar r w s) := by
  have hv := (evaluationAssignmentIff _ r0 (loadValue op a ofs s) s w
    (instLoadMap op r0 a ofs s h.1)).mp h.2
  exact (evaluationAssignmentIff _ r (loadValue op a ofs s) s w
    (instLoadMap op r a ofs s h.1)).mpr hv

/-- Full original write-frame equivalence, including `n = r`. The only
excluded register is the address register, as in HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_load_set_var"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem evaluateLoadSetVar {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : HolMemop) (r a : Nat) (ofs : BitVec width) (n : Nat) (u w : WordLocW width)
    (s : WordSemStateFiniteExact width C F) (h : isStore op = false ∧ a ≠ n) :
    (evaluate (.inst (.mem op r (.addr a ofs))) (setVar n u s) =
      (none, setVar r w (setVar n u s))) ↔
    evaluate (.inst (.mem op r (.addr a ofs))) s = (none, setVar r w s) := by
  rw [evaluationAssignmentIff _ r (loadValue op a ofs (setVar n u s)) (setVar n u s) w
    (instLoadMap op r a ofs (setVar n u s) h.1)]
  rw [evaluationAssignmentIff _ r (loadValue op a ofs s) s w (instLoadMap op r a ofs s h.1)]
  rw [loadValueSetVar op a n ofs u s h.2]

/-- Full original address substitution under equality of actual sparse-map
lookups. No word-valued lookup or successful target evaluation is assumed.
All three load theorems retain the evaluator's existing rational-cut assumption
through `inst` (SOUNDNESS item 8), with no additional assumption. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_load_change_addr"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem evaluateLoadChangeAddr {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : HolMemop) (r a a' : Nat) (ofs : BitVec width) (w : WordLocW width)
    (s : WordSemStateFiniteExact width C F)
    (h : isStore op = false ∧ sptLookup a' s.locals = sptLookup a s.locals ∧
      evaluate (.inst (.mem op r (.addr a ofs))) s = (none, setVar r w s)) :
    evaluate (.inst (.mem op r (.addr a' ofs))) s = (none, setVar r w s) := by
  have hv := (evaluationAssignmentIff _ r (loadValue op a ofs s) s w
    (instLoadMap op r a ofs s h.1)).mp h.2.2
  apply (evaluationAssignmentIff _ r (loadValue op a' ofs s) s w
    (instLoadMap op r a' ofs s h.1)).mpr
  rw [loadValueAddressCongr op a a' ofs s h.2.1]
  exact hv

end Flapjack.Compiler.Backend.WordCse
