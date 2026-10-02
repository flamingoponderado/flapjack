import Flapjack.Compiler.Backend.WordCse.Proofs.LoadEvaluation

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack Compiler.Encoders.Asm WordSemStateFiniteExact AssignmentResults LoadEvaluationSupport

/-! Full original arithmetic and state-agreement frames. The untagged helpers
have no separate HOL declarations: they factor the actual native `inst` clauses
and prove the input-field independence used in HOL's case-by-case proofs.
Public statements keep the complete faithful evaluator and original guards. -/

private def arithValue {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a : HolArith width) (s : WordSemStateFiniteExact width C F) : Option (WordLocW width) :=
  match a with
  | .binop op _ src ri =>
    wordExp s (.op op [.var src, match ri with | .reg r => .var r | .imm w => .const w])
  | .shift sh _ src ri =>
    wordExp s (.shift sh (.var src) (match ri with | .reg r => .var r | .imm w => .const w))
  | .div _ src1 src2 =>
    match WordSemStateFiniteExact.getVars [src2, src1] s with
    | some [.word q, .word v] => if q ≠ 0 then some (.word (v.sdiv q)) else none
    | _ => none
  | _ => none

private theorem instArithMap {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a : HolArith width) (s : WordSemStateFiniteExact width C F) (h : canMemArith a = true) :
    inst (.arith (HolArith.toWordLangArith a)) s =
      (arithValue a s).map (fun v => setVar (firstRegOfArith a) v s) := by
  cases a with
  | binop op dst src ri =>
    cases ri <;> simp [HolArith.toWordLangArith, HolRegImm.toWordRegImm, inst, arithValue,
      firstRegOfArith, assignMap]
  | shift sh dst src ri =>
    cases ri <;> simp [HolArith.toWordLangArith, HolRegImm.toWordRegImm, inst, arithValue,
      firstRegOfArith, assignMap]
  | div dst src1 src2 =>
    simp only [HolArith.toWordLangArith, inst, arithValue, firstRegOfArith]
    split <;> simp_all [Option.map]
    split <;> simp_all
  | _ => simp [canMemArith] at h

private theorem arithValueLocalsAgree {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a : HolArith width) (s1 s2 : WordSemStateFiniteExact width C F)
    (h : s2.locals = s1.locals) : arithValue a s2 = arithValue a s1 := by
  cases a with
  | binop op dst src ri =>
    cases ri <;> simp [arithValue, wordExp, getVar, h]
  | shift sh dst src ri =>
    cases ri <;> simp [arithValue, wordExp, getVar, h]
  | div dst src1 src2 => simp [arithValue, WordSemStateFiniteExact.getVars, getVar, h]
  | _ => rfl

private theorem arithValueSetVar {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a : HolArith width) (r : Nat) (u : WordLocW width) (s : WordSemStateFiniteExact width C F)
    (h : r ∉ arithReads a) : arithValue a (setVar r u s) = arithValue a s := by
  cases a with
  | binop op dst src ri =>
    cases ri <;> simp_all [arithValue, arithReads, wordExp, getVar, setVar,
      sptLookup_sptInsert_ne, ne_comm]
  | shift sh dst src ri =>
    cases ri <;> simp_all [arithValue, arithReads, wordExp, getVar, setVar,
      sptLookup_sptInsert_ne, ne_comm]
  | div dst src1 src2 =>
    simp_all [arithValue, arithReads, WordSemStateFiniteExact.getVars, getVar, setVar,
      sptLookup_sptInsert_ne, ne_comm]
  | _ => rfl

private theorem loadValueFieldsAgree {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : HolMemop) (a : Nat) (ofs : BitVec width) (s1 s2 : WordSemStateFiniteExact width C F)
    (hl : s2.locals = s1.locals) (hm : s2.memory = s1.memory)
    (hd : s2.mdomain = s1.mdomain) (hb : s2.be = s1.be) :
    loadValue op a ofs s2 = loadValue op a ofs s1 := by
  cases op <;> simp [loadValue, wordExp, getVar, memLoad, hl, hm, hd, hb]

namespace EvaluationFramesWitness

theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end EvaluationFramesWitness

/-- Full original arithmetic write-frame equivalence; no disjoint-destination
guard is added. Native `can_mem_arith` and the actual read list are retained. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_arith_set_var"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem evaluateArithSetVar {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a : HolArith width) (r : Nat) (u w : WordLocW width) (s : WordSemStateFiniteExact width C F)
    (h : canMemArith a = true ∧ r ∉ arithReads a) :
    (evaluate (.inst (.arith (HolArith.toWordLangArith a))) (setVar r u s) =
      (none, setVar (firstRegOfArith a) w (setVar r u s))) ↔
    evaluate (.inst (.arith (HolArith.toWordLangArith a))) s =
      (none, setVar (firstRegOfArith a) w s) := by
  rw [evaluationAssignmentIff _ _ (arithValue a (setVar r u s)) (setVar r u s) w
    (instArithMap a (setVar r u s) h.1)]
  rw [evaluationAssignmentIff _ _ (arithValue a s) s w (instArithMap a s h.1)]
  rw [arithValueSetVar a r u s h.2]

/-- Full original replacement of arbitrary memory. The post-state update is
exactly HOL's update after `set_var`, not an assumed memory relation. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_arith_memory"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem evaluateArithMemory {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a : HolArith width) (w : WordLocW width) (s : WordSemStateFiniteExact width C F)
    (m : BitVec width → WordLocW width) (h : canMemArith a = true) :
    (evaluate (.inst (.arith (HolArith.toWordLangArith a))) {s with memory := m} =
      (none, {setVar (firstRegOfArith a) w s with memory := m})) ↔
    evaluate (.inst (.arith (HolArith.toWordLangArith a))) s =
      (none, setVar (firstRegOfArith a) w s) := by
  change (evaluate (.inst (.arith (HolArith.toWordLangArith a))) {s with memory := m} =
    (none, setVar (firstRegOfArith a) w {s with memory := m})) ↔ _
  rw [evaluationAssignmentIff _ _ (arithValue a {s with memory := m}) {s with memory := m} w
    (instArithMap a {s with memory := m} h)]
  rw [evaluationAssignmentIff _ _ (arithValue a s) s w (instArithMap a s h)]
  rw [arithValueLocalsAgree a s {s with memory := m} rfl]

/-- Full original arithmetic state agreement, requiring only input locals
equality and original eligibility/source evaluation. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_arith_agree"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem evaluateArithAgree {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a : HolArith width) (w : WordLocW width) (s1 s2 : WordSemStateFiniteExact width C F)
    (h : evaluate (.inst (.arith (HolArith.toWordLangArith a))) s1 =
        (none, setVar (firstRegOfArith a) w s1) ∧
      canMemArith a = true ∧ s2.locals = s1.locals) :
    evaluate (.inst (.arith (HolArith.toWordLangArith a))) s2 =
      (none, setVar (firstRegOfArith a) w s2) := by
  have hv := (evaluationAssignmentIff _ _ (arithValue a s1) s1 w (instArithMap a s1 h.2.1)).mp h.1
  apply (evaluationAssignmentIff _ _ (arithValue a s2) s2 w (instArithMap a s2 h.2.1)).mpr
  rw [arithValueLocalsAgree a s1 s2 h.2.2]
  exact hv

/-- Full original load agreement on locals, memory, domain and endianness.
All four frame theorems retain the inherited evaluator rational-cut assumption
(SOUNDNESS item 8) and add no evaluation or global invariant hypothesis. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_load_agree"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem evaluateLoadAgree {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : HolMemop) (r a : Nat) (ofs : BitVec width) (w : WordLocW width)
    (s1 s2 : WordSemStateFiniteExact width C F)
    (h : evaluate (.inst (.mem op r (.addr a ofs))) s1 = (none, setVar r w s1) ∧
      isStore op = false ∧ s2.locals = s1.locals ∧ s2.memory = s1.memory ∧
      s2.mdomain = s1.mdomain ∧ s2.be = s1.be) :
    evaluate (.inst (.mem op r (.addr a ofs))) s2 = (none, setVar r w s2) := by
  have hv := (evaluationAssignmentIff _ r (loadValue op a ofs s1) s1 w
    (instLoadMap op r a ofs s1 h.2.1)).mp h.1
  apply (evaluationAssignmentIff _ r (loadValue op a ofs s2) s2 w
    (instLoadMap op r a ofs s2 h.2.1)).mpr
  rw [loadValueFieldsAgree op a ofs s1 s2 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2]
  exact hv

end Flapjack.Compiler.Backend.WordCse
