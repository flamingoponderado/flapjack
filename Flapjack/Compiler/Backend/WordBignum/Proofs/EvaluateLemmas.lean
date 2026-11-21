module

public import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd
public import Flapjack.Compiler.Backend.WordBignum.Proofs.StateRel
public import Flapjack.Compiler.Backend.WordBignum.Helpers
public import Flapjack.Compiler.Backend.WordBignum.Proofs.WordSemClauses
public import Flapjack.HolArb

@[expose] public section

/-! The wordSem evaluation lemmas of
`cakeml/compiler/backend/proofs/word_bignumProofScript.sml` (the
`evaluate_*` theorem group). They are stated over the exact `wordSem`
evaluator, so the finite-map state carrier is named by the qualifier on each
tagged declaration. -/

namespace Flapjack.Compiler.Backend.WordBignum

open Flapjack

namespace WordSemEvaluateLemmasSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged lemmas of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemEvaluateLemmasSupport

/-- HOL `evaluate_Seq_Seq` (`word_bignumProofScript.sml:345`): sequencing is
associative on the wordSem evaluator. HOL's proof inducts over `p1` after
rebinding `evaluate_def`; Lean does not need the induction because the rebound
`Seq` clause is pure plumbing on the `evaluate p1` result, so it expands both
sides and splits on that result and on `evaluate p2`. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "evaluate_Seq_Seq"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_seqSeq {width : Nat} [NeZero width] {C F : Type}
    (p1 p2 p3 : WordLangProgHOL (BitVec width)) (t1 : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (.seq p1 (.seq p2 p3)) t1 =
      WordSemStateFiniteExact.evaluate (.seq (.seq p1 p2) p3) t1 := by
  have hseq := (WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C)
    (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hseq, hseq, hseq]
  cases h1 : WordSemStateFiniteExact.evaluate p1 t1 with
  | mk res s1 =>
    cases res with
    | none =>
      cases h2 : WordSemStateFiniteExact.evaluate p2 s1 with
      | mk res2 s2 =>
        cases res2 <;> simp_all
    | some r =>
      simp

/-- HOL `evaluate_SeqTemp` (`word_bignumProofScript.sml:454`): when the
`SeqTemp` source register is a live temporary register, the sequence evaluates
as the body with that register copied into the destination; otherwise the
statement is the trivial rewrite-to-itself that HOL writes. HOL's guard
`Temp (n2w r) IN FDOM t.store` keeps its domain form (`∈ … .dom`), and
`t.store ' Temp (n2w r)` is the reviewed `holFapply`. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "evaluate_SeqTemp"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_seqTemp {width : Nat} [NeZero width] {C F : Type}
    (i r : Nat) (p : WordLangProgHOL (BitVec width)) (t : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (seqTemp i r p) t =
      if (.temp (BitVec.ofNat 5 r)) ∈ t.store.dom then
        WordSemStateFiniteExact.evaluate p
          (WordSemStateFiniteExact.setVar i
            (holFapply t.store (.temp (BitVec.ofNat 5 r))) t)
      else WordSemStateFiniteExact.evaluate (seqTemp i r p) t := by
  unfold seqTemp
  have hseq := (WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C)
    (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hasg := (WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C)
    (F := F)).2.2.2.2.2.1
  rw [hseq, hasg]
  simp only [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore]
  cases hl : t.store.lookup (.temp (BitVec.ofNat 5 r)) with
  | none => simp [HolFiniteMapExact.dom, hl]
  | some v => simp [HolFiniteMapExact.dom, hl, holFapply_of_lookup hl]

open Flapjack.WordSemStateFiniteExact.BignumClauses

open Classical in
/-- HOL `evaluate_SeqTempImm` (`word_bignumProofScript.sml:463`): with a register
operand that is a live temporary, or an immediate, `SeqTempImm` evaluates as
the body with the operand value copied into the destination; otherwise the
statement is the trivial rewrite-to-itself that HOL writes. HOL's
`case ri of Reg r => ... | Imm w => ...` is a match in the same constructor
order; HOL's Boolean guard is decided classically. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "evaluate_SeqTempImm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_seqTempImm {width : Nat} [NeZero width] {C F : Type}
    (i : Nat) (ri : WordRegImm (BitVec width)) (p : WordLangProgHOL (BitVec width))
    (t : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (seqTempImm i ri p) t =
      if ∀ r, ri = .reg r → (.temp (BitVec.ofNat 5 r)) ∈ t.store.dom then
        WordSemStateFiniteExact.evaluate p
          (WordSemStateFiniteExact.setVar i
            (match ri with
             | .reg r => holFapply t.store (.temp (BitVec.ofNat 5 r))
             | .imm w => .word w) t)
      else WordSemStateFiniteExact.evaluate (seqTempImm i ri p) t := by
  cases ri with
  | reg r =>
    simp only [seqTempImm]
    rw [evaluate_seqTemp]
    by_cases h : (.temp (BitVec.ofNat 5 r)) ∈ t.store.dom
    · simp [h]
    · simp [h]
  | imm w =>
    simp only [seqTempImm]
    rw [evaluate_seq, evaluate_assign]
    simp [WordSemStateFiniteExact.wordExp]

open Classical in
/-- HOL `evaluate_SeqTempImmNot` (`word_bignumProofScript.sml:476`): the
complemented variant. A register operand must be a live temporary holding a
word; the complemented word is copied into the destination. HOL's inner
`case ... of Word w => Word (~w) | Loc v1 v2 => ARB` keeps its `Loc` arm as the
reviewed `holArb` rendering of `ARB` at `word_loc`, whose inhabitant is the
module-level `wordLocWNonempty` instance. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "evaluate_SeqTempImmNot"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_seqTempImmNot {width : Nat} [NeZero width] {C F : Type}
    (i : Nat) (ri : WordRegImm (BitVec width)) (p : WordLangProgHOL (BitVec width))
    (t : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (seqTempImmNot i ri p) t =
      if ∀ r, ri = .reg r → (.temp (BitVec.ofNat 5 r)) ∈ t.store.dom ∧
          ∃ w, holFapply t.store (.temp (BitVec.ofNat 5 r)) = .word w then
        WordSemStateFiniteExact.evaluate p
          (WordSemStateFiniteExact.setVar i
            (match ri with
             | .reg r =>
               match holFapply t.store (.temp (BitVec.ofNat 5 r)) with
               | .word w => .word (~~~w)
               | .loc _ _ => holArb (WordLocW width)
             | .imm w => .word (~~~w)) t)
      else WordSemStateFiniteExact.evaluate (seqTempImmNot i ri p) t := by
  cases ri with
  | reg r =>
    by_cases h : (.temp (BitVec.ofNat 5 r)) ∈ t.store.dom ∧
          ∃ w, holFapply t.store (.temp (BitVec.ofNat 5 r)) = .word w
    · rw [if_pos (by intro r' hr; cases hr; exact h)]
      obtain ⟨hdom, w, hw⟩ := h
      simp only [seqTempImmNot, seqTemp]
      rw [evaluate_seq, evaluate_assign]
      cases hl : t.store.lookup (.temp (BitVec.ofNat 5 r)) with
      | none => exact absurd hl hdom
      | some v =>
        rw [holFapply_of_lookup hl] at hw
        subst hw
        simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore, hl]
        rw [evaluate_seq, evaluate_assign]
        simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, holFapply_of_lookup hl, theWords, wordOpHOL, wordOp,
          sptLookup_sptInsert_same, sptInsert_insert_shadow]
    · rw [if_neg (by intro hall; exact h (hall r rfl))]
  | imm w =>
    simp only [seqTempImmNot]
    rw [evaluate_seq, evaluate_assign]
    simp [WordSemStateFiniteExact.wordExp]

end Flapjack.Compiler.Backend.WordBignum
