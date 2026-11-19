module

public import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd
public import Flapjack.Compiler.Backend.WordBignum.Proofs.StateRel
public import Flapjack.Compiler.Backend.WordBignum.Helpers

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
`Temp (n2w r) IN FDOM t.store` is rendered as the store lookup being defined,
and `t.store ' Temp (n2w r)` as the reviewed `holFapply`. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "evaluate_SeqTemp"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_seqTemp {width : Nat} [NeZero width] {C F : Type}
    (i r : Nat) (p : WordLangProgHOL (BitVec width)) (t : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (seqTemp i r p) t =
      if t.store.lookup (.temp (BitVec.ofNat 5 r)) ≠ none then
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
  | none => simp
  | some v => simp [holFapply_of_lookup hl]

end Flapjack.Compiler.Backend.WordBignum
