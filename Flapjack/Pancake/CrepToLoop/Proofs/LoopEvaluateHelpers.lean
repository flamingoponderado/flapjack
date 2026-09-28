import Flapjack.Pancake.Semantics.LoopProps.NestedSeqExact

/-!
# crep_to_loopProof loop-evaluator helper lemmas

Counterparts of the loopSem-evaluator helper theorems of
`cakeml/pancake/proofs/crep_to_loopProofScript.sml` over the exact
`LoopSemStateFiniteExact.evaluate`/`eval` and `loopNestedSeqHOL`
(the `nested_seq` rendering used by the exact `compile_def`).
-/

namespace Flapjack
namespace LoopSemStateFiniteExact

variable {width : Nat} [NeZero width] {F : Type}

namespace CrepToLoopLoopHelpersFiniteSupport

/-- Local same-module witness for the canonical finite-support
`LoopSemStateFiniteExact` carrier used by the `fmap_as_finite_support := [globals]`
qualified ports in this module (re-exports the checked witness of
`Flapjack/Pancake/Semantics/LoopSemStateExact.lean`). -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

end CrepToLoopLoopHelpersFiniteSupport

/-- Exact HOL `evaluate_nested_seq_append_first` (`crep_to_loopProofScript.sml:17-18`,
    `evaluate_nested_seq_cases |> CONJUNCT1`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "evaluate_nested_seq_append_first"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluate_nested_seq_append_first :
    ∀ (p q : List (HolLoopProg width)) (s st t : LoopSemStateFiniteExact width F),
      evaluate (loopNestedSeqHOL (p ++ q)) s = (none, t) ∧
      evaluate (loopNestedSeqHOL p) s = (none, st) →
      evaluate (loopNestedSeqHOL q) st = (none, t) :=
  evaluate_nested_seq_cases.1

/-- Exact HOL `evaluate_none_nested_seq_append` (`crep_to_loopProofScript.sml:19-20`,
    `evaluate_nested_seq_cases |> CONJUNCT2 |> CONJUNCT1`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "evaluate_none_nested_seq_append"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluate_none_nested_seq_append :
    ∀ (p : List (HolLoopProg width)) (s st : LoopSemStateFiniteExact width F)
      (q : List (HolLoopProg width)),
      evaluate (loopNestedSeqHOL p) s = (none, st) →
      evaluate (loopNestedSeqHOL (p ++ q)) s = evaluate (loopNestedSeqHOL q) st :=
  evaluate_nested_seq_cases.2.1

/-- Exact HOL `evaluate_not_none_nested_seq_append` (`crep_to_loopProofScript.sml:21-22`,
    `evaluate_nested_seq_cases |> CONJUNCT2 |> CONJUNCT2`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "evaluate_not_none_nested_seq_append"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluate_not_none_nested_seq_append :
    ∀ (p : List (HolLoopProg width)) (s : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (st : LoopSemStateFiniteExact width F)
      (q : List (HolLoopProg width)),
      evaluate (loopNestedSeqHOL p) s = (res, st) ∧ res ≠ none →
      evaluate (loopNestedSeqHOL (p ++ q)) s = evaluate (loopNestedSeqHOL p) s :=
  evaluate_nested_seq_cases.2.2

/-- Exact HOL `evaluate_comb_seq` (`crep_to_loopProofScript.sml:333-336`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "evaluate_comb_seq"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluate_comb_seq :
    ∀ (p : HolLoopProg width) (s t : LoopSemStateFiniteExact width F) (q : HolLoopProg width)
      (r : LoopSemStateFiniteExact width F),
      evaluate p s = (none, t) ∧ evaluate q t = (none, r) → evaluate (.seq p q) s = (none, r) := by
  intro p s t q r ⟨h1, h2⟩
  rw [evaluate_seq, h1]; exact h2

/-- Exact HOL `evaluate_none_nested_seq_append_eq` (`crep_to_loopProofScript.sml:3256-3259`,
    `[local]`); its free variables `p q s s1 res_s` are universally quantified. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "evaluate_none_nested_seq_append_eq"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluate_none_nested_seq_append_eq (p q : List (HolLoopProg width))
    (s s1 : LoopSemStateFiniteExact width F)
    (res_s : Option (LoopResultExact width) × LoopSemStateFiniteExact width F) :
    evaluate (loopNestedSeqHOL p) s = (none, s1) ∧ evaluate (loopNestedSeqHOL q) s1 = res_s →
      evaluate (loopNestedSeqHOL (p ++ q)) s = res_s := by
  intro ⟨h1, h2⟩
  rw [evaluate_none_nested_seq_append p s s1 q h1, h2]

/-- Exact HOL `loop_eval_upd_clock` (`crep_to_loopProofScript.sml:3301-3302`, `[local]`):
    `loopSem$eval (s with clock := v) = eval s` (an equation of functions). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "loop_eval_upd_clock"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loop_eval_upd_clock (s : LoopSemStateFiniteExact width F) (v : Nat) :
    eval { s with clock := v } = eval s :=
  funext fun e => eval_upd_clock_eq s e v

/-- Exact HOL `evaluate_Seq_Skip` (`crep_to_loopProofScript.sml:4010-4011`, `[local]`):
    `loopSem$evaluate (Seq prog Skip, s) = evaluate (prog, s)`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "evaluate_Seq_Skip"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluate_Seq_Skip (prog : HolLoopProg width) (s : LoopSemStateFiniteExact width F) :
    evaluate (.seq prog .skip) s = evaluate prog s := by
  rw [evaluate_seq]
  cases evaluate prog s with
  | mk r t => cases r <;> simp [evaluate]

theorem with_clock_with_clock (s : LoopSemStateFiniteExact width F) (a b : Nat) :
    ({ { s with clock := a } with clock := b } : LoopSemStateFiniteExact width F) =
      { s with clock := b } := by
  cases s; rfl

theorem eq_with_clock_of_clock_zero {s s3 : LoopSemStateFiniteExact width F}
    (h : ({ s with clock := 0 } : LoopSemStateFiniteExact width F) = { s3 with clock := 0 }) :
    s3 = { s with clock := s3.clock } := by
  cases s; cases s3
  simp only [LoopSemStateFiniteExact.mk.injEq] at h ⊢
  simp_all

/-- Exact HOL `evaluate_less_clock_cases` (`crep_to_loopProofScript.sml:4018-4024`,
    `[local]`); its free variables `prog s res s2 ck` are universally quantified. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "evaluate_less_clock_cases"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluate_less_clock_cases (prog : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (res : Option (LoopResultExact width)) (s2 : LoopSemStateFiniteExact width F) (ck : Nat) :
    evaluate prog s = (res, s2) → ck ≤ s.clock →
      ∃ res2 s3, evaluate prog { s with clock := ck } = (res2, s3) ∧
        ((res = res2 ∧ ∃ ck2, s3 = { s2 with clock := ck2 }) ∨ res2 = some .timeOut) := by
  intro h hck
  cases he : evaluate prog { s with clock := ck } with
  | mk res2 s3 =>
    refine ⟨res2, s3, rfl, ?_⟩
    by_cases hto : res2 = some .timeOut
    · exact Or.inr hto
    · left
      have hadd := evaluate_add_clock_eq prog { s with clock := ck } res2 s3 (s.clock - ck) he hto
      have hs : ({ { s with clock := ck } with clock := ck + (s.clock - ck) } :
          LoopSemStateFiniteExact width F) = s := by
        rw [with_clock_with_clock, show ck + (s.clock - ck) = s.clock by omega]
      simp only at hadd
      rw [hs, h] at hadd
      simp only [Prod.mk.injEq] at hadd
      obtain ⟨rfl, rfl⟩ := hadd
      exact ⟨rfl, s3.clock, by rw [with_clock_with_clock]⟩

/-- Exact HOL `evaluate_twice_cases` (`crep_to_loopProofScript.sml:4036-4044`,
    `[local]`); its free variables `prog s res s2 s3 res2 s4` are universally
    quantified. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "evaluate_twice_cases"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluate_twice_cases (prog : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (res : Option (LoopResultExact width)) (s2 s3 : LoopSemStateFiniteExact width F)
    (res2 : Option (LoopResultExact width)) (s4 : LoopSemStateFiniteExact width F) :
    evaluate prog s = (res, s2) → evaluate prog s3 = (res2, s4) →
      ({ s with clock := 0 } : LoopSemStateFiniteExact width F) = { s3 with clock := 0 } →
      (s.clock ≤ s3.clock ∧ (res = some .timeOut ∨
        (res = res2 ∧ ∃ ck, s2 = { s4 with clock := ck }))) ∨
      (s3.clock ≤ s.clock ∧ (res2 = some .timeOut ∨
        (res2 = res ∧ ∃ ck, s4 = { s2 with clock := ck }))) := by
  intro h1 h2 hclk
  have hs3 := eq_with_clock_of_clock_zero hclk
  by_cases hle : s.clock ≤ s3.clock
  · left
    refine ⟨hle, ?_⟩
    by_cases hto : res = some .timeOut
    · exact Or.inl hto
    · right
      have hadd := evaluate_add_clock_eq prog s res s2 (s3.clock - s.clock) h1 hto
      rw [show s.clock + (s3.clock - s.clock) = s3.clock by omega, ← hs3, h2] at hadd
      simp only [Prod.mk.injEq] at hadd
      obtain ⟨rfl, rfl⟩ := hadd
      exact ⟨rfl, s2.clock, by rw [with_clock_with_clock]⟩
  · right
    have hle' : s3.clock ≤ s.clock := by omega
    refine ⟨hle', ?_⟩
    by_cases hto : res2 = some .timeOut
    · exact Or.inl hto
    · right
      have hs : s = { s3 with clock := s.clock } := by
        rw [hs3, with_clock_with_clock]
      have hadd := evaluate_add_clock_eq prog s3 res2 s4 (s.clock - s3.clock) h2 hto
      rw [show s3.clock + (s.clock - s3.clock) = s.clock by omega, ← hs, h1] at hadd
      simp only [Prod.mk.injEq] at hadd
      obtain ⟨rfl, rfl⟩ := hadd
      exact ⟨rfl, s4.clock, by rw [with_clock_with_clock]⟩

end LoopSemStateFiniteExact
end Flapjack
