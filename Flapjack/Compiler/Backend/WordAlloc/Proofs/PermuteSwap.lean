import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PermuteSwap

/-!
# Word allocation permutation-oracle swap

Counterpart of `word_allocProofScript.sml:836-851` (`permute_swap_lemma4`),
the form of wordProps `permute_swap_lemma` used by `evaluate_apply_colour`.
-/

namespace Flapjack.WordAlloc

namespace PermuteSwapWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end PermuteSwapWitnesses

open PermuteSwapWitnesses

/-- Exact HOL `permute_swap_lemma4` (`word_allocProofScript.sml:836-851`).
HOL's `(I ## (λs. s with permute := perm))` is the pair map applying the state
update to the second component. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem permuteSwapLemma4 {width : Nat} [NeZero width] {C F : Type}
    (prog : WordLangProgHOL (BitVec width)) (st : WordSemStateFiniteExact width C F)
    (P : Option (WordSemResult width) × WordSemStateFiniteExact width C F → Prop) :
    (∀ st', WordSemStateFiniteExact.evaluate prog st = (some .error, st') →
        P (some .error, st')) ∧
      (∃ perm, P ((fun p => (p.1, { p.2 with permute := perm }))
        (WordSemStateFiniteExact.evaluate prog st))) →
    ∃ perm, P (WordSemStateFiniteExact.evaluate prog { st with permute := perm }) := by
  rintro ⟨herr, perm, hP⟩
  rcases he : WordSemStateFiniteExact.evaluate prog st with ⟨res, rst⟩
  rw [he] at hP
  by_cases hres : res = some .error
  · subst hres
    refine ⟨st.permute, ?_⟩
    have hst : ({ st with permute := st.permute } : WordSemStateFiniteExact width C F) = st := rfl
    rw [hst, he]
    exact herr rst he
  · have hsw := WordSemStateFiniteExact.permute_swap_lemma prog st perm
    rw [he] at hsw
    obtain ⟨perm', hperm'⟩ := hsw hres
    exact ⟨perm', by rw [hperm']; exact hP⟩

end Flapjack.WordAlloc
