import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Leaves
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PermuteSwap

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

namespace EvaluateApplyColourSeqWitnesses
/-- Canonical imported state-carrier roundtrip; no duplicate carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end EvaluateApplyColourSeqWitnesses

/-- HOL `evaluate_apply_colour`, Seq case. Only the genuine subprogram
induction hypotheses supplement the original three premises. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateApplyColour_Seq {width : Nat} [NeZero width] {C F : Type}
    (first second : WordLangProgHOL (BitVec width))
    (ihFirst : applyColourGoal C F first) (ihSecond : applyColourGoal C F second) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.seq first second) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.seq first second) live lt)) st.locals cst.locals →
      applyColourPost f (.seq first second) live lt st cst := by
  classical
  rintro st cst f live lt ⟨hc, hs, hl⟩
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc1 := hc.2.2
  have hc2 := hc.2.1
  obtain ⟨p1, hp1⟩ := ihFirst st cst f (getLive second live lt) lt ⟨hc1, hs, by simpa only [getLive] using hl⟩
  rcases he1 : evaluate first { st with permute := p1 } with ⟨r1, s1⟩
  rw [he1] at hp1
  dsimp only at hp1
  by_cases herr : r1 = some .error
  · refine ⟨p1, ?_⟩
    simp only [ht, he1, herr]
    trivial
  · rw [if_neg herr] at hp1
    rcases hec1 : evaluate (applyColour f first) cst with ⟨rc1, cs1⟩
    rw [hec1] at hp1
    dsimp only at hp1
    obtain ⟨hr1, hs1, hl1⟩ := hp1
    subst rc1
    cases r1 with
    | some result =>
        refine ⟨p1, ?_⟩
        simp only [ht, he1, applyColour, hec1]
        rw [if_neg herr]
        refine ⟨trivial, hs1, ?_⟩
        cases result <;> exact hl1
    | none =>
        obtain ⟨p2, hp2⟩ := ihSecond s1 cs1 f live lt ⟨hc2, hs1, hl1⟩
        obtain ⟨p0, he0⟩ := permute_swap_lemma first { st with permute := p1 } p2
          (by rw [he1]; simp)
        rw [he1] at he0
        simp only at he0
        have he0' : evaluate first { st with permute := p0 } =
            (none, { s1 with permute := p2 }) := by
          simpa only using he0
        refine ⟨p0, ?_⟩
        simp only [ht, he0', applyColour, hec1]
        exact hp2

end Flapjack.WordAlloc
