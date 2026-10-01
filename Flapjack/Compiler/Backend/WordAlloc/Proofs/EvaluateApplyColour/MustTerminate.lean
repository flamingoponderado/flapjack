import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Leaves

namespace Flapjack.WordAlloc
open WordSemStateFiniteExact

namespace EvaluateApplyColourMustTerminateWitnesses
/-- Canonical imported state-carrier roundtrip; no duplicate carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end EvaluateApplyColourMustTerminateWitnesses

/-- HOL `evaluate_apply_colour`, MustTerminate case, with only the genuine
body induction hypothesis in addition to the original three premises. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_MustTerminate {width : Nat} [NeZero width] {C F : Type}
    (body : WordLangProgHOL (BitVec width)) (ih : applyColourGoal C F body) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.mustTerminate body) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.mustTerminate body) live lt)) st.locals cst.locals →
      applyColourPost f (.mustTerminate body) live lt st cst := by
  classical
  rintro st cst f live lt ⟨hc, hs, hl⟩
  by_cases hz : st.termdep = 0
  · refine ⟨st.permute, ?_⟩
    rw [evaluate]
    simp [hz]
  · have hdep : cst.termdep = st.termdep := by simp_all [wordStateEqRel]
    have hclk := wsrClock hs
    let s := { st with clock := wordSemMustTerminateLimit width, termdep := st.termdep - 1 }
    let cs := { cst with clock := wordSemMustTerminateLimit width, termdep := cst.termdep - 1 }
    have hsc : wordStateEqRel s cs := by simp_all [s, cs, wordStateEqRel]
    obtain ⟨perm, hp⟩ := ih s cs f live lt
      ⟨hc, hsc, by simpa only [getLive] using hl⟩
    rcases he : evaluate body { s with permute := perm } with ⟨res, rs⟩
    rw [he] at hp
    dsimp only at hp
    refine ⟨perm, ?_⟩
    rw [evaluate]
    simp only [dif_neg hz]
    have hein : evaluate body
        { { st with permute := perm } with clock := wordSemMustTerminateLimit width, termdep := st.termdep - 1 } = (res, rs) := he
    rw [hein]
    by_cases herr : res = some .error
    · subst res
      simp
    · rw [if_neg herr] at hp
      rcases hec : evaluate (applyColour f body) cs with ⟨resc, rcs⟩
      rw [hec] at hp
      dsimp only at hp
      obtain ⟨hr, hsr, hloc⟩ := hp
      subst resc
      cases res with
      | none =>
          simp only [applyColour]
          rw [evaluate]
          simp only [hdep, dif_neg hz]
          rw [show evaluate (applyColour f body)
            { cst with clock := wordSemMustTerminateLimit width, termdep := st.termdep - 1 }
              = (none, rcs) by simpa only [cs, hdep] using hec]
          simp_all [wordStateEqRel, applyColourLocals]
      | some result =>
          cases result with
          | timeOut => simp
          | error => exact (herr rfl).elim
          | _ =>
              simp only [applyColour]
              rw [evaluate]
              simp only [hdep, dif_neg hz]
              rw [show evaluate (applyColour f body)
                { cst with clock := wordSemMustTerminateLimit width, termdep := st.termdep - 1 }
                  = (_, rcs) by simpa only [cs, hdep] using hec]
              simp_all [wordStateEqRel, applyColourLocals]

end Flapjack.WordAlloc
