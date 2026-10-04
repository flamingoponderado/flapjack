import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Leaves

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

namespace EvaluateApplyColourIfWitnesses
/-- Canonical imported state-carrier roundtrip; no duplicate carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end EvaluateApplyColourIfWitnesses

/-- HOL `evaluate_apply_colour`, If case. Only the genuine two branch
induction hypotheses supplement the original three premises. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateApplyColour_If {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (left : Nat) (right : WordRegImm (BitVec width))
    (yes no : WordLangProgHOL (BitVec width))
    (ihYes : applyColourGoal C F yes) (ihNo : applyColourGoal C F no) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.ite cmp left right yes no) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.ite cmp left right yes no) live lt)) st.locals cst.locals →
      applyColourPost f (.ite cmp left right yes no) live lt st cst := by
  classical
  rintro st cst f live lt ⟨hc, hs, hl⟩
  have hv : ∀ perm : Nat → Nat → Nat,
      getVar left { st with permute := perm } = getVar left st := fun _ => rfl
  have hi : ∀ perm : Nat → Nat → Nat,
      WordSemStateFiniteExact.getVarImm right { st with permute := perm } = WordSemStateFiniteExact.getVarImm right st := by
    intro perm; cases right <;> rfl
  have hm : ∀ key, sptDomain (sptUnion (getLive yes live lt) (getLive no live lt)) key →
      sptDomain (getLive (.ite cmp left right yes no) live lt) key := by
    intro key hk
    cases right <;> simp only [getLive]
    case imm =>
        exact (sptDomain_ins _ _ _ key).mpr (Or.inr hk)
    case reg =>
        exact (sptDomain_ins _ _ _ key).mpr (Or.inr
          ((sptDomain_ins _ _ _ key).mpr (Or.inr hk)))
  have hleft : sptDomain (getLive (.ite cmp left right yes no) live lt) left := by
    cases right <;> simp only [getLive]
    case imm => exact (sptDomain_ins _ _ _ left).mpr (Or.inl rfl)
    case reg => exact (sptDomain_ins _ _ _ left).mpr (Or.inr
        ((sptDomain_ins _ _ _ left).mpr (Or.inl rfl)))
  cases hx : getVar left st with
  | none =>
      refine ⟨st.permute, ?_⟩
      rw [evaluate, hv, hx]
      simp
  | some x =>
      cases hy : WordSemStateFiniteExact.getVarImm right st with
      | none =>
          refine ⟨st.permute, ?_⟩
          rw [evaluate, hv, hi, hx, hy]
          simp
      | some y =>
          have hcx := strongLocalsRelGetVar f _ st cst left x ⟨hl, hleft, hx⟩
          have hcy := strongLocalsRelGetVarImm f _ st cst right y ⟨hl, by
            cases right <;> simp only [getLive]
            case reg => exact (sptDomain_ins _ _ _ _).mpr (Or.inl rfl), hy⟩
          cases hw : wordSemWordCmp cmp x y with
          | none =>
              refine ⟨st.permute, ?_⟩
              rw [evaluate, hv, hi, hx, hy]
              simp [hw]
          | some decision =>
              cases decision with
              | false =>
                  obtain ⟨perm, hp⟩ := ihNo st cst f live lt
                    ⟨hc.2.2, hs, slrMono hl (fun k hk => hm k
                      ((sptDomain_uni _ _ k).mpr (Or.inr hk)))⟩
                  refine ⟨perm, ?_⟩
                  rw [evaluate, hv, hi, hx, hy]
                  simp only [hw]
                  simp only [applyColour]
                  rw [evaluate, hcx, hcy]
                  simpa only [hw] using hp
              | true =>
                  obtain ⟨perm, hp⟩ := ihYes st cst f live lt
                    ⟨hc.2.1, hs, slrMono hl (fun k hk => hm k
                      ((sptDomain_uni _ _ k).mpr (Or.inl hk)))⟩
                  refine ⟨perm, ?_⟩
                  rw [evaluate, hv, hi, hx, hy]
                  simp only [hw]
                  simp only [applyColour]
                  rw [evaluate, hcx, hcy]
                  simpa only [hw] using hp

end Flapjack.WordAlloc
