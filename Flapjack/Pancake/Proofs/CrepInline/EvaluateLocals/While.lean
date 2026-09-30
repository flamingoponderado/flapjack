import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.Structural
import Flapjack.Pancake.Semantics.CrepSem.EvaluateInd

namespace Flapjack.CrepInlineExact

/-- Flapjack-specific spelling of the motive of HOL's domain-preservation
induction. No independent HOL declaration is claimed for this abbreviation. -/
abbrev localsDomainMotive {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width σ) : Prop :=
  ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ),
    evalCrepSemHOLProgExact s p = (r,s') →
    (match (generalizing := false) r with
     | none => True
     | some (.continue _) => True
     | some (.break _) => True
     | _ => False) →
    crepHolFdom s.locals.lookup = crepHolFdom s'.locals.lookup

/-- The three guarded recursion premises of the exact HOL evaluate_ind
While case, specialized to localsDomainMotive. This infrastructure records
which recursive evaluations are justified; it is not a HOL theorem port. -/
structure WhileDomainIH {width : Nat} [NeZero width] {σ : Type}
    (e : CrepExpHOL width) (c : CrepProgHOL width)
    (s : CrepSemHOLState width σ) : Prop where
  continueCase : ∀ v2 w res s1 v1 v8,
    crepExactEvalExpClassical s e = some v2 → v2 = .word w → w ≠ 0 → s.clock ≠ 0 →
    (res,s1) = evalCrepSemHOLProgExact (decClockCrepSemHOL s) c →
    res = some v1 → v1 = .continue v8 → v8 = 0 → localsDomainMotive (.while e c) s1
  normalCase : ∀ v2 w res s1,
    crepExactEvalExpClassical s e = some v2 → v2 = .word w → w ≠ 0 → s.clock ≠ 0 →
    (res,s1) = evalCrepSemHOLProgExact (decClockCrepSemHOL s) c →
    res = none → localsDomainMotive (.while e c) s1
  bodyCase : ∀ v2 w,
    crepExactEvalExpClassical s e = some v2 → v2 = .word w → w ≠ 0 → s.clock ≠ 0 →
    localsDomainMotive c (decClockCrepSemHOL s)

namespace WhileLocalsSupport
/-- Flapjack-specific canonical carrier roundtrip re-export. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end WhileLocalsSupport

/-- HOL While domain case. The bundled IH contains exactly the three guarded
recursive premises of evaluate_ind, specialized to the original domain motive. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_locals_same_fdom"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateLocalsSameFdomWhileExact {width : Nat} [NeZero width] {σ : Type}
    (s s' : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width))
    (e : CrepExpHOL width) (c : CrepProgHOL width)
    (ih : WhileDomainIH e c s)
    (heval : evalCrepSemHOLProgExact s (.while e c) = (r,s'))
    (hresult : match (generalizing := false) r with
      | none => True | some (.continue _) => True | some (.break _) => True
      | _ => False) :
    crepHolFdom s.locals.lookup = crepHolFdom s'.locals.lookup := by
  classical
  rw [evalCrepSemHOLProgExact_while_holShape] at heval
  split at heval
  · rename_i w hexp
    by_cases hw : w ≠ 0
    · rw [if_pos hw] at heval
      by_cases hc : s.clock = 0
      · rw [if_pos hc] at heval
        obtain ⟨hr, ht⟩ := Prod.ext_iff.mp heval
        simp only at hr ht
        subst r
        exact False.elim hresult
      · rw [if_neg hc] at heval
        have hclass : crepExactEvalExpClassical s e = some (.word w) := by
          simpa only [crepExactEvalExpClassical_eq, crepExactEvalExp_eq_eval] using hexp
        have hbody := ih.bodyCase (.word w) w hclass rfl hw hc
        cases hb : evalCrepSemHOLProgExact (decClockCrepSemHOL s) c with
        | mk res t =>
          rw [hb] at heval
          have hdom (hg : match (generalizing := false) res with
              | none => True | some (.continue _) => True | some (.break _) => True
              | _ => False) : crepHolFdom s.locals.lookup = crepHolFdom t.locals.lookup :=
            hbody res t hb hg
          cases res with
          | none =>
            simp only at heval
            exact (hdom True.intro).trans
              (ih.normalCase (.word w) w none t hclass rfl hw hc hb.symm rfl r s' heval hresult)
          | some result =>
            cases result <;> simp only [exitLoopCrepResult] at heval
            all_goals try
              obtain ⟨hr, ht⟩ := Prod.ext_iff.mp heval
              simp only at hr ht
              subst r
              exact False.elim hresult
            all_goals rename_i n
            all_goals cases n with
            | zero =>
              simp only at heval
              first
              | exact (hdom True.intro).trans
                  (ih.continueCase (.word w) w _ t _ 0 hclass rfl hw hc hb.symm rfl rfl rfl
                    r s' heval hresult)
              | obtain ⟨hr, ht⟩ := Prod.ext_iff.mp heval
                simp only at hr ht
                subst s'
                exact hdom True.intro
            | succ n =>
              simp only at heval
              obtain ⟨hr, ht⟩ := Prod.ext_iff.mp heval
              simp only at hr ht
              subst s'
              exact hdom True.intro
    · rw [if_neg hw] at heval
      have ht := congrArg Prod.snd heval
      simp only at ht
      subst s'
      rfl
  · have ht := congrArg Prod.snd heval
    simp only at ht
    subst s'
    rfl

end Flapjack.CrepInlineExact
