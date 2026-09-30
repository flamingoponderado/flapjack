import Flapjack.Pancake.Proofs.CrepInline

namespace Flapjack.CrepInlineExact
namespace StructuralLocalsSupport
/-- Flapjack-specific canonical state roundtrip re-export. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end StructuralLocalsSupport

/-- HOL Seq case with the original fixed-state first IH and continuation IH
guarded by the source first run and NONE result. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_locals_same_fdom"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateLocalsSameFdomSeqExact {width : Nat} [NeZero width] {σ : Type}
    (s s' : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width))
    (first second : CrepProgHOL width)
    (ihFirst : ∀ (t : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width)),
      evalCrepSemHOLProgExact s first = (r,t) →
      (match (generalizing := false) r with
      | none => True
      | some (.break _) => True
      | some (.continue _) => True
      | _ => False) → crepHolFdom s.locals.lookup = crepHolFdom t.locals.lookup)
    (ihSecond : ∀ (r1 : Option (CrepResultHOLExact width)) (u : CrepSemHOLState width σ),
      (r1,u) = evalCrepSemHOLProgExact s first → r1 = none →
      ∀ (t : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width)),
      evalCrepSemHOLProgExact u second = (r,t) →
      (match (generalizing := false) r with
      | none => True
      | some (.break _) => True
      | some (.continue _) => True
      | _ => False) → crepHolFdom u.locals.lookup = crepHolFdom t.locals.lookup)
    (heval : evalCrepSemHOLProgExact s (.seq first second) = (r,s'))
    (hresult : match (generalizing := false) r with
      | none => True
      | some (.break _) => True
      | some (.continue _) => True
      | _ => False) :
    crepHolFdom s.locals.lookup = crepHolFdom s'.locals.lookup := by
  rw [evalCrepSemHOLProgExact_seq_holShape] at heval
  cases hfirst : evalCrepSemHOLProgExact s first with
  | mk res t =>
      rw [hfirst] at heval
      simp only [] at heval
      split at heval
      · rename_i hn
        subst res
        exact (ihFirst t none hfirst True.intro).trans
          (ihSecond none t hfirst.symm rfl s' r heval hresult)
      · obtain ⟨hr,ht⟩ := Prod.ext_iff.mp heval
        simp only at hr ht
        subst r
        subst s'
        exact ihFirst t res hfirst hresult

/-- HOL If case with its single original guarded selected-branch IH at the
fixed source state, rather than hypotheses generalized over arbitrary states. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_locals_same_fdom"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateLocalsSameFdomIfExact {width : Nat} [NeZero width] {σ : Type}
    (s s' : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width))
    (condition : CrepExpHOL width) (yes no : CrepProgHOL width)
    (ih : ∀ (value : HolWordLab width) (w : BitVec width),
      crepExactEvalExpClassical s condition = some value → value = .word w →
      ∀ (t : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width)),
      evalCrepSemHOLProgExact s (if w ≠ 0 then yes else no) = (r,t) →
      (match (generalizing := false) r with
      | none => True
      | some (.break _) => True
      | some (.continue _) => True
      | _ => False) → crepHolFdom s.locals.lookup = crepHolFdom t.locals.lookup)
    (heval : evalCrepSemHOLProgExact s (.ite condition yes no) = (r,s'))
    (hresult : match (generalizing := false) r with
      | none => True
      | some (.break _) => True
      | some (.continue _) => True
      | _ => False) :
    crepHolFdom s.locals.lookup = crepHolFdom s'.locals.lookup := by
  rw [evalCrepSemHOLProgExact_ite_holShape] at heval
  cases hv : evalCrepSemHOLExp s condition with
  | none =>
      rw [hv] at heval
      have hs := congrArg Prod.snd heval
      simp only at hs
      subst s'
      rfl
  | some value =>
      cases value with
      | word w =>
          rw [hv] at heval
          have hcl : crepExactEvalExpClassical s condition = some (.word w) := by
            simpa only [crepExactEvalExpClassical_eq, crepExactEvalExp_eq_eval] using hv
          exact ih (.word w) w hcl rfl s' r heval hresult

/-- HOL Dec constructor case: the body IH fixes the updated domain;
restoring the scoped key restores its original membership. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_locals_same_fdom"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateLocalsSameFdomDecExact {width : Nat} [NeZero width] {σ : Type}
    (s s' : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width))
    (name : Nat) (value : CrepExpHOL width) (body : CrepProgHOL width)
    (ihBody : ∀ val, crepExactEvalExpClassical s value = some val →
      ∀ (t : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width)),
      evalCrepSemHOLProgExact (CrepSemHOLState.setVar name val s) body = (r,t) →
      (match (generalizing := false) r with
      | none => True
      | some (.break _) => True
      | some (.continue _) => True
      | _ => False) → crepHolFdom (CrepSemHOLState.setVar name val s).locals.lookup = crepHolFdom t.locals.lookup)
    (heval : evalCrepSemHOLProgExact s (.dec name value body) = (r,s'))
    (hresult : match (generalizing := false) r with
      | none => True
      | some (.break _) => True
      | some (.continue _) => True
      | _ => False) :
    crepHolFdom s.locals.lookup = crepHolFdom s'.locals.lookup := by
  rw [evalCrepSemHOLProgExact_dec_holShape] at heval
  cases hv : evalCrepSemHOLExp s value with
  | none =>
      simp only [hv] at heval
      have hs := congrArg Prod.snd heval
      simp only at hs
      subst s'
      rfl
  | some val =>
      simp only [hv] at heval
      let u : CrepSemHOLState width σ := {s with locals := s.locals.updateEq (name,val)}
      change (match evalCrepSemHOLProgExact u body with
        | (res,t) => (res,{t with locals := t.locals.resVarEq (name,s.locals.lookup name)})) = (r,s') at heval
      cases hb : evalCrepSemHOLProgExact u body with
      | mk res t =>
          rw [hb] at heval
          simp only [] at heval
          obtain ⟨hr,ht⟩ := Prod.ext_iff.mp heval
          simp only at hr ht
          subst r
          subst s'
          have hcl : crepExactEvalExpClassical s value = some val := by
            simpa only [crepExactEvalExpClassical_eq, crepExactEvalExp_eq_eval] using hv
          have hd : crepHolFdom u.locals.lookup = crepHolFdom t.locals.lookup :=
            ihBody val hcl t res hb hresult
          funext key
          have hk := congrFun hd key
          by_cases heq : key = name
          · subst key
            cases hlookup : s.locals.lookup name <;>
              simp [crepHolFdom, HolFiniteMapExact.resVarEq, FUPDATE_HOL, FDOMSUB_HOL, hlookup]
          · cases hlookup : s.locals.lookup name <;>
              simpa [crepHolFdom, u, HolFiniteMapExact.resVarEq,
                HolFiniteMapExact.updateEq, HolFiniteMapExact.eraseEq,
                FUPDATE_HOL, FDOMSUB_HOL, heq, hlookup] using hk

end Flapjack.CrepInlineExact
