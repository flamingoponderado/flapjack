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

/-- HOL Seq constructor case; the only added premises are the two
subprogram induction hypotheses for the same domain-preservation statement. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_locals_same_fdom"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateLocalsSameFdomSeqExact {width : Nat} [NeZero width] {σ : Type}
    (s s' : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width))
    (first second : CrepProgHOL width)
    (ihFirst : ∀ (u t : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width)),
      evalCrepSemHOLProgExact u first = (r,t) →
      (match (generalizing := false) r with
      | none => True
      | some (.break _) => True
      | some (.continue _) => True
      | _ => False) → crepHolFdom u.locals.lookup = crepHolFdom t.locals.lookup)
    (ihSecond : ∀ (u t : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width)),
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
        exact (ihFirst s t none hfirst True.intro).trans
          (ihSecond t s' r heval hresult)
      · obtain ⟨hr,ht⟩ := Prod.ext_iff.mp heval
        simp only at hr ht
        subst r
        subst s'
        exact ihFirst s t res hfirst hresult

/-- HOL If constructor case; retain both branch induction hypotheses. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_locals_same_fdom"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateLocalsSameFdomIfExact {width : Nat} [NeZero width] {σ : Type}
    (s s' : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width))
    (condition : CrepExpHOL width) (yes no : CrepProgHOL width)
    (ihYes : ∀ (u t : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width)),
      evalCrepSemHOLProgExact u yes = (r,t) →
      (match (generalizing := false) r with
      | none => True
      | some (.break _) => True
      | some (.continue _) => True
      | _ => False) → crepHolFdom u.locals.lookup = crepHolFdom t.locals.lookup)
    (ihNo : ∀ (u t : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width)),
      evalCrepSemHOLProgExact u no = (r,t) →
      (match (generalizing := false) r with
      | none => True
      | some (.break _) => True
      | some (.continue _) => True
      | _ => False) → crepHolFdom u.locals.lookup = crepHolFdom t.locals.lookup)
    (heval : evalCrepSemHOLProgExact s (.ite condition yes no) = (r,s'))
    (hresult : match (generalizing := false) r with
      | none => True
      | some (.break _) => True
      | some (.continue _) => True
      | _ => False) :
    crepHolFdom s.locals.lookup = crepHolFdom s'.locals.lookup := by
  rw [evalCrepSemHOLProgExact_ite_holShape] at heval
  split at heval
  · split at heval
    · exact ihYes s s' r heval hresult
    · exact ihNo s s' r heval hresult
  · have hs := congrArg Prod.snd heval
    simp only at hs
    subst s'
    rfl

/-- HOL Dec constructor case: the body IH fixes the updated domain;
restoring the scoped key restores its original membership. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_locals_same_fdom"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateLocalsSameFdomDecExact {width : Nat} [NeZero width] {σ : Type}
    (s s' : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width))
    (name : Nat) (value : CrepExpHOL width) (body : CrepProgHOL width)
    (ihBody : ∀ (u t : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width)),
      evalCrepSemHOLProgExact u body = (r,t) →
      (match (generalizing := false) r with
      | none => True
      | some (.break _) => True
      | some (.continue _) => True
      | _ => False) → crepHolFdom u.locals.lookup = crepHolFdom t.locals.lookup)
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
          have hd := ihBody u t res hb hresult
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
