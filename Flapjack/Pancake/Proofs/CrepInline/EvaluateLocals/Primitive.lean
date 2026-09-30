import Flapjack.Pancake.Proofs.CrepInline

namespace Flapjack.CrepInlineExact
namespace PrimitiveLocalsSupport
/-- Flapjack-specific canonical state roundtrip re-export. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end PrimitiveLocalsSupport

/-- Flapjack-specific canonical map infrastructure: updating existing keys
preserves domain membership at every query. No independent HOL declaration. -/
theorem updateListEqIsSomeOfPresent {α β : Type} [DecidableEq α]
    (m : HolFiniteMapExact α β) (entries : List (α × β))
    (hpresent : ∀ e ∈ entries, (m.lookup e.1).isSome = true) :
    ∀ key, ((m.updateListEq entries).lookup key).isSome = (m.lookup key).isSome := by
  induction entries generalizing m with
  | nil => intro key; rfl
  | cons entry entries ih =>
      have hup : ∀ key, ((m.updateEq entry).lookup key).isSome = (m.lookup key).isSome := by
        intro key
        by_cases heq : key = entry.1
        · subst key
          simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, hpresent entry (by simp)]
        · simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, heq]
      have htail : ∀ e ∈ entries, ((m.updateEq entry).lookup e.1).isSome = true := by
        intro e he
        rw [hup]
        exact hpresent e (by simp [he])
      intro key
      change (((m.updateEq entry).updateListEq entries).lookup key).isSome = _
      rw [ih (m.updateEq entry) htail key, hup]

/-- Primitive case of HOL evaluate_locals_same_fdom. The exact successful
clause checks all destinations are already bound before its update list. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_locals_same_fdom"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateLocalsSameFdomPrimitiveExact {width : Nat} [NeZero width] {σ : Type}
    (s s' : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width))
    (names args : List Nat) (operator : PrimOp)
    (heval : evalCrepSemHOLProgExact s (.primitive names operator args) = (r,s'))
    (_hresult : match r with
      | none => True
      | some (.break _) => True
      | some (.continue _) => True
      | _ => False) :
    crepHolFdom s.locals.lookup = crepHolFdom s'.locals.lookup := by
  rw [evalCrepSemHOLProgExact_primitive_holShape] at heval
  split at heval
  · split at heval
    · split at heval
      · rename_i values results hg
        have hs := congrArg Prod.snd heval
        simp only at hs
        subst s'
        funext key
        apply Eq.symm
        apply updateListEqIsSomeOfPresent
        intro e he
        exact hg.2.1 e.1 (List.of_mem_zip he).1
      · have hs := congrArg Prod.snd heval
        simp only at hs
        subst s'
        rfl
    · have hs := congrArg Prod.snd heval
      simp only at hs
      subst s'
      rfl
  · have hs := congrArg Prod.snd heval
    simp only at hs
    subst s'
    rfl

end Flapjack.CrepInlineExact
