import Flapjack.Pancake.Proofs.CrepInline

namespace Flapjack.CrepInlineExact
namespace ExtCallLocalsSupport
/-- Flapjack-specific canonical state roundtrip re-export. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end ExtCallLocalsSupport

/-- ExtCall case of HOL evaluate_locals_same_fdom. Both FFI outcomes and every
failure preserve locals; the original normal/Break/Continue guard is retained. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_locals_same_fdom"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateLocalsSameFdomExtCallExact {width : Nat} [NeZero width] {σ : Type}
    (s s' : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width))
    (function : Basis.Pure.MlString.MlString)
    (configuration configurationLength array arrayLength : Nat)
    (heval : evalCrepSemHOLProgExact s
      (.extCall function configuration configurationLength array arrayLength) = (r,s'))
    (_hresult : match r with
      | none => True
      | some (.break _) => True
      | some (.continue _) => True
      | _ => False) :
    crepHolFdom s.locals.lookup = crepHolFdom s'.locals.lookup := by
  rw [evalCrepSemHOLProgExact_extCall_holShape] at heval
  repeat' split at heval
  all_goals
    have hs := congrArg Prod.snd heval
    simp only at hs
    subst s'
    rfl

end Flapjack.CrepInlineExact
