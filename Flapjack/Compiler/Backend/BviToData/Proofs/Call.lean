module

public import Flapjack.Compiler.Backend.BviToData.Proofs.CompileCorrect
public import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateList

@[expose] public section

/-! Return-value facts used in the BVI-to-data correctness proof. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

private theorem evaluate_vars_of_relation {C F : Type} (indices : List Nat) (values env : List BvlSem.Value)
    (state : BviSem.BviState C F)
    (lookups : List.Forall₂ (fun index value => env[index]? = some value) indices values) :
    BviSem.evaluate (indices.map Bvi.Exp.var) env state = (.val values, state) := by
  induction lookups with
  | nil => simp [BviSem.evaluate]
  | @cons index value indices values lookup rest ih =>
    cases indices with
    | nil =>
      cases rest
      simp [BviSem.evaluate, lookup]
    | cons second more =>
      rw [List.map_cons, List.map_cons, BviSem.evaluate, BviSem.fixClock_evaluate]
      simp only [List.map_cons] at ih
      simp [BviSem.evaluate, lookup, ih]
      rfl

namespace ReturnCarrier
/-- The BVI reference carrier and its finite-support view roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end ReturnCarrier

/-- Returning the first `rets` environment values forwards exactly those values. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "evaluate_Return_GENLIST_Var"
  (fmap_as_finite_support := [refs])]
theorem evaluate_return_range {C F : Type} (rets : Nat) (values env : List BvlSem.Value)
    (state : BviSem.BviState C F) (length : values.length = rets) :
    BviSem.evaluateTuple ([.return ((List.range rets).map Bvi.Exp.var)], values ++ env, state) =
      (.err (.raise (.ret values)), state) := by
  change BviSem.evaluate [.return ((List.range rets).map Bvi.Exp.var)] (values ++ env) state = _
  have lookups : List.Forall₂ (fun index value => (values ++ env)[index]? = some value) (List.range rets) values := by
    apply List.forall₂_iff_get.mpr
    constructor
    · simp [length]
    · intro index leftBound rightBound
      have bound : index < values.length := rightBound
      simp [List.getElem?_append, bound]
  have evaluated := evaluate_vars_of_relation (List.range rets) values (values ++ env) state lookups
  simp [BviSem.evaluate, evaluated]

end Flapjack.Compiler.Backend.BviToData
