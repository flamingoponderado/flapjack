module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.Relations
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section


/-! Exact closure-application equations for the known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Relations.AppExact
open ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Exact application of an uncurried closure either times out or evaluates
its body with the arguments followed by the captured environment. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_app_exact_rw"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAppExactRw {C F : Type} (args env : List ClosSem.Value) (numArgs loc : Nat)
    (body : ClosLang.Exp) (s : State C F) (h : args ≠ [] ∧ numArgs = args.length) :
    evaluateApp (some loc) (.closure (some loc) [] env numArgs body) args s =
      if s.clock < args.length then (.err (.abort .timeoutError), { s with clock := 0 })
      else evaluate [body] (args ++ env) (decClock numArgs s) := by
  rcases h with ⟨nonempty, rfl⟩
  have pos : 0 < args.length := List.length_pos_iff.mpr nonempty
  have takeAll : args.reverse.take args.length = args.reverse := by
    simpa only [List.length_reverse] using
      (show args.reverse.take args.reverse.length = args.reverse from List.take_length)
  have dest : destClosure s.maxApp (some loc) (.closure (some loc) [] env args.length body) args =
      some (.fullApp body (args ++ env) []) := by
    simp [destClosure, checkLoc, pos, takeAll]
  cases args with
  | nil => contradiction
  | cons first rest =>
    rw [evaluateApp, dest]
    simp only [List.length_nil, Nat.sub_zero]
    split
    · rfl
    · rw [fixClock_evaluate]
      cases run : evaluate [body] ((first :: rest) ++ env) (decClock (first :: rest).length s) with
      | mk result next =>
        cases result with
        | err error => rfl
        | val values =>
          obtain ⟨v, rfl⟩ := evaluate_singleton_value body ((first :: rest) ++ env)
            (decClock (first :: rest).length s) next values run
          simp [evaluateApp]

end Flapjack.Compiler.Backend.ClosKnown.Relations.AppExact
