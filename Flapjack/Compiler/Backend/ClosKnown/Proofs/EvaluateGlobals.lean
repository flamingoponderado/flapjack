import Flapjack.Compiler.Backend.ClosKnown.Proofs.InstallGlobals
import Flapjack.Compiler.Backend.ClosKnown.Proofs.ClosureGlobals
import Flapjack.Compiler.Backend.ClosKnown.Proofs.PrimitiveGlobals
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact

/-! Global-write safety during closure evaluation. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosSem ClosProps ClosProps.StateGlobalSafety
open Flapjack.SemanticPrimitivesHOL
open FlatProps (emptyGlobalBag)

namespace EvaluateGlobalsPort
/-- The closure evaluator uses the canonical finite-map state representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Empty expression evaluation preserves the source global invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsNil {C F : Type} (env : List ClosSem.Value)
    (s0 : ClosSem.State C F) (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([] : List ClosLang.Exp), esgcFree e) ∧ (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  rcases h with ⟨run, safe, _, _⟩
  simp [evaluate] at run
  rcases run with ⟨rfl, rfl⟩
  exact ⟨safe, by simp [rsgcFree], 0, shiftSeqZero _, mglobalsExtendRefl _ _⟩

/-- Applying a safe closure to no arguments preserves the source invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAppChangedGlobalsNil {C F : Type} (location : Option Nat) (f : ClosSem.Value)
    (s0 : ClosSem.State C F) (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluateApp location f [] s0 = (res, s) ∧ ssgcFree s0 ∧ vsgcFree f ∧
      (∀ v ∈ ([] : List ClosSem.Value), vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0} s.globals := by
  rcases h with ⟨run, safe, fnSafe, _⟩
  simp [evaluateApp] at run
  rcases run with ⟨rfl, rfl⟩
  exact ⟨safe, by simpa [rsgcFree] using fnSafe, 0, shiftSeqZero _, mglobalsExtendRefl _ _⟩


/-- Variable evaluation preserves the source global invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_changed_globals_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateChangedGlobalsVar {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (env : List ClosSem.Value) (s0 : ClosSem.State C F)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate [.var trace index] env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ e ∈ ([.var trace index] : List ClosLang.Exp), esgcFree e) ∧
      (∀ v ∈ env, vsgcFree v)) :
    ssgcFree s ∧ rsgcFree res ∧ ∃ n,
      s.compileOracle = Flapjack.holShiftSeq n s0.compileOracle ∧
      mglobalsExtend s0.globals
        ({k | elistGlobals [.var trace index] k ≠ 0} ∪
         {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) s.globals := by
  rcases h with ⟨run, safe, _, envSafe⟩
  cases found : env[index]? with
  | none =>
    simp [evaluate, found] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨safe, by simp [rsgcFree], 0, shiftSeqZero _, mglobalsExtendRefl _ _⟩
  | some value =>
    have valueSafe := envSafe value (List.mem_of_getElem? found)
    simp [evaluate, found] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨safe, by simpa [rsgcFree] using valueSafe, 0, shiftSeqZero _, mglobalsExtendRefl _ _⟩

end EvaluateGlobalsPort
end Flapjack.Compiler.Backend.ClosKnown
