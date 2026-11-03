import Flapjack.Compiler.Backend.ClosFvs.Proofs.Relations
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact

/-! Initial evaluator case for free-variable removal correctness. -/
namespace Flapjack.Compiler.Backend.ClosFvs
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Original result relation specialized to related lists and exceptions. -/
def ResultRel : Result (List Value) Value → Result (List Value) Value → Prop
  | .val left, .val right => List.Forall₂ ValueRel left right
  | .err (.raise left), .err (.raise right) => ValueRel left right
  | .err (.abort left), .err (.abort right) => left = right
  | _, _ => False

namespace EvaluatePort
/-- The closure state has the reviewed canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end EvaluatePort

/-- Empty expression lists preserve the original evaluation result and state. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "evaluate_remove_fvs"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_fvs_nil {C F : Type} (env nextEnv : List Value)
    (source : State C F) (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (target : State C F)
    (premises : evaluate [] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel env.length [] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, _, states, code⟩ := premises
  simp [evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  simp [CodeRel, removeList] at code
  subst targetCode
  exact ⟨.val [], target, by simp [evaluate], .nil, states⟩

/-- Related environments have related optional results at every index. -/
theorem environment_lookup (env nextEnv : List Value) (related : List.Forall₂ ValueRel env nextEnv)
    (index : Nat) : OptionRel ValueRel env[index]? nextEnv[index]? := by
  induction related generalizing index with
  | nil => simp [OptionRel]
  | cons head tail ih =>
    cases index with
    | zero => simpa [OptionRel] using head
    | succ index => simpa using ih index

/-- A source variable, including an out-of-scope one, is simulated by the
corresponding variable or generated type-error expression. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "evaluate_remove_fvs"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_fvs_var {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (env nextEnv : List Value) (source : State C F) (result : Result (List Value) Value)
    (sourceNext : State C F) (targetCode : List ClosLang.Exp) (target : State C F)
    (premises : evaluate [.var trace index] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel env.length [.var trace index] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have lookup := environment_lookup env nextEnv envRel index
  cases found : env[index]? with
  | none =>
    have outside := List.getElem?_eq_none_iff.mp found
    simp [evaluate, found] at run
    obtain ⟨rfl, rfl⟩ := run
    have codeEq : targetCode = [.op trace (.memOp .el) []] := by
      simpa [CodeRel, removeList, removeSing, Nat.not_lt.mpr outside] using code
    refine ⟨.err (.abort .typeError), target, ?_, rfl, states⟩
    rw [codeEq]
    simp [evaluate, doApp, applyMemory, fixClock]
  | some value =>
    have inside : index < env.length := by
      by_contra h
      have missing : env[index]? = none := List.getElem?_eq_none (Nat.le_of_not_gt h)
      simp [missing] at found
    cases nextFound : nextEnv[index]? with
    | none => simp [found, nextFound, OptionRel] at lookup
    | some nextValue =>
      have values : ValueRel value nextValue := by simpa [found, nextFound, OptionRel] using lookup
      simp [evaluate, found] at run
      obtain ⟨rfl, rfl⟩ := run
      have codeEq : targetCode = [.var trace index] := by
        simpa [CodeRel, removeList, removeSing, inside] using code
      refine ⟨.val [nextValue], target, ?_, .cons values .nil, states⟩
      rw [codeEq]
      simp [evaluate, nextFound]

end Flapjack.Compiler.Backend.ClosFvs
