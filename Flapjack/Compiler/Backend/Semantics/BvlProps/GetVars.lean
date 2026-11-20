module

public import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList
public import Flapjack.Compiler.Backend.Semantics.BvlProps.VarBound
public import Flapjack.HolRef

@[expose] public section

/-! Environment lookup for BVL variable lists. -/
namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem

/-- Look up each variable index in order, failing if any index is out of range. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "get_vars_def"]
def getVars {α : Type} : List Nat → List α → Option (List α)
  | [], _ => some []
  | index :: rest, env =>
    match env[index]? with
    | none => none
    | some value => (getVars rest env).map (value :: ·)

namespace GetVarsCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end GetVarsCarrier

/-- Evaluating a list of variables either fails with a type error or yields
exactly the environment lookups. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_Var_list"
  (fmap_as_finite_support := [refs])]
theorem evaluateVar_list {C F : Type} (l : List Bvl.Exp) (env : List Value)
    (s : Flapjack.Compiler.Backend.BvlSem.State C F)
    (all : ∀ e ∈ l, isVar e = true) :
    evaluateTuple (l, env, s) = (.err (.abort .typeError), s) ∨
      ∃ vs, evaluateTuple (l, env, s) = (.val vs, s) ∧
        getVars (l.map destVar) env = some vs ∧ vs.length = l.length := by
  induction l with
  | nil =>
    right
    refine ⟨[], ?_, ?_, ?_⟩
    · simp [evaluateTuple, evaluate]
    · simp [getVars]
    · simp
  | cons x xs ih =>
    have hx : isVar x = true := all x (by simp)
    have allTail : ∀ e ∈ xs, isVar e = true := by
      intro e member
      exact all e (by simp [member])
    have hxvar : ∃ n, x = .var n := by
      cases x with
      | var n => exact ⟨n, rfl⟩
      | ifThenElse a b c => simp [isVar] at hx
      | «let» es body => simp [isVar] at hx
      | raise body => simp [isVar] at hx
      | handle a b => simp [isVar] at hx
      | tick body => simp [isVar] at hx
      | call t d es => simp [isVar] at hx
      | force loc v => simp [isVar] at hx
      | op o es => simp [isVar] at hx
    obtain ⟨n, rfl⟩ := hxvar
    cases found : env[n]? with
    | none =>
      left
      conv_lhs => rw [evaluateCons]
      simp [evaluateTuple, evaluate, found, typeError]
    | some v =>
      have varRun : evaluateTuple ([.var n], env, s) = (.val [v], s) := by
        simp [evaluateTuple, evaluate, found]
      rcases ih allTail with err | ⟨vs, tailRun, lookups, length⟩
      · left
        conv_lhs => rw [evaluateCons]
        simp only [varRun]
        simp [err]
      · right
        refine ⟨v :: vs, ?_, ?_, ?_⟩
        · conv_lhs => rw [evaluateCons]
          simp only [varRun]
          simp [tailRun, Flapjack.holHd]
        · simp [List.map_cons, destVar, getVars, found, lookups]
        · simp [length]

end Flapjack.Compiler.Backend.BvlProps
