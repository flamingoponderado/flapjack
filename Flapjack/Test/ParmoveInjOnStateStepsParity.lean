import Flapjack.Compiler.Backend.Parmove.InjOnState.Steps

namespace Flapjack.Test.ParmoveInjOnStateStepsParity
open Compiler.Backend.Parmove

/-! Kernel checks for the literal HOL theorem `steps_inj_on_state`
(`parmoveScript.sml:1115`): injectivity on the endpoint state survives any
number of primitive move steps. -/

private def collapse : Option Bool → Option Unit
  | none => none
  | some _ => some ()

private theorem forallOptionBool (p : Option Bool → Prop) :
    (∀ x, p x) ↔ p none ∧ p (some false) ∧ p (some true) := by
  constructor
  · intro h
    exact ⟨h none, h (some false), h (some true)⟩
  · rintro ⟨hn, hf, ht⟩ x
    cases x with
    | none => exact hn
    | some b => cases b <;> assumption

-- A genuine one-step transition (`removeSelf`) preserves injectivity.
example : injOnState collapse (([], [], []) : State Bool) :=
  stepsInjOnState collapse _ _
    ⟨by simp [injOnState, stateToList, forallOptionBool, collapse],
     Relation.ReflTransGen.tail Relation.ReflTransGen.refl
       (Step.removeSelf (some false) ([] : List (Move Bool)) [] [] [])⟩

-- The reflexive closure is the identity case.
example {α β : Type} (f : Option α → Option β) (state : State α)
    (h : injOnState f state) : injOnState f state :=
  stepsInjOnState f state state ⟨h, Relation.ReflTransGen.refl⟩

def runChecks : IO Bool := do
  IO.println "PASS parmove steps_inj_on_state preserves injectivity (reflexive and one-step)"
  pure true
end Flapjack.Test.ParmoveInjOnStateStepsParity
