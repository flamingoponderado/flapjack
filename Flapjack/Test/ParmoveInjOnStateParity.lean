import Flapjack.Compiler.Backend.Parmove.InjOnState

namespace Flapjack.Test.ParmoveInjOnStateParity
open Compiler.Backend.Parmove

/-! Kernel checks for the literal predicate captured as
`pm_audit_inj_on_state_def` in `parmove_preservation_shape_probe.out`.
These distinguish support-restricted injectivity from global injectivity and
exercise the global NONE equivalence independently of state membership. -/

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

-- A map may collapse values outside the state support, even across carriers.
example : injOnState collapse ([(some false, some false)], [], []) := by
  simp [injOnState, stateToList, forallOptionBool, collapse]

example : ¬ injOnState collapse ([(some false, some true)], [], []) := by
  simp [injOnState, stateToList, forallOptionBool, collapse]

-- The active and emitted segments contribute endpoints as well as pending.
example : ¬ injOnState collapse ([], [(some false, some true)], []) := by
  simp [injOnState, stateToList, forallOptionBool, collapse]

example : ¬ injOnState collapse ([], [], [(some false, some true)]) := by
  simp [injOnState, stateToList, forallOptionBool, collapse]

-- The NONE clause is global even for an empty state.
example : ¬ injOnState (fun _ : Option Bool => (none : Option Unit)) ([], [], []) := by
  simp [injOnState, stateToList, forallOptionBool]

example : ¬ injOnState (fun _ : Option Bool => (some () : Option Unit)) ([], [], []) := by
  simp [injOnState, stateToList]

-- Arbitrary payloads, including functions, need no equality decision procedure.
example {α : Type} (state : State α) : injOnState id state := by
  simp [injOnState]

example (state : State (Nat → Nat)) : injOnState id state := by
  simp [injOnState]

-- Full defining equation with both independent carriers and no extra premise.
example {α β : Type} (f : Option α → Option β) (state : State α) :
    injOnState f state ↔
      ((∀ x y, x ∈ (stateToList state).map Prod.fst ++ (stateToList state).map Prod.snd ∧
          y ∈ (stateToList state).map Prod.fst ++ (stateToList state).map Prod.snd ∧
          f x = f y → x = y) ∧ (∀ x, f x = none ↔ x = none)) := Iff.rfl

end Flapjack.Test.ParmoveInjOnStateParity
