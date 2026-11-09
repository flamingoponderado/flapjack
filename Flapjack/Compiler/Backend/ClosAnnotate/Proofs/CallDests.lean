import Flapjack.Compiler.Backend.ClosAnnotate.Shift.OriginalEquivalence
import Flapjack.Compiler.Backend.Semantics.ClosProps.AppCallDests

/-! Closure shifting preserves the original call-destination sets. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang ClosProps

private theorem dests_cons (opt : Option Bool) (x : Exp) (xs : List Exp) :
    appCallDests opt (x :: xs) = appCallDests opt [x] ∪ appCallDests opt xs := by
  cases xs <;> simp [appCallDests]

private theorem dests_map_congr {α : Type} (opt : Option Bool) (xs : List α) (f g : α → Exp)
    (h : ∀ x ∈ xs, appCallDests opt [f x] = appCallDests opt [g x]) :
    appCallDests opt (xs.map f) = appCallDests opt (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    rw [dests_cons opt (f x) (xs.map f), dests_cons opt (g x) (xs.map g)]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

private theorem dests_shiftHead (opt : Option Bool) (x : Exp) (m l : Nat) (i : Spt Nat) :
    appCallDests opt [@Flapjack.holHd Exp ⟨.var .none 0⟩ (shiftSource [x] m l i)] =
      appCallDests opt (shiftSource [x] m l i) := by
  rw [shiftSource_sing_eq.1]
  rfl

/-- Shifting preserves application and call destinations in every mode. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "call_dests_shift"]
theorem callDests_shift (opt : Option Bool) (expressions : List Exp) (m l : Nat) (i : Spt Nat) :
    appCallDests opt (shiftSource expressions m l i) = appCallDests opt expressions := by
  induction expressions, m, l, i using shiftSource.induct <;>
    simp_all [shiftSource, appCallDests, appCallDests_append, dests_shiftHead]
  case case9 =>
    rename_i t loc x xs m l i ihX ihXs
    cases opt <;> cases loc <;> simp_all [appCallDests, dests_shiftHead]
  case case10 =>
    rename_i name loc vs args x m l i k live ih
    dsimp [k, live] at ih
    exact ih
  case case11 =>
    rename_i names loc vs fs x m l i k live newI ihFuns ihBody
    dsimp [k, live, newI] at ihFuns
    simp only [List.map_attach_eq_pmap, List.pmap_eq_map, Function.comp_def]
    congr 1
    apply dests_map_congr
    intro entry member
    cases entry with
    | mk arity body => simpa [dests_shiftHead] using ihFuns arity body member
  case case13 =>
    split <;> simp_all

end Flapjack.Compiler.Backend.ClosAnnotate
