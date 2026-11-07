import Flapjack.Misc.ListEl

/-! Indexed environment lookup from CakeML's general-purpose list utilities. -/
namespace Flapjack.Compiler.Backend.ClosSem

/-- Gather selected environment values in order, rejecting an invalid index. -/
@[hol "cakeml/misc/miscScript.sml" "lookup_vars_def"]
def lookupVars {α : Type} : List Nat → List α → Option (List α)
  | [], _ => some []
  | index :: indices, env => do
    let value ← env[index]?
    let values ← lookupVars indices env
    some (value :: values)

/-- Optional indexing gives the original bound-and-`EL` source equation. -/
theorem lookupVars_cons_source {α : Type} [Nonempty α] (index : Nat)
    (indices : List Nat) (env : List α) :
    lookupVars (index :: indices) env =
      if index < env.length then
        (lookupVars indices env).map (fun values => Flapjack.holEl index env :: values)
      else none := by
  by_cases bound : index < env.length
  · simp [lookupVars, bound, Flapjack.holEl_eq_getElem index env bound]
    cases lookupVars indices env <;> rfl
  · simp [lookupVars, bound]

end Flapjack.Compiler.Backend.ClosSem
