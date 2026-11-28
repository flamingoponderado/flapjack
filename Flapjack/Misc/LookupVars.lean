module

public import Flapjack.Misc.ListEl

@[expose] public section

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

/-- Original `EVERY_lookup_vars`: gathering environment values preserves any
property that already holds of every environment entry. HOL's `EVERY P env`
is the quantified membership form and `P` stays `Bool`-valued, so it is
stated as `P x = true`. -/
@[hol "cakeml/misc/miscScript.sml" "EVERY_lookup_vars"]
theorem every_lookupVars {α : Type} :
    ∀ (vs : List Nat) (env env' : List α) (P : α → Bool),
      (∀ x ∈ env, P x = true) ∧ lookupVars vs env = some env' → ∀ x ∈ env', P x = true := by
  intro vs
  induction vs with
  | nil =>
    intro env env' P h x hx
    obtain ⟨_, h'⟩ := h
    simp only [lookupVars, Option.some.injEq] at h'
    subst h'
    simp at hx
  | cons index indices ih =>
    intro env env' P h x hx
    obtain ⟨hall, h'⟩ := h
    simp only [lookupVars] at h'
    obtain ⟨value, hvalue, hinner⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨values, hvalues, hval⟩ := Option.bind_eq_some_iff.mp hinner
    simp only [Option.some.injEq] at hval
    rw [← hval] at hx
    rcases List.mem_cons.mp hx with hxv | hxs
    · rw [hxv]
      exact hall value (List.mem_iff_getElem?.mpr ⟨index, hvalue⟩)
    · exact ih env values P ⟨hall, hvalues⟩ x hxs

end Flapjack.Compiler.Backend.ClosSem
