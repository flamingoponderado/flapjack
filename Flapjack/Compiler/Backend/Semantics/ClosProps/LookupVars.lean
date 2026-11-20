module

public import Flapjack.Misc.LookupVars
public import Flapjack.Misc.ListEl
public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.Semantics.ClosSem

@[expose] public section

/-! Indexed environment lookup properties from the original `closProps`
script. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosSem

/-- Indexed lookup fails exactly when some index is out of range. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "lookup_vars_NONE"]
theorem lookupVars_none {α : Type} (vs : List Nat) (env : List α) :
    lookupVars vs env = none ↔ ∃ v ∈ vs, env.length ≤ v := by
  induction vs with
  | nil => simp [lookupVars]
  | cons v vs ih =>
    cases lookup : env[v]? with
    | none =>
      have bound : env.length ≤ v := List.getElem?_eq_none_iff.mp lookup
      simp [lookupVars, bound]
    | some value =>
      have notBound : ¬ env.length ≤ v := by
        intro h
        rw [List.getElem?_eq_none_iff.mpr h] at lookup
        cases lookup
      cases valuesRun : lookupVars vs env with
      | none =>
        simp [lookupVars, lookup, valuesRun, notBound]
        exact ih.mp valuesRun
      | some values =>
        have noFail : ¬ ∃ a, a ∈ vs ∧ env.length ≤ a := by
          rw [← ih, valuesRun]
          simp
        simp [lookupVars, lookup, valuesRun, notBound]
        intro x hx
        have hnot : ¬ env.length ≤ x := by
          intro hle
          exact noFail ⟨x, hx, hle⟩
        omega

/-- A successful indexed lookup returns as many values as indices. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "lookup_vars_SOME"]
theorem lookupVars_some_length {α : Type} (vs : List Nat) (env xs : List α)
    (run : lookupVars vs env = some xs) : vs.length = xs.length := by
  induction vs generalizing xs with
  | nil =>
    simp [lookupVars] at run
    subst run
    simp
  | cons v vs ih =>
    cases lookup : env[v]? with
    | none =>
      simp [lookupVars, lookup] at run
    | some value =>
      cases valuesRun : lookupVars vs env with
      | none =>
        simp [lookupVars, lookup, valuesRun] at run
      | some values =>
        simp [lookupVars, lookup, valuesRun] at run
        subst run
        simp [ih values valuesRun]

/-- The source value type is inhabited, so HOL's unspecified `EL` past the
end of a list has a Lean instance to draw on. -/
local instance lookupVarsValueInhabited : Nonempty Value := ⟨Value.number 0⟩

/-- A successful indexed lookup returns the selected entries in order. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "lookup_vars_MEM"]
theorem lookupVars_mem (ys : List Nat) (env2 x : List Value) (n : Nat)
    (h : lookupVars ys env2 = some x ∧ n < ys.length) :
    Flapjack.holEl n ys < env2.length ∧
      Flapjack.holEl n x = Flapjack.holEl (Flapjack.holEl n ys) env2 := by
  induction ys generalizing x n with
  | nil =>
    obtain ⟨_, lt⟩ := h
    simp at lt
  | cons v vs ih =>
    obtain ⟨run, lt⟩ := h
    simp only [List.length_cons] at lt
    cases lookup : env2[v]? with
    | none => simp [lookupVars, lookup] at run
    | some value =>
      cases valuesRun : lookupVars vs env2 with
      | none => simp [lookupVars, lookup, valuesRun] at run
      | some values =>
        simp [lookupVars, lookup, valuesRun] at run
        subst run
        obtain ⟨bound, entryEq⟩ := List.getElem?_eq_some_iff.mp lookup
        cases n with
        | zero =>
          simp only [Flapjack.holEl, Flapjack.holHd]
          constructor
          · exact bound
          · rw [Flapjack.holEl_eq_getElem v env2 bound]
            exact entryEq.symm
        | succ n =>
          simp only [Flapjack.holEl, List.tail_cons]
          exact ih values n ⟨valuesRun, by omega⟩

end Flapjack.Compiler.Backend.ClosProps
