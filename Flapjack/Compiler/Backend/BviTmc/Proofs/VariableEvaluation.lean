import Flapjack.Compiler.Backend.BviTmc
import Flapjack.Compiler.Backend.BviTailrec.Proofs.PrimitiveRelation

/-! Variable-list evaluation for the TMC expression simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc
open BvlSem BviSem

theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness

private theorem evaluateVars {C F : Type} (indices : List Nat) (env : List Value)
    (state : BviState C F) (bounds : wfVars env.length indices) :
    evaluate (indices.map Bvi.Exp.var) env state = (.val (indices.map fun n => holEl n env), state) := by
  have run := BviTailrec.evaluate_var_indices indices env state bounds
  have results : indices.map (fun n => (env[n]?).getD unitValue) = indices.map (fun n => holEl n env) := by
    apply List.map_congr_left
    intro n member
    have bound := bounds n member
    rw [holEl_eq_getElem n env bound]
    simp [bound]
  rw [results] at run
  exact run

/-- Well-formed source variable lists evaluate to their environment entries. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_vars_source"
  (fmap_as_finite_support := [refs])]
theorem evaluate_vars_source {C F : Type} (indices : List Nat) (env : List Value)
    (state : BviState (Nat × C) F) (wellFormed : wfVars env.length indices) :
    evaluate (indices.map Bvi.Exp.var) env state = (.val (indices.map fun n => holEl n env), state) :=
  evaluateVars indices env state wellFormed

/-- A larger target environment also evaluates well-formed variable lists. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_vars_target"
  (fmap_as_finite_support := [refs])]
theorem evaluate_vars_target {C F : Type} (indices : List Nat) (n : Nat) (env : List Value)
    (state : BviState C F) (wellFormed : wfVars n indices) (length : n ≤ env.length) :
    evaluate (indices.map Bvi.Exp.var) env state = (.val (indices.map fun k => holEl k env), state) :=
  evaluateVars indices env state (wfVars_expand n env.length indices wellFormed length)

private theorem evaluateVars_failure {C F : Type} (indices : List Nat) (env : List Value)
    (state : BviState C F) (invalid : ¬wfVars env.length indices) :
    evaluate (indices.map Bvi.Exp.var) env state = (.err (.abort .typeError), state) := by
  induction indices with
  | nil => exact (invalid (wfVars_empty env.length)).elim
  | cons n rest ih =>
    by_cases bound : n < env.length
    · have restInvalid : ¬wfVars env.length rest := by
        intro wellFormed
        apply invalid
        intro index member
        rcases List.mem_cons.mp member with rfl | member
        · exact bound
        · exact wellFormed index member
      have head : evaluate [.var n] env state = (.val [env[n]], state) := by
        simp [BviSem.evaluate, bound]
      change evaluateTuple (.var n :: rest.map Bvi.Exp.var, env, state) = _
      rw [evaluateCons]
      simp [BviSem.evaluateTuple, head, ih restInvalid]
    · have head : evaluate [.var n] env state = (.err (.abort .typeError), state) := by
        simp [BviSem.evaluate, bound]
      change evaluateTuple (.var n :: rest.map Bvi.Exp.var, env, state) = _
      rw [evaluateCons]
      simp [BviSem.evaluateTuple, head]

/-- A variable-list evaluation that avoids a type error returns exactly its
environment entries without changing the state. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_var_list"
  (fmap_as_finite_support := [refs])]
theorem evaluate_var_list {C F : Type} (indices : List Nat) (env : List Value)
    (state next : BviState C F) (result : BviResult)
    (run : evaluate (indices.map Bvi.Exp.var) env state = (result, next))
    (notError : result ≠ .err (.abort .typeError)) :
    (result, next) = (.val (indices.map fun n => holEl n env), state) := by
  by_cases wellFormed : wfVars env.length indices
  · exact run.symm.trans (evaluateVars indices env state wellFormed)
  · have failure := evaluateVars_failure indices env state wellFormed
    rw [run] at failure
    exact (notError (congrArg Prod.fst failure)).elim

/-- Appending extra environment values preserves a successful variable-list evaluation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_vars_expand_env"
  (fmap_as_finite_support := [refs])]
theorem evaluate_vars_expand_env {C F : Type} (indices : List Nat) (env : List Value)
    (state : BviState C F) (values extras : List Value)
    (run : evaluate (indices.map Bvi.Exp.var) env state = (.val values, state)) :
    evaluate (indices.map Bvi.Exp.var) (env ++ extras) state = (.val values, state) := by
  have wellFormed : wfVars env.length indices := by
    by_contra invalid
    have failure := evaluateVars_failure indices env state invalid
    rw [run] at failure
    simp at failure
  have extended : wfVars (env ++ extras).length indices :=
    wfVars_expand env.length (env ++ extras).length indices wellFormed (by simp)
  have sameValues : indices.map (fun n => holEl n (env ++ extras)) = indices.map (fun n => holEl n env) := by
    apply List.map_congr_left
    intro n member
    have bound := wellFormed n member
    have extendedBound : n < (env ++ extras).length := by simp; omega
    rw [holEl_eq_getElem n (env ++ extras) extendedBound, holEl_eq_getElem n env bound]
    simp [List.getElem_append_left, bound]
  have extendedRun := evaluateVars indices (env ++ extras) state extended
  rw [sameValues] at extendedRun
  exact extendedRun.trans ((evaluateVars indices env state wellFormed).symm.trans run)

/-- Shifting variable indices by a prefix length leaves their evaluation unchanged. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_shift_vars"
  (fmap_as_finite_support := [refs])]
theorem evaluate_shift_vars {C F : Type} (indices : List Nat) (env : List Value)
    (state : BviState C F) (prefixValues : List Value) :
    evaluate ((shiftVars prefixValues.length indices).map Bvi.Exp.var) (prefixValues ++ env) state =
      evaluate (indices.map Bvi.Exp.var) env state := by
  have shiftedIff : wfVars (prefixValues ++ env).length (shiftVars prefixValues.length indices) ↔
      wfVars env.length indices := by
    constructor
    · intro shifted index member
      have h := shifted (index + prefixValues.length) (List.mem_map.mpr ⟨index, member, rfl⟩)
      simp only [List.length_append] at h
      omega
    · intro original
      simpa [List.length_append] using wfVars_shift env.length prefixValues.length indices original
  by_cases wellFormed : wfVars env.length indices
  · have shifted := shiftedIff.mpr wellFormed
    rw [evaluateVars _ _ state shifted, evaluateVars _ _ state wellFormed]
    congr 1
    simp only [shiftVars, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro n member
    have bound := wellFormed n member
    have shiftedBound : n + prefixValues.length < (prefixValues ++ env).length := by simp; omega
    rw [holEl_eq_getElem _ _ shiftedBound, holEl_eq_getElem _ _ bound]
    simp [List.getElem_append_right]
  · rw [evaluateVars_failure _ _ state (fun shifted => wellFormed (shiftedIff.mp shifted)),
      evaluateVars_failure _ _ state wellFormed]

/-- The one-element prefix instance of variable shifting. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_shift_vars_sing"
  (fmap_as_finite_support := [refs])]
theorem evaluate_shift_vars_sing {C F : Type} (indices : List Nat) (env : List Value)
    (state : BviState C F) (value : Value) :
    evaluate ((shiftVars 1 indices).map Bvi.Exp.var) (value :: env) state =
      evaluate (indices.map Bvi.Exp.var) env state := by
  simpa using evaluate_shift_vars indices env state [value]

/-- Adding binders and shifting variable indices preserves a non-type-error run. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_var_list_binders"
  (fmap_as_finite_support := [refs])]
theorem evaluate_var_list_binders {C F : Type} (indices : List Nat) (extras env : List Value)
    (state : BviState C F) (result : BviResult) (next : BviState C F)
    (run : evaluate (indices.map Bvi.Exp.var) env state = (result, next))
    (_notError : result ≠ .err (.abort .typeError)) :
    evaluate (indices.map fun n => Bvi.Exp.var (n + extras.length)) (extras ++ env) state = (result, next) := by
  simpa [shiftVars, List.map_map, Function.comp_def] using
    (evaluate_shift_vars indices env state extras).trans run

end Flapjack.Compiler.Backend.BviTmc
