import Flapjack.Compiler.Backend.BviTmc
import Flapjack.Compiler.Backend.BviTmc.Proofs.ExtractCorrespondence
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

private theorem evaluateBindings {C F : Type} (args : List Bvi.Exp) (values : List Value)
    (count : values.length = args.length) (n : Nat) (ys : List Value)
    (prefixLength : ys.length = n) (state : BviState C F) :
    evaluate ((bind n args).1.map Bvi.Exp.var) (ys ++ values) state = (.val values, state) := by
  induction args generalizing values n ys with
  | nil =>
    cases values <;> simp_all [bind, BviSem.evaluate]
  | cons arg args ih =>
    cases values with
    | nil => simp at count
    | cons value values =>
      have count' : values.length = args.length := by simpa using count
      cases binding : bind (n + 1) args with
      | mk indices last =>
        have tail := ih values count' (n + 1) (ys ++ [value]) (by simp [prefixLength])
        simp only [binding] at tail
        simp only [bind, binding, List.map_cons]
        change evaluateTuple (.var n :: indices.map Bvi.Exp.var, ys ++ value :: values, state) = _
        rw [evaluateCons]
        have head : evaluateTuple ([.var n], ys ++ value :: values, state) = (.val [value], state) := by
          simp [BviSem.evaluateTuple, BviSem.evaluate, ← prefixLength]
        rw [head]
        simp only [BviSem.evaluateTuple, Flapjack.holHd]
        rw [show evaluate (indices.map Bvi.Exp.var) (ys ++ value :: values) state =
          (.val values, state) by simpa [List.append_assoc] using tail]

/-- The bindings generated for successful arguments retrieve their values. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_binders"
  (fmap_as_finite_support := [refs])]
theorem evaluate_binders {C F : Type} (args : List Bvi.Exp) (env : List Value)
    (state nextState : BviState C F) (values : List Value) (next next' : Nat)
    (indices : List Nat)
    (run : evaluate args env state = (.val values, nextState))
    (binding : bind next args = (indices, next')) (ys : List Value)
    (prefixLength : ys.length = next) :
    evaluate (indices.map Bvi.Exp.var) (ys ++ values) nextState = (.val values, nextState) := by
  have count := BviSem.evaluate_length args env state nextState values run
  have result := evaluateBindings args values count next ys prefixLength nextState
  simpa [binding] using result

/-- Reconstruct a BVI expression from a constructor call skeleton. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "cb_to_bvi_def"]
def callBlockToBvi (loc : Nat) : CallBlock → Bvi.Exp
  | .rCall ticks args => .call ticks (some loc) (args.map Bvi.Exp.var) none
  | .callBlock tag left child right =>
      .op (.blockOp (.cons tag))
        (left.map Bvi.Exp.var ++ [callBlockToBvi loc child] ++ right.map Bvi.Exp.var)

/-- Shifting a call skeleton preserves its evaluation under a prefixed environment. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_shift_cb"
  (fmap_as_finite_support := [refs])]
theorem evaluate_shift_cb {C F : Type} (cb : CallBlock) (loc : Nat) (env : List Value)
    (state : BviState C F) (bs : List Value) :
    evaluate [callBlockToBvi loc (shiftBlock bs.length cb)] (bs ++ env) state =
      evaluate [callBlockToBvi loc cb] env state := by
  induction cb generalizing state with
  | rCall ticks args =>
    simp only [shiftBlock, callBlockToBvi, BviSem.evaluate]
    rw [evaluate_shift_vars]
  | callBlock tag left child right ih =>
    have argsEqual : evaluateTuple (((shiftVars bs.length left).map Bvi.Exp.var) ++
        [callBlockToBvi loc (shiftBlock bs.length child)] ++
        (shiftVars bs.length right).map Bvi.Exp.var, bs ++ env, state) =
        evaluateTuple (left.map Bvi.Exp.var ++ [callBlockToBvi loc child] ++
        right.map Bvi.Exp.var, env, state) := by
      simp only [List.append_assoc]
      conv_lhs => rw [evaluateAppend]
      conv_rhs => rw [evaluateAppend]
      simp only [BviSem.evaluateTuple, evaluate_shift_vars]
      cases h : evaluate (left.map Bvi.Exp.var) env state with
      | mk result next =>
        cases result with
        | err error => rfl
        | val values =>
          simp only
          have tailEqual : evaluateTuple ([callBlockToBvi loc (shiftBlock bs.length child)] ++
              (shiftVars bs.length right).map Bvi.Exp.var, bs ++ env, next) =
              evaluateTuple ([callBlockToBvi loc child] ++ right.map Bvi.Exp.var, env, next) := by
            conv_lhs => rw [evaluateAppend]
            conv_rhs => rw [evaluateAppend]
            simp only [BviSem.evaluateTuple, ih, evaluate_shift_vars]
          change evaluate ([callBlockToBvi loc (shiftBlock bs.length child)] ++
            (shiftVars bs.length right).map Bvi.Exp.var) (bs ++ env) next =
            evaluate ([callBlockToBvi loc child] ++ right.map Bvi.Exp.var) env next at tailEqual
          rw [tailEqual]
    simp only [shiftBlock, callBlockToBvi, BviSem.evaluate]
    rw [show evaluate _ _ state = evaluate _ env state from argsEqual]

/-- The single-value environment-prefix instance for a call skeleton. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_shift_cb_sing"
  (fmap_as_finite_support := [refs])]
theorem evaluate_shift_cb_sing {C F : Type} (cb : CallBlock) (loc : Nat) (env : List Value)
    (state : BviState C F) (b : Value) :
    evaluate [callBlockToBvi loc (shiftBlock 1 cb)] (b :: env) state =
      evaluate [callBlockToBvi loc cb] env state := by
  simpa using evaluate_shift_cb cb loc env state [b]

/-- Flapjack infrastructure: evaluating the arguments of a shifted constructor
frame gives the original argument result, including errors and state changes. -/
theorem evaluate_shift_frame_args {C F : Type} (loc : Nat) (left right : List Nat)
    (child : CallBlock) (env : List Value) (state : BviState C F) (prefixValues : List Value) :
    evaluate ((shiftVars prefixValues.length left).map Bvi.Exp.var ++
      [callBlockToBvi loc (shiftBlock prefixValues.length child)] ++
      (shiftVars prefixValues.length right).map Bvi.Exp.var) (prefixValues ++ env) state =
    evaluate (left.map Bvi.Exp.var ++ [callBlockToBvi loc child] ++ right.map Bvi.Exp.var) env state := by
  change evaluateTuple (_, prefixValues ++ env, state) = evaluateTuple (_, env, state)
  simp only [List.append_assoc]
  conv_lhs => rw [evaluateAppend]
  conv_rhs => rw [evaluateAppend]
  simp only [BviSem.evaluateTuple, evaluate_shift_vars]
  cases h : evaluate (left.map Bvi.Exp.var) env state with
  | mk result next =>
    cases result with
    | err error => rfl
    | val values =>
      have tailEqual : evaluateTuple ([callBlockToBvi loc (shiftBlock prefixValues.length child)] ++
          (shiftVars prefixValues.length right).map Bvi.Exp.var, prefixValues ++ env, next) =
          evaluateTuple ([callBlockToBvi loc child] ++ right.map Bvi.Exp.var, env, next) := by
        conv_lhs => rw [evaluateAppend]
        conv_rhs => rw [evaluateAppend]
        simp only [BviSem.evaluateTuple, evaluate_shift_cb, evaluate_shift_vars]
      change evaluate ([callBlockToBvi loc (shiftBlock prefixValues.length child)] ++
        (shiftVars prefixValues.length right).map Bvi.Exp.var) (prefixValues ++ env) next =
        evaluate ([callBlockToBvi loc child] ++ right.map Bvi.Exp.var) env next at tailEqual
      dsimp only
      rw [tailEqual]

/-- Flapjack infrastructure for the list simulation: a leading binding is
added to the reconstructed block after the original frame arguments run. -/
theorem evaluate_prefixed_frame {C F : Type} (loc tag : Nat) (left right : List Nat)
    (child : CallBlock) (value : Value) (env : List Value) (state : BviState C F) :
    evaluate [callBlockToBvi loc (.callBlock tag (0 :: shiftVars 1 left)
      (shiftBlock 1 child) (shiftVars 1 right))] (value :: env) state =
      match evaluate (left.map Bvi.Exp.var ++ [callBlockToBvi loc child] ++ right.map Bvi.Exp.var) env state with
      | (.err error, next) => (.err error, next)
      | (.val values, next) => (.val [.block tag (values.reverse ++ [value])], next) := by
  have argsRun : evaluate (.var 0 :: ((shiftVars 1 left).map Bvi.Exp.var ++
      [callBlockToBvi loc (shiftBlock 1 child)] ++ (shiftVars 1 right).map Bvi.Exp.var)) (value :: env) state =
      match evaluate (left.map Bvi.Exp.var ++ [callBlockToBvi loc child] ++ right.map Bvi.Exp.var) env state with
      | (.err error, next) => (.err error, next)
      | (.val values, next) => (.val (value :: values), next) := by
    change evaluateTuple (_, value :: env, state) = _
    rw [evaluateCons]
    simp only [BviSem.evaluateTuple]
    have head : evaluate [.var 0] (value :: env) state = (.val [value], state) := by simp [BviSem.evaluate]
    rw [head]
    dsimp only
    have tail := evaluate_shift_frame_args loc left right child env state [value]
    simp only [List.length_singleton, List.singleton_append] at tail
    rw [tail]
    cases evaluate (left.map Bvi.Exp.var ++ [callBlockToBvi loc child] ++ right.map Bvi.Exp.var) env state with
    | mk result next => cases result <;> rfl
  simp only [callBlockToBvi, List.map_cons, List.cons_append]
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
  cases evaluate (left.map Bvi.Exp.var ++ [callBlockToBvi loc child] ++ right.map Bvi.Exp.var) env state with
  | mk result next =>
    cases result with
    | err error => rfl
    | val values => simp [BviTailrec.doApp_blockCons]

/-- Flapjack infrastructure: a successful reconstructed frame remains a
constructor when a preceding argument is inserted. -/
theorem evaluate_prefixed_frame_success {C F : Type} (loc tag : Nat) (left right : List Nat)
    (child : CallBlock) (value : Value) (env : List Value) (state next : BviState C F)
    (result : Value) (run : evaluate [callBlockToBvi loc (.callBlock tag left child right)] env state =
      (.val [result], next)) :
    ∃ fields, result = .block tag fields ∧
      evaluate [callBlockToBvi loc (.callBlock tag (0 :: shiftVars 1 left)
        (shiftBlock 1 child) (shiftVars 1 right))] (value :: env) state =
        (.val [.block tag (fields ++ [value])], next) := by
  rw [callBlockToBvi, BviSem.evaluate, BviSem.fixClock_evaluate] at run
  rw [evaluate_prefixed_frame]
  cases argsRun : evaluate (left.map Bvi.Exp.var ++ [callBlockToBvi loc child] ++
      right.map Bvi.Exp.var) env state with
  | mk argsResult argsState =>
    simp only [List.append_assoc, List.singleton_append] at argsRun
    cases argsResult with
    | err error => simp [argsRun] at run
    | val values =>
      simp [argsRun, BviTailrec.doApp_blockCons] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨values.reverse, rfl, rfl⟩

/-- Flapjack infrastructure: adding a preceding binding preserves errors
produced by a reconstructed frame. -/
theorem evaluate_prefixed_frame_error {C F : Type} (loc tag : Nat) (left right : List Nat)
    (child : CallBlock) (value : Value) (env : List Value) (state next : BviState C F)
    (error : SemanticPrimitivesHOL.ErrorResult ExnOrRet)
    (run : evaluate [callBlockToBvi loc (.callBlock tag left child right)] env state = (.err error, next)) :
    evaluate [callBlockToBvi loc (.callBlock tag (0 :: shiftVars 1 left)
      (shiftBlock 1 child) (shiftVars 1 right))] (value :: env) state = (.err error, next) := by
  rw [callBlockToBvi, BviSem.evaluate, BviSem.fixClock_evaluate] at run
  rw [evaluate_prefixed_frame]
  cases argsRun : evaluate (left.map Bvi.Exp.var ++ [callBlockToBvi loc child] ++
      right.map Bvi.Exp.var) env state with
  | mk argsResult argsState =>
    simp only [List.append_assoc, List.singleton_append] at argsRun
    cases argsResult with
    | err argsError => simpa [argsRun] using run
    | val values => simp [argsRun, BviTailrec.doApp_blockCons] at run

end Flapjack.Compiler.Backend.BviTmc
