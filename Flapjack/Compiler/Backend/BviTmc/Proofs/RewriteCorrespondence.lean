import Flapjack.Compiler.Backend.BviTmc.Proofs.ExtractCorrespondence
import Flapjack.Compiler.Backend.BviTmc.Proofs.Total

/-! Source-shaped TMC rewriting and correspondence with the executed pass. -/
namespace Flapjack.Compiler.Backend.BviTmc
open Bvi

/-- Construct a mutable block with one hole. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "mut_cons_def"]
def mutConsSource (tag : Nat) (left right : List Nat) : Exp :=
  .op (.memOp (.mutCons tag right.length))
    (left.map .var ++ [.op (.intOp (.const 0)) []] ++ right.map .var)

/-- Update a mutable block slot. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "update_cons_def"]
def updateConsSource (ptr idx value : Exp) : Exp := .op (.memOp .updateCons) [value, idx, ptr]

/-- Fill a worker's pending hole. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "fill_hole_def"]
def fillHoleSource (ptr idx : Nat) (e : Exp) : Exp := updateConsSource (.var ptr) (.var idx) e

/-- Invoke the worker with the pointer and hole index appended. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "optimise_call_def"]
def optimiseCallSource (ticks dest : Nat) (args : List Nat) (ptr idx : Exp) : Exp :=
  .call ticks (some dest) (args.map .var ++ [ptr, idx]) none

/-- Number of constructor levels in a call block. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "cb_size_def"]
def callBlockDepth : CallBlock → Nat
  | .rCall _ _ => 0
  | .callBlock _ _ child _ => callBlockDepth child + 1

private theorem callBlockDepth_shift (cb : CallBlock) (shift : Nat) :
    callBlockDepth (shiftBlock shift cb) = callBlockDepth cb := by
  induction cb with
  | rCall ticks args => rfl
  | callBlock tag left child right ih => simpa [shiftBlock, callBlockDepth] using ih

/-- Shifting by zero leaves a block unchanged. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "shift_cb_zero"]
theorem shiftBlock_zero (cb : CallBlock) : shiftBlock 0 cb = cb := by
  induction cb with
  | rCall ticks args =>
    change CallBlock.rCall ticks (args.map (· + 0)) = _
    simp
  | callBlock tag left child right ih =>
    change CallBlock.callBlock tag (left.map (· + 0)) (shiftBlock 0 child) (right.map (· + 0)) = _
    simp [ih]

/-- Successive variable shifts compose by addition. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "shift_cb_dist"]
theorem shiftBlock_add (cb : CallBlock) (first second : Nat) :
    shiftBlock first (shiftBlock second cb) = shiftBlock (first + second) cb := by
  induction cb with
  | rCall ticks args =>
    change CallBlock.rCall ticks ((args.map (· + second)).map (· + first)) =
      CallBlock.rCall ticks (args.map (· + (first + second)))
    simp [List.map_map, Function.comp_def, Nat.add_comm, Nat.add_left_comm]
  | callBlock tag left child right ih =>
    change CallBlock.callBlock tag ((left.map (· + second)).map (· + first))
      (shiftBlock first (shiftBlock second child)) ((right.map (· + second)).map (· + first)) =
      CallBlock.callBlock tag (left.map (· + (first + second)))
        (shiftBlock (first + second) child) (right.map (· + (first + second)))
    simp [ih, List.map_map, Function.comp_def, Nat.add_comm, Nat.add_left_comm]

/-- The original worker auxiliary recurses on a shifted child. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "cb_to_bvi_worker_aux_def"]
def workerAuxSource : CallBlock → Nat → Nat → Nat → Exp
  | .rCall ticks args, dest, ptr, idx =>
    optimiseCallSource ticks dest args (.var ptr) (.op (.intOp (.const (Int.ofNat idx))) [])
  | .callBlock tag left child right, dest, ptr, idx =>
    .let [mutConsSource tag left right]
      (.let [updateConsSource (.var (ptr + 1)) (.op (.intOp (.const (Int.ofNat idx))) []) (.var 0)]
        (workerAuxSource (shiftBlock 2 child) dest 1 right.length))
termination_by cb _ _ _ => callBlockDepth cb
decreasing_by simp [callBlockDepth, callBlockDepth_shift]

/-- The accumulator worker computes the original shifted-recursion result. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "cb_to_bvi_worker_aux_alt_thm"]
theorem workerAux_eq_shift (cb : CallBlock) (shift dest ptr idx : Nat) :
    workerAux shift cb dest ptr idx = workerAuxSource (shiftBlock shift cb) dest ptr idx := by
  induction cb generalizing shift dest ptr idx with
  | rCall ticks args =>
    rw [shiftBlock, workerAuxSource.eq_def]
    rfl
  | callBlock tag left child right ih =>
    rw [shiftBlock, workerAuxSource.eq_def]
    change Exp.let [mutConsSource tag (left.map (· + shift)) (right.map (· + shift))]
      (Exp.let [updateConsSource (.var (ptr + 1)) (.op (.intOp (.const (Int.ofNat idx))) []) (.var 0)]
        (workerAux (shift + 2) child dest 1 right.length)) =
      Exp.let [mutConsSource tag (left.map (· + shift)) (right.map (· + shift))]
        (Exp.let [updateConsSource (.var (ptr + 1)) (.op (.intOp (.const (Int.ofNat idx))) []) (.var 0)]
          (workerAuxSource (shiftBlock 2 (shiftBlock shift child)) dest 1 (right.map (· + shift)).length))
    simp only [List.length_map, shiftBlock_add]
    rw [Nat.add_comm 2 shift]
    rw [ih]

/-- The original worker-block construction. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "cb_to_bvi_worker_def"]
def workerBlockSource (cb : CallBlock) (dest ptr idx : Nat) : Exp :=
  match cb with
  | .rCall ticks args => optimiseCallSource ticks dest args (.var ptr) (.var idx)
  | .callBlock tag left child right =>
    .let [mutConsSource tag left right]
      (.let [updateConsSource (.var (ptr + 1)) (.var (idx + 1)) (.var 0)]
        (workerAuxSource (shiftBlock 2 child) dest 1 right.length))

/-- The source wrapper-block construction. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "cb_to_bvi_wrapper_def"]
def wrapperBlockSource (tag : Nat) (left : List Nat) (child : CallBlock) (right : List Nat) (dest : Nat) : Exp :=
  .let [mutConsSource tag left right]
    (.let [workerAuxSource (shiftBlock 1 child) dest 0 right.length] (.op (.memOp .finaliseCons) [.var 1]))

/-- Accumulator-based form of source worker-block construction. -/
def workerBlockAlt (cb : CallBlock) (dest ptr idx : Nat) : Exp :=
  match cb with
  | .rCall ticks args => optimiseCallSource ticks dest args (.var ptr) (.var idx)
  | .callBlock tag left child right =>
    .let [mutConsSource tag left right]
      (.let [updateConsSource (.var (ptr + 1)) (.var (idx + 1)) (.var 0)]
        (workerAux 2 child dest 1 right.length))

/-- Accumulator-based form of source wrapper-block construction. -/
def wrapperBlockAlt (tag : Nat) (left : List Nat) (child : CallBlock) (right : List Nat) (dest : Nat) : Exp :=
  .let [mutConsSource tag left right]
    (.let [workerAux 1 child dest 0 right.length] (.op (.memOp .finaliseCons) [.var 1]))

private theorem workerBlockAlt_eq_source (cb : CallBlock) (dest ptr idx : Nat) :
    workerBlockAlt cb dest ptr idx = workerBlockSource cb dest ptr idx := by
  cases cb <;> simp [workerBlockAlt, workerBlockSource, workerAux_eq_shift]

private theorem wrapperBlockAlt_eq_source (tag : Nat) (left : List Nat) (child : CallBlock)
    (right : List Nat) (dest : Nat) :
    wrapperBlockAlt tag left child right dest = wrapperBlockSource tag left child right dest := by
  simp [wrapperBlockAlt, wrapperBlockSource, workerAux_eq_shift]

/-- The source wrapper traversal. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "rewrite_wrapper_def"]
def rewriteWrapperSource (loc next n : Nat) : Exp → Option Exp
  | .ifThenElse cond yes no =>
    let y := rewriteWrapperSource loc next n yes
    let z := rewriteWrapperSource loc next n no
    match y, z with
    | none, none => none
    | _, _ => some (.ifThenElse cond (y.getD yes) (z.getD no))
  | .let xs body => (rewriteWrapperSource loc next (n + xs.length) body).map (.let xs)
  | .tick x => (rewriteWrapperSource loc next n x).map .tick
  | .op op xs =>
    match toBlockSource n loc (.op op xs) with
    | some (bs, .callBlock tag left child right) => some (.let bs (wrapperBlockSource tag left child right next))
    | _ => none
  | _ => none
termination_by e => sizeOf e

/-- The source worker traversal. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "rewrite_worker_def"]
def rewriteWorkerSource (loc next ptr idx n : Nat) : Exp → Exp
  | .ifThenElse cond yes no => .ifThenElse cond (rewriteWorkerSource loc next ptr idx n yes)
      (rewriteWorkerSource loc next ptr idx n no)
  | .let xs body => .let xs (rewriteWorkerSource loc next (ptr + xs.length) (idx + xs.length) (n + xs.length) body)
  | .raise x => .raise x
  | .tick x => .tick (rewriteWorkerSource loc next ptr idx n x)
  | e@(.op _ _) | e@(.call _ _ _ _) =>
    match toBlockSource n loc e with
    | some (bs, cb) => .let bs (workerBlockSource cb next (bs.length + ptr) (bs.length + idx))
    | none => fillHoleSource ptr idx e
  | e => fillHoleSource ptr idx e
termination_by e => sizeOf e

/-- Every successful bounded wrapper traversal agrees with its total
source-shaped form. -/
theorem rewriteWrapperFuel_success_eq (fuel loc next n : Nat) (e : Exp) (result : Option Exp)
    (run : rewriteWrapperFuel fuel loc next n e = some result) :
    result = rewriteWrapperSource loc next n e := by
  induction fuel generalizing n e result with
  | zero => simp [rewriteWrapperFuel] at run
  | succ fuel ih =>
    cases e with
    | ifThenElse cond yes no =>
      cases hy : rewriteWrapperFuel fuel loc next n yes with
      | none => simp [rewriteWrapperFuel, hy] at run
      | some y =>
        cases hz : rewriteWrapperFuel fuel loc next n no with
        | none => simp [rewriteWrapperFuel, hy, hz] at run
        | some z =>
          have ey := ih n yes y hy
          have ez := ih n no z hz
          simp only [rewriteWrapperFuel, hy, hz] at run
          rw [rewriteWrapperSource.eq_def]
          dsimp only
          rw [← ey, ← ez]
          clear ey ez hy hz
          cases y <;> cases z <;> simp_all
    | «let» xs body =>
      cases h : rewriteWrapperFuel fuel loc next (n + xs.length) body with
      | none => simp [rewriteWrapperFuel, h] at run
      | some value =>
        have equal := ih (n + xs.length) body value h
        cases value <;> simp_all [rewriteWrapperFuel, rewriteWrapperSource]
    | tick body =>
      cases h : rewriteWrapperFuel fuel loc next n body with
      | none => simp [rewriteWrapperFuel, h] at run
      | some value =>
        have equal := ih n body value h
        cases value <;> simp_all [rewriteWrapperFuel, rewriteWrapperSource]
    | op op xs =>
      simp only [rewriteWrapperFuel, toBlockFuel_eq_source] at run
      simp only [rewriteWrapperSource]
      cases h : toBlockSource n loc (.op op xs) with
      | none => simp [h] at run ⊢; exact run.symm
      | some value =>
        obtain ⟨bs, cb⟩ := value
        cases cb with
        | rCall ticks args => simp [h] at run ⊢; exact run.symm
        | callBlock tag left child right =>
          simp [h] at run ⊢
          rw [← wrapperBlockAlt_eq_source]
          exact run.symm
    | _ => simpa [rewriteWrapperFuel, rewriteWrapperSource] using (Option.some.inj run).symm

/-- Every successful bounded worker traversal agrees with its total
source-shaped form. -/
theorem rewriteWorkerFuel_success_eq (fuel loc next ptr idx n : Nat) (e result : Exp)
    (run : rewriteWorkerFuel fuel loc next ptr idx n e = some result) :
    result = rewriteWorkerSource loc next ptr idx n e := by
  induction fuel generalizing ptr idx n e result with
  | zero => simp [rewriteWorkerFuel] at run
  | succ fuel ih =>
    cases e with
    | ifThenElse cond yes no =>
      cases hy : rewriteWorkerFuel fuel loc next ptr idx n yes with
      | none => simp [rewriteWorkerFuel, hy] at run
      | some y =>
        cases hz : rewriteWorkerFuel fuel loc next ptr idx n no with
        | none => simp [rewriteWorkerFuel, hy, hz] at run
        | some z =>
          have ey := ih ptr idx n yes y hy
          have ez := ih ptr idx n no z hz
          simpa [rewriteWorkerFuel, rewriteWorkerSource, hy, hz, ey, ez] using run.symm
    | «let» xs body =>
      cases h : rewriteWorkerFuel fuel loc next (ptr + xs.length) (idx + xs.length) (n + xs.length) body with
      | none => simp [rewriteWorkerFuel, h] at run
      | some value =>
        have equal := ih (ptr + xs.length) (idx + xs.length) (n + xs.length) body value h
        simpa [rewriteWorkerFuel, rewriteWorkerSource, h, equal] using run.symm
    | tick body =>
      cases h : rewriteWorkerFuel fuel loc next ptr idx n body with
      | none => simp [rewriteWorkerFuel, h] at run
      | some value =>
        have equal := ih ptr idx n body value h
        simpa [rewriteWorkerFuel, rewriteWorkerSource, h, equal] using run.symm
    | op op xs =>
      simp only [rewriteWorkerFuel, toBlockFuel_eq_source] at run
      simp only [rewriteWorkerSource]
      cases h : toBlockSource n loc (.op op xs) with
      | none => simp [h] at run ⊢; exact run.symm
      | some value => obtain ⟨bs, cb⟩ := value; simp [h] at run ⊢; rw [← workerBlockAlt_eq_source]; exact run.symm
    | call ticks dest xs handler =>
      simp only [rewriteWorkerFuel, toBlockFuel_eq_source] at run
      simp only [rewriteWorkerSource]
      cases h : toBlockSource n loc (.call ticks dest xs handler) with
      | none => simp [h] at run ⊢; exact run.symm
      | some value => obtain ⟨bs, cb⟩ := value; simp [h] at run ⊢; rw [← workerBlockAlt_eq_source]; exact run.symm
    | _ =>
      simp only [rewriteWorkerFuel] at run
      simp only [rewriteWorkerSource]
      exact (Option.some.inj run).symm

/-- Function compilation using the total source-shaped traversals. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "compile_exp_def"]
def compileExpSource (loc next arity : Nat) (e : Exp) : Option (Exp × Exp) :=
  (rewriteWrapperSource loc next arity e).map fun wrapper =>
    (wrapper, rewriteWorkerSource loc next arity (arity + 1) arity e)

/-- Any successful bounded function conversion agrees with the total form. -/
theorem compileExpFuel_success_eq (fuel loc next arity : Nat) (e : Exp)
    (result : Option (Exp × Exp)) (run : compileExpFuel fuel loc next arity e = some result) :
    result = compileExpSource loc next arity e := by
  cases wrapper : rewriteWrapperFuel fuel loc next arity e with
  | none => simp [compileExpFuel, wrapper] at run
  | some value =>
    have wrapperEq := rewriteWrapperFuel_success_eq fuel loc next arity e value wrapper
    cases value with
    | none =>
      simp [compileExpFuel, wrapper] at run
      simp [compileExpSource, ← wrapperEq, ← run]
    | some body =>
      cases worker : rewriteWorkerFuel fuel loc next arity (arity + 1) arity e with
      | none => simp [compileExpFuel, wrapper, worker] at run
      | some output =>
        have workerEq := rewriteWorkerFuel_success_eq fuel loc next arity (arity + 1) arity e output worker
        simp [compileExpFuel, wrapper, worker] at run
        simp [compileExpSource, ← wrapperEq, ← workerEq, ← run]

/-- The production retry returns the total source-shaped function result. -/
theorem compileExpBounded_eq_source (fuel loc next arity : Nat) (e : Exp) :
    compileExpBounded fuel loc next arity e = some (compileExpSource loc next arity e) := by
  obtain ⟨result, run⟩ := compileExpBounded_succeeds fuel loc next arity e
  cases first : compileExpFuel fuel loc next arity e with
  | some value =>
    have equal := compileExpFuel_success_eq fuel loc next arity e value first
    simp [compileExpBounded, first, equal]
  | none =>
    have retry : compileExpFuel (max fuel (expBudget e + 1)) loc next arity e = some result := by
      simpa [compileExpBounded, first] using run
    have equal := compileExpFuel_success_eq _ loc next arity e result retry
    simpa [equal] using run

/-- Source-shaped program traversal in function order. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "compile_each_def"]
def compileEachSource : Nat → List (Nat × Nat × Exp) → Nat × List (Nat × Nat × Exp)
  | next, [] => (next, [])
  | next, (loc, arity, body) :: rest =>
    match compileExpSource loc next arity body with
    | none =>
      let (last, output) := compileEachSource next rest
      (last, (loc, arity, body) :: output)
    | some (wrapper, worker) =>
      let (last, output) := compileEachSource (next + Flapjack.bvlToBviNamespaces) rest
      (last, (loc, arity, wrapper) :: (next, arity + 2, worker) :: output)

/-- The production function-list traversal returns the source-shaped list. -/
theorem compileEachFuel_eq_source (fuel next : Nat) (code : List (Nat × Nat × Exp)) :
    compileEachFuel fuel next code = some (compileEachSource next code) := by
  induction code generalizing next with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨loc, arity, body⟩ := entry
    cases decision : compileExpSource loc next arity body with
    | none => simp [compileEachFuel, compileEachSource, compileExpBounded_eq_source, decision, ih]
    | some pair =>
      obtain ⟨wrapper, worker⟩ := pair
      simp [compileEachFuel, compileEachSource, compileExpBounded_eq_source, decision, ih]

/-- Source-shaped whole-program transformation, including the disabled case. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "compile_prog_def"]
def compileProgSource (enabled : Bool) (next : Nat) (code : List (Nat × Nat × Exp)) :
    Nat × List (Nat × Nat × Exp) :=
  if enabled then compileEachSource next code else (next, code)

/-- The executed program pass returns the source-shaped result for every fuel. -/
theorem compileProgFuel_eq_source (fuel : Nat) (enabled : Bool) (next : Nat)
    (code : List (Nat × Nat × Exp)) :
    compileProgFuel fuel enabled next code = some (compileProgSource enabled next code) := by
  cases enabled <;> simp [compileProgFuel, compileProgSource, compileEachFuel_eq_source]

end Flapjack.Compiler.Backend.BviTmc
