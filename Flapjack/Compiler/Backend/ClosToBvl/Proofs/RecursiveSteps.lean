import Flapjack.Compiler.Backend.ClosToBvl.Proofs.RecursiveAllocation
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateClosure

/-! Evaluation of generated mutually recursive closure construction. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL

/-- The initial generated recursive-closure step builds a closure block,
stores it at the requested in-bounds array position, and returns that block.
The code label must be installed, exactly as required by BVL label evaluation. -/
theorem evaluate_reccLet0 {C F : Type} (state : BvlSem.State C F)
    (env : List BvlSem.Value) (ptr label arity index : Nat) (values : List BvlSem.Value)
    (labelInstalled : ∃ entry, sptLookup label state.code = some entry)
    (lookup : state.refs.lookup ptr = some (.valueArray values)) (bound : index < values.length) :
    let block := BvlSem.Value.block 30 [.codePtr label, .number (Int.ofNat (arity - 1)), .refPtr true ptr]
    BvlSem.evaluate [reccLet0 label arity index] (.refPtr true ptr :: env) state =
      (.val [block], { state with refs := state.refs.updateEq (ptr, .valueArray (values.set index block)) }) := by
  obtain ⟨entry, labelLookup⟩ := labelInstalled
  have inBounds : ¬ values.length ≤ index := by omega
  have nonnegative : ¬ ((index : Int) < 0) := by omega
  simp [reccLet0, mkConst, mkLabel, BvlSem.evaluate, BvlSem.fixClock,
    BvlSem.doApp, BvlSem.applyBlock, BvlSem.applyNumeric, BvlSem.doIntApp,
    BvlSem.applyMemory, labelLookup, lookup, inBounds, nonnegative]

/-- A subsequent recursive-closure step reads the shared pointer from the
previous block, writes a new block at the requested position, and returns it. -/
theorem evaluate_reccLet {C F : Type} (state : BvlSem.State C F)
    (env : List BvlSem.Value) (ptr label arity index previousLabel : Nat) (previousArity : Int)
    (values : List BvlSem.Value)
    (labelInstalled : ∃ entry, sptLookup label state.code = some entry)
    (lookup : state.refs.lookup ptr = some (.valueArray values)) (bound : index < values.length) :
    let block := BvlSem.Value.block 30 [.codePtr label, .number (Int.ofNat (arity - 1)), .refPtr true ptr]
    BvlSem.evaluate [reccLet label arity index]
      (.block 30 [.codePtr previousLabel, .number previousArity, .refPtr true ptr] :: env) state =
      (.val [block], { state with refs := state.refs.updateEq (ptr, .valueArray (values.set index block)) }) := by
  let oldClosure := BvlSem.Value.block 30 [.codePtr previousLabel, .number previousArity, .refPtr true ptr]
  have extract : BvlSem.evaluate [.op (.blockOp (.elemAt 2)) [.var 0]] (oldClosure :: env) state =
      (.val [.refPtr true ptr], state) := by
    simp [oldClosure, BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyBlock]
  change BvlSem.evaluate [.let [.op (.blockOp (.elemAt 2)) [.var 0]] (reccLet0 label arity index)]
      (oldClosure :: env) state = _
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, extract]
  exact evaluate_reccLet0 state (oldClosure :: env) ptr label arity index values labelInstalled lookup bound

/-- One iteration of the generated recursive builder performs its write and
continues with the new closure at the front of the target environment. -/
theorem evaluate_reccLets_succ {C F : Type} (state : BvlSem.State C F)
    (env : List BvlSem.Value) (ptr base arity index previousLabel : Nat) (previousArity : Int)
    (values : List BvlSem.Value) (remaining : List Nat) (body : Bvl.Exp)
    (labelInstalled : ∃ entry, sptLookup (base + 2 * index) state.code = some entry)
    (lookup : state.refs.lookup ptr = some (.valueArray values)) (bound : index < values.length) :
    let oldClosure := BvlSem.Value.block 30 [.codePtr previousLabel, .number previousArity, .refPtr true ptr]
    let block := BvlSem.Value.block 30 [.codePtr (base + 2 * index),
      .number (Int.ofNat (arity - 1)), .refPtr true ptr]
    let next := { state with refs := state.refs.updateEq (ptr, .valueArray (values.set index block)) }
    BvlSem.evaluate [reccLetsHOL base (arity :: remaining) (index + 1) body] (oldClosure :: env) state =
      BvlSem.evaluate [reccLetsHOL base remaining index body] (block :: oldClosure :: env) next := by
  have step := evaluate_reccLet state env ptr (base + 2 * index) arity index previousLabel previousArity
    values labelInstalled lookup bound
  change BvlSem.evaluate [.let [reccLet (base + 2 * index) arity index]
      (reccLetsHOL base remaining index body)] _ state = _
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, step]
  rfl

/-- The initial generated write also preserves the source-to-target relation
when it targets a cell that was fresh in the original target store. -/
theorem evaluate_reccLet0_targetOnly {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (current : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    (env : List BvlSem.Value) (ptr label arity index : Nat) (values : List BvlSem.Value)
    (states : stateRel f s t) (unused : t.refs.lookup ptr = none)
    (extension : ∀ key cell, t.refs.lookup key = some cell → current.lookup key = some cell)
    (labelInstalled : ∃ entry, sptLookup label t.code = some entry)
    (lookup : current.lookup ptr = some (.valueArray values)) (bound : index < values.length) :
    let block := BvlSem.Value.block 30 [.codePtr label, .number (Int.ofNat (arity - 1)), .refPtr true ptr]
    let next := { t with refs := current.updateEq (ptr, .valueArray (values.set index block)) }
    BvlSem.evaluate [reccLet0 label arity index] (.refPtr true ptr :: env) { t with refs := current } =
      (.val [block], next) ∧
    stateRel f s next ∧ unmappedRefsSubmap t.refs next.refs f f ∧
    (¬ ∃ sourcePtr, f.lookup sourcePtr = some ptr) ∧
    next.refs.lookup ptr = some (.valueArray (values.set index block)) := by
  refine ⟨?_, stateRel_targetRefs_update_originally_fresh s t f current ptr
    (.valueArray (values.set index (.block 30 [.codePtr label, .number (Int.ofNat (arity - 1)), .refPtr true ptr])))
    states unused extension⟩
  exact evaluate_reccLet0 { t with refs := current } env ptr label arity index values labelInstalled lookup bound

/-- A list of zero constants evaluates without changing the BVL state. -/
theorem evaluate_zero_constants {C F : Type} (count : Nat) (env : List BvlSem.Value)
    (state : BvlSem.State C F) :
    BvlSem.evaluate (List.replicate count (mkConst 0)) env state =
      (.val (List.replicate count (.number 0)), state) := by
  induction count with
  | zero => simp [BvlSem.evaluate]
  | succ count ih =>
    have head : BvlSem.evaluate [mkConst 0] env state = (.val [.number 0], state) := by
      simp [mkConst, BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyNumeric, BvlSem.doIntApp]
    cases count with
    | zero => simpa using head
    | succ rest =>
      simp only [List.replicate_succ] at ih ⊢
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, head, ih]
      rfl

/-- The recursive builder's initial allocation contains one zero placeholder
per function followed by the captured values, and uses the evaluator's least
unused reference. -/
theorem evaluate_recursiveArray_allocate {C F : Type} (arities indices : List Nat)
    (env : List BvlSem.Value) (state : BvlSem.State C F) (values : List BvlSem.Value)
    (nonempty : arities ≠ []) (lookup : ClosSem.lookupVars indices env = some values) :
    let ptr := BvlSem.leastUnusedRef state.refs
    let initial := List.replicate arities.length (BvlSem.Value.number 0) ++ values
    BvlSem.evaluate [.op (.memOp .ref)
      (((arities.map fun _ => mkConst 0) ++ indices.map Bvl.Exp.var).reverse)] env state =
      (.val [.refPtr true ptr], { state with refs := state.refs.updateEq (ptr, .valueArray initial) }) := by
  have zeros : (arities.map (fun _ => mkConst 0)).reverse = List.replicate arities.length (mkConst 0) := by
    simp
  have zerosNonempty : List.replicate arities.length (mkConst 0) ≠ [] := by
    cases arities with
    | nil => contradiction
    | cons first rest => simp
  have zeroRun := evaluate_zero_constants arities.length env state
  have captured := lookupVars_reverse indices env values lookup
  have argRun := evaluate_vars_append indices.reverse env state state values.reverse
    (List.replicate arities.length (.number 0)) (List.replicate arities.length (mkConst 0))
    zerosNonempty captured zeroRun
  have argRun' : BvlSem.evaluate
      (((arities.map fun _ => mkConst 0) ++ indices.map Bvl.Exp.var).reverse) env state =
      (.val (values.reverse ++ List.replicate arities.length (.number 0)), state) := by
    simpa [zeros] using argRun
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argRun']
  simp [BvlSem.doApp, BvlSem.applyMemory]

/-- The generated initialization allocates the placeholder array and writes
the first recursive closure block, leaving the captured suffix intact. -/
theorem evaluate_recursiveArray_first {C F : Type} (arities indices : List Nat)
    (env : List BvlSem.Value) (state : BvlSem.State C F) (values : List BvlSem.Value)
    (label arity index : Nat) (nonempty : arities ≠ []) (indexBound : index < arities.length)
    (lookup : ClosSem.lookupVars indices env = some values)
    (labelInstalled : ∃ entry, sptLookup label state.code = some entry) :
    let ptr := BvlSem.leastUnusedRef state.refs
    let initial := List.replicate arities.length (BvlSem.Value.number 0) ++ values
    let allocated := { state with refs := state.refs.updateEq (ptr, .valueArray initial) }
    let block := BvlSem.Value.block 30 [.codePtr label, .number (Int.ofNat (arity - 1)), .refPtr true ptr]
    let next := { allocated with refs := allocated.refs.updateEq (ptr, .valueArray (initial.set index block)) }
    BvlSem.evaluate [.let [.op (.memOp .ref)
      (((arities.map fun _ => mkConst 0) ++ indices.map Bvl.Exp.var).reverse)] (reccLet0 label arity index)] env state =
      (.val [block], next) := by
  let ptr := BvlSem.leastUnusedRef state.refs
  let initial := List.replicate arities.length (BvlSem.Value.number 0) ++ values
  let allocated := { state with refs := state.refs.updateEq (ptr, .valueArray initial) }
  have allocatedRun := evaluate_recursiveArray_allocate arities indices env state values nonempty lookup
  change BvlSem.evaluate [.op (.memOp .ref)
      (((arities.map fun _ => mkConst 0) ++ indices.map Bvl.Exp.var).reverse)] env state =
      (.val [.refPtr true ptr], allocated) at allocatedRun
  have arrayLookup : allocated.refs.lookup ptr = some (.valueArray initial) := by
    simp [allocated, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  have arrayBound : index < initial.length := by simp [initial]; omega
  have step := evaluate_reccLet0 allocated env ptr label arity index initial labelInstalled arrayLookup arrayBound
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, allocatedRun]
  exact step

end Flapjack.Compiler.Backend.ClosToBvl
