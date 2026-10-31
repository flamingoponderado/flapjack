import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileByteBounds

/-! Global reads in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- A source global slot appears at the next index in the target global array.
This is infrastructure for the pass simulation. -/
theorem stateRel_globalSlot {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (ptr index : Nat) (value : Value) (related : stateRel relocate source target)
    (globalPtr : target.global = some ptr) (slot : source.globals[index]? = some (some value)) :
    ∃ fields, target.refs.lookup ptr = some (.valueArray fields) ∧
      fields[index + 1]? = some (adjustBv relocate value) := by
  obtain ⟨_, size, lookup, _⟩ := related.2.2.1 ptr globalPtr
  refine ⟨_, lookup, ?_⟩
  have bound : index < source.globals.length := List.getElem?_eq_some_iff.mp slot |>.1
  simp only [List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by simpa using bound), List.getElem?_map, slot]
  rfl

/-- Reading a source global through the corresponding target global array.
Untagged pending BVI dispatcher correspondence review. -/
theorem doGlobal_target {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (ptr index : Nat) (value : Value) (related : stateRel relocate source target)
    (globalPtr : target.global = some ptr) (slot : source.globals[index]? = some (some value)) :
    BviSem.doApp (.globOp (.global (index + 1))) [] target = .val (adjustBv relocate value, target) := by
  obtain ⟨fields, lookup, selected⟩ := stateRel_globalSlot relocate source target ptr index value related globalPtr slot
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, globalPtr, lookup, selected]

/-- A nullary global read satisfies the pass simulation. Untagged pending
BVI evaluator and dispatcher correspondence review. -/
theorem simulation_global_empty {C F : Type} (index : Nat) (env : List Value)
    (source : BvlSem.State (Nat × C) F) :
    simulation [.op (.globOp (.global index)) []] env source := by
  intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
  simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyGlobal] at run
  cases slot : source.globals[index]? with
  | none =>
    simp [slot] at run
    exact (notTypeError run.1.symm).elim
  | some item =>
    cases item with
    | none =>
      simp [slot] at run
      exact (notTypeError run.1.symm).elim
    | some value =>
      simp [slot] at run
      rcases run with ⟨rfl, rfl⟩
      simp [compileListSource, compileSingSource, compileOp, smartAppend] at compiled
      rcases compiled with ⟨rfl, rfl, rfl⟩
      cases globalPtr : target.global with
      | none => simp [globalPtr] at global
      | some ptr =>
        refine ⟨target, relocate, 0, ?_, related, rfl, ?_⟩
        · simp [BviSem.evaluate, BviSem.fixClock, BviProps.incClock, mapSimulationResult,
            doGlobal_target relocate source target ptr index value related globalPtr slot]
        · intro key present
          rfl

/-- Writing the target global array does not change any related source cell.
This follows from separation of the global pointer from relocated references. -/
theorem refsRel_writeGlobal (relocate : Nat → Nat)
    (source target : HolFiniteMapExact Nat (BvlSem.Ref Value)) (ptr : Nat) (cell : BvlSem.Ref Value)
    (related : refsRel relocate source target)
    (separate : ∀ key, source.lookup key ≠ none → ptr ≠ relocate key) :
    refsRel relocate source (target.updateEq (ptr, cell)) := by
  refine ⟨?_, related.2.1, ?_⟩
  · intro key present
    have different : relocate key ≠ ptr := Ne.symm (separate key present)
    simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using related.1 key present
  · intro key value lookup
    have present : source.lookup key ≠ none := by rw [lookup]; simp
    have different : relocate key ≠ ptr := Ne.symm (separate key present)
    simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using related.2.2 key value lookup

/-- Updating a global slot and its target array element preserves the state
relation. This is infrastructure for the global-write simulation. -/
theorem stateRel_setGlobal {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (ptr index : Nat) (value : Value) (related : stateRel relocate source target)
    (globalPtr : target.global = some ptr) (bound : index < source.globals.length) :
    ∃ fields, target.refs.lookup ptr = some (.valueArray fields) ∧
      index + 1 < fields.length ∧
      stateRel relocate { source with globals := source.globals.set index (some value) }
        { target with refs := target.refs.updateEq (ptr, .valueArray (fields.set (index + 1) (adjustBv relocate value))) } := by
  obtain ⟨separate, size, lookup, sizeBound⟩ := related.2.2.1 ptr globalPtr
  let fields := .number (Int.ofNat (source.globals.length + 1)) ::
    (source.globals.map (fun entry => (entry.map (adjustBv relocate)).getD (.number 0)) ++
      List.replicate (size - (source.globals.length + 1)) (.number 0))
  refine ⟨fields, lookup, ?_, ?_⟩
  · simp [fields]
    omega
  refine ⟨refsRel_writeGlobal relocate source.refs target.refs ptr (.valueArray (fields.set (index + 1) (adjustBv relocate value)) ) related.1 separate,
    related.2.1, ?_, related.2.2.2⟩
  intro other otherPtr
  have same : other = ptr := by rw [globalPtr] at otherPtr; exact Option.some.inj otherPtr.symm
  subst other
  refine ⟨separate, size, ?_, by simpa using sizeBound⟩
  simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, if_true, Option.some.injEq, BvlSem.Ref.valueArray.injEq]
  simp [fields, List.map_set]
  apply List.set_append_left
  simpa using bound

/-- Global writes satisfy pass simulation given operand simulation. Untagged
pending BVI evaluator and dispatcher correspondence review. -/
theorem simulation_setGlobal {C F : Type} (index : Nat) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.globOp (.setGlobal index)) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.globOp (.setGlobal index)) arguments env source middle error argsIH argsRun
    | val values =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      rcases argsCompile : compileListSource n arguments with ⟨argsCode, argsAux, finalName⟩
      have nilRight : smartAppend argsAux .nil = argsAux := by cases argsAux <;> rfl
      simp [compileListSource, compileSingSource, argsCompile, nilRight, compileOp] at compiled
      rcases compiled with ⟨rfl, rfl, rfl⟩
      have shape : BvlHandle.Proofs.handleOk arguments := by simpa [BvlHandle.Proofs.handleOk] using handlers
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
      cases reversed : values.reverse with
      | nil =>
        simp [BvlSem.doApp, BvlSem.applyGlobal, reversed] at run
        exact (notTypeError run.1.symm).elim
      | cons value rest =>
        cases rest with
        | cons second tail =>
          simp [BvlSem.doApp, BvlSem.applyGlobal, reversed] at run
          exact (notTypeError run.1.symm).elim
        | nil =>
          cases slot : middle.globals[index]? with
          | none =>
            simp [BvlSem.doApp, BvlSem.applyGlobal, reversed, slot] at run
            exact (notTypeError run.1.symm).elim
          | some previous =>
            have bound : index < middle.globals.length := List.getElem?_eq_some_iff.mp slot |>.1
            simp [BvlSem.doApp, BvlSem.applyGlobal, reversed, slot] at run
            rcases run with ⟨rfl, rfl⟩
            obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
              argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                argsCompile related sourceOk envOk installed shape global
            have targetGlobal := BviProps.evaluate_global_mono argsCode (env.map (adjustBv newRelocate))
              (BviProps.incClock clock target) targetNext (.val (values.map (adjustBv newRelocate))) (by
                simpa [mapSimulationResult] using targetArgs) (by simpa [BviProps.incClock] using global)
            cases globalPtr : targetNext.global with
            | none => simp [globalPtr] at targetGlobal
            | some ptr =>
              obtain ⟨fields, lookup, targetBound, relatedWrite⟩ :=
                stateRel_setGlobal newRelocate middle targetNext ptr index value relatedNext globalPtr bound
              refine ⟨{ targetNext with refs := targetNext.refs.updateEq (ptr, .valueArray (fields.set (index + 1) (adjustBv newRelocate value))) },
                newRelocate, clock, ?_, relatedWrite, envEq, refsEq⟩
              rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
              simp only [mapSimulationResult]
              rw [← List.map_reverse, reversed]
              simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, globalPtr, lookup, targetBound,
                BvlSem.unitValue, adjustBv, adjustValues]

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
