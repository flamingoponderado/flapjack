import Flapjack.Compiler.Backend.BvlToBvi.Proofs.FindCode

/-! Thunk inspection and evaluated-force simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Successful thunk inspection is preserved by state relocation. This is
Flapjack infrastructure for the source force case. -/
theorem destThunk_stateRel {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (thunk value : Value) (mode : AstHOL.ThunkMode)
    (related : stateRel relocate source target)
    (found : BvlSem.destThunk thunk source.refs = .isThunk mode value) :
    BviSem.destThunk (adjustBv relocate thunk) target.refs = .isThunk mode (adjustBv relocate value) := by
  cases thunk with
  | refPtr flag address =>
    cases lookup : source.refs.lookup address with
    | none => simp [BvlSem.destThunk, lookup] at found
    | some entry =>
      cases entry with
      | thunk storedMode storedValue =>
        cases flag with
        | true => simp [BvlSem.destThunk, lookup] at found
        | false =>
          simp [BvlSem.destThunk, lookup] at found
          rcases found with ⟨rfl, rfl⟩
          have targetLookup := stateRel_thunk relocate source target address storedMode storedValue related lookup
          simp [adjustBv, BviSem.destThunk, targetLookup]
      | _ => simp [BvlSem.destThunk, lookup] at found
  | _ => simp [BvlSem.destThunk] at found

/-- Force of an already evaluated thunk preserves its relocated result and
the state. Untagged pending BVI evaluator correspondence review. -/
theorem simulation_force_evaluated {C F : Type} (location index : Nat) (env : List Value)
    (source : BvlSem.State (Nat × C) F) (thunk value : Value)
    (lookup : env[index]? = some thunk)
    (found : BvlSem.destThunk thunk source.refs = .isThunk .evaluated value) :
    simulation [.force location index] env source := by
  intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
  simp [BvlSem.evaluate, lookup, found] at run
  rcases run with ⟨rfl, rfl⟩
  simp [compileListSource, compileSingSource, smartAppend] at compiled
  rcases compiled with ⟨rfl, rfl, rfl⟩
  have targetLookup : (env.map (adjustBv relocate))[index]? = some (adjustBv relocate thunk) := by
    simp [lookup]
  have targetThunk := destThunk_stateRel relocate source target thunk value .evaluated related found
  refine ⟨target, relocate, 0, ?_, related, rfl, ?_⟩
  · simp [BviSem.evaluate, BviProps.incClock, targetLookup, targetThunk, mapSimulationResult]
  · intro key present
    rfl

/-- Force of an unevaluated thunk follows from the dynamically selected
body's simulation at a strictly smaller clock. Untagged pending BVI evaluator
and dispatcher correspondence review. -/
theorem simulation_force_unevaluated {C F : Type} (location index : Nat) (env : List Value)
    (source : BvlSem.State (Nat × C) F) (thunk function : Value)
    (lookup : env[index]? = some thunk)
    (found : BvlSem.destThunk thunk source.refs = .isThunk .notEvaluated function)
    (bodyIH : ∀ (body : Bvl.Exp) (args : List Value) (s : BvlSem.State (Nat × C) F),
      s.clock < source.clock → simulation [body] args s) :
    simulation [.force location index] env source := by
  intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
  simp [compileListSource, compileSingSource, smartAppend] at compiled
  rcases compiled with ⟨rfl, rfl, rfl⟩
  cases selected : BvlSem.findCode (some location) [thunk, function] source.code with
  | none =>
    simp [BvlSem.evaluate, lookup, found, selected] at run
    exact (notTypeError run.1.symm).elim
  | some pair =>
    rcases pair with ⟨args, body⟩
    obtain ⟨bodyName, converted, bodyAux, finalName, bodyCompiled, targetFind, bodyInstalled, bodyShape⟩ :=
      stateRel_findCode relocate source target (some location) [thunk, function] args body related selected
    have targetFind' : BvlSem.findCode (some (bvlNumStubs + bvlToBviNamespaces * location))
        [adjustBv relocate thunk, adjustBv relocate function] target.code =
          some (args.map (adjustBv relocate), BviLet.compileSing [] 0 converted) := by
      simpa using targetFind
    have targetLookup : (env.map (adjustBv relocate))[index]? = some (adjustBv relocate thunk) := by simp [lookup]
    have targetThunk := destThunk_stateRel relocate source target thunk function .notEvaluated related found
    have clocks : source.clock = target.clock := related.2.2.2.1
    by_cases zero : source.clock = 0
    · have targetZero : target.clock = 0 := by omega
      have sourceReset : { source with clock := 0 } = source := by cases source; simp_all
      have targetReset : { target with clock := 0 } = target := by cases target; simp_all
      simp [BvlSem.evaluate, lookup, found, selected, zero, sourceReset] at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨target, relocate, 0, ?_, related, rfl, ?_⟩
      · simp [BviSem.evaluate, BviProps.incClock, targetLookup, targetThunk, targetFind',
          targetZero, targetReset, mapSimulationResult]
      · intro key present
        rfl
    · have bodyRun : BvlSem.evaluate [body] args (BvlSem.decClock 1 source) = (res, next) := by
        simpa [BvlSem.evaluate, lookup, found, selected, zero] using run
      have thunkOk : bvOk source.refs thunk :=
        (bvOkList_iff _ _).1 envOk thunk (List.mem_of_getElem? lookup)
      have functionOk : bvOk source.refs function := destThunk_ok source thunk function .notEvaluated sourceOk found
      have argsOk : bvOkList source.refs args := by
        apply findCode_bvOk (some location) [thunk, function] args source.code body source.refs selected
        simpa [bvOkList] using And.intro thunkOk functionOk
      have relatedDec := stateRel_decClock relocate source target related 1
      have sourceOkDec : stateOk (BvlSem.decClock 1 source) := (stateOk_decClock 1 source).2 sourceOk
      have bodyClockSmaller : (BvlSem.decClock 1 source).clock < source.clock := by
        simp [BvlSem.decClock]
        omega
      obtain ⟨targetNext, finalRelocate, clock, targetRun, relatedNext, argsEq, refsEq⟩ :=
        bodyIH body args (BvlSem.decClock 1 source) bodyClockSmaller bodyName res next
          (BviSem.decClock 1 target) finalName [converted] bodyAux relocate bodyRun notTypeError bodyCompiled
          relatedDec sourceOkDec argsOk bodyInstalled bodyShape global
      have envEq := adjustMap_eq_of_ok relocate finalRelocate env source.refs envOk refsEq
      have inputsOk : bvOkList source.refs [thunk, function] := by simpa [bvOkList] using And.intro thunkOk functionOk
      have inputsEq := adjustMap_eq_of_ok relocate finalRelocate [thunk, function] source.refs inputsOk refsEq
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at inputsEq
      have thunkEq := inputsEq.1
      have functionEq := inputsEq.2.1
      have targetLookupFinal : (env.map (adjustBv finalRelocate))[index]? = some (adjustBv finalRelocate thunk) := by
        simpa [← envEq, ← thunkEq] using targetLookup
      have targetThunkFinal : BviSem.destThunk (adjustBv finalRelocate thunk) target.refs =
          .isThunk .notEvaluated (adjustBv finalRelocate function) := by
        simpa [← thunkEq, ← functionEq] using targetThunk
      have targetFindFinal : BvlSem.findCode (some (bvlNumStubs + bvlToBviNamespaces * location))
          [adjustBv finalRelocate thunk, adjustBv finalRelocate function] target.code =
            some (args.map (adjustBv finalRelocate), BviLet.compileSing [] 0 converted) := by
        simpa [← thunkEq, ← functionEq, ← argsEq] using targetFind'
      have optimized := BviLet.Proofs.evaluate_compileList [converted] (args.map (adjustBv finalRelocate))
        (BviProps.incClock clock (BviSem.decClock 1 target)) targetNext (mapSimulationResult finalRelocate res)
        targetRun (by cases res with | val values => simp [mapSimulationResult] | err error => cases error <;> simp_all [mapSimulationResult])
      have optimizedRun : BviSem.evaluate [BviLet.compileSing [] 0 converted] (args.map (adjustBv finalRelocate))
          (BviProps.incClock clock (BviSem.decClock 1 target)) = (mapSimulationResult finalRelocate res, targetNext) := by
        simpa [BviLet.compileList, BviSem.evaluateTuple] using optimized
      have targetNonzero : target.clock ≠ 0 := by omega
      have clockNonzero : (BviProps.incClock clock target).clock ≠ 0 := by simp [BviProps.incClock]; omega
      refine ⟨targetNext, finalRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
      rw [BviSem.evaluate]
      simp only [show (BviProps.incClock clock target).refs = target.refs from rfl,
        show (BviProps.incClock clock target).code = target.code from rfl,
        targetLookupFinal, targetThunkFinal, targetFindFinal, clockNonzero, ↓reduceIte]
      rw [BviProps.decClock_incClock_one target clock targetNonzero]
      rw [optimizedRun]
      cases res with
      | val values => rfl
      | err error => cases error <;> rfl

/-- The force simulation follows from the dynamic body simulation at smaller
clocks. Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem simulation_force {C F : Type} (location index : Nat) (env : List Value)
    (source : BvlSem.State (Nat × C) F)
    (bodyIH : ∀ (body : Bvl.Exp) (args : List Value) (s : BvlSem.State (Nat × C) F),
      s.clock < source.clock → simulation [body] args s) :
    simulation [.force location index] env source := by
  cases lookup : env[index]? with
  | none =>
    intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
    simp [BvlSem.evaluate, lookup] at run
    exact (notTypeError run.1.symm).elim
  | some thunk =>
    cases found : BvlSem.destThunk thunk source.refs with
    | badRef =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      simp [BvlSem.evaluate, lookup, found] at run
      exact (notTypeError run.1.symm).elim
    | notThunk =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      simp [BvlSem.evaluate, lookup, found] at run
      exact (notTypeError run.1.symm).elim
    | isThunk mode value =>
      cases mode with
      | evaluated => exact simulation_force_evaluated location index env source thunk value lookup found
      | notEvaluated => exact simulation_force_unevaluated location index env source thunk value lookup found bodyIH

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
