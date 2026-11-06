import Flapjack.Compiler.Backend.ClosInterp.Proofs.SimulationFull

/-! Initialization and interpreter insertion for the proof-side evaluator.
The evaluator and state carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendProps

/-- Initialization allocates global slot zero and installs the interpreter. -/
theorem evaluate_compileInit_true {C F : Type} (state : ClosSem.State C F)
    (emptyGlobals : state.globals = []) (positive : 1 ≤ state.maxApp) :
    ClosSem.evaluate [compileInit true] [] state =
      (.val [ClosSem.unitValue],
        { state with globals := [some (.closure none [] [] 1 closInterpreter)] }) := by
  simp [compileInit, interpreterVar_eq, closInterpreter, ClosSem.evaluate,
    ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric, ClosSem.doIntApp,
    ClosSem.applyGlobal, ClosSem.getGlobal, emptyGlobals, positive, ClosSem.unitValue]

/-- Initialization without installation reserves global slot zero as unit. -/
theorem evaluate_compileInit_false {C F : Type} (state : ClosSem.State C F)
    (emptyGlobals : state.globals = []) :
    ClosSem.evaluate [compileInit false] [] state =
      (.val [ClosSem.unitValue], { state with globals := [some ClosSem.unitValue] }) := by
  simp [compileInit, interpreterCons_eq, interpreterVar_eq, ClosSem.evaluate,
    ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric, ClosSem.doIntApp,
    ClosSem.applyGlobal, ClosSem.applyBlock, ClosSem.getGlobal, emptyGlobals, ClosSem.unitValue]

/-- Initial states become related after the interpreter is installed in slot zero. -/
theorem initialized_states_related {C F : Type} (ffi : HolFfiState F) (maxApp clock : Nat)
    (oracle : ClosSem.CompileOracle C) (compiler : ClosSem.Compiler C)
    (safe : ∀ index, (oracle index).2.2 = []) (positive : 1 ≤ maxApp) :
    StateRel
      { ClosSem.initialState ffi maxApp HolFiniteMapExact.empty oracle (pureCc insertProgram compiler) clock with
        globals := [some (.closure none [] [] 1 closInterpreter)] }
      { ClosSem.initialState ffi maxApp HolFiniteMapExact.empty (pureCo insertProgram ∘ oracle) compiler clock with
        globals := [some (.closure none [] [] 1 closInterpreter)] } := by
  exact ⟨⟨safe, rfl, rfl, rfl, positive, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- When the initializer installs the interpreter, the attached program
simulates from related initialized states. -/
theorem attachInterpreter_installed_simulation {C F : Type} (expressions : List ClosLang.Exp)
    (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (needsInterpreter : ClosLang.hasInstallList expressions = true)
    (sourceEmpty : source.globals = []) (targetEmpty : target.globals = [])
    (sourcePositive : 1 ≤ source.maxApp) (targetPositive : 1 ≤ target.maxApp)
    (initializedRel : StateRel
      { source with globals := [some (.closure none [] [] 1 closInterpreter)] }
      { target with globals := [some (.closure none [] [] 1 closInterpreter)] })
    (run : ClosSem.evaluate (attachInterpreter expressions) [] source = (result, sourceFinal))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate (attachInterpreter expressions) [] { target with clock := extra + target.clock } =
        (result, targetFinal) ∧ StateRel sourceFinal targetFinal := by
  let sourceInitialized := { source with globals := [some (.closure none [] [] 1 closInterpreter)] }
  let targetInitialized := { target with globals := [some (.closure none [] [] 1 closInterpreter)] }
  have initRun : ClosSem.evaluate [compileInit true] [] source = (.val [ClosSem.unitValue], sourceInitialized) := by
    simpa [sourceInitialized] using evaluate_compileInit_true source sourceEmpty sourcePositive
  have sourceSequence := ClosProps.evaluate_cons_value (compileInit true) expressions [] source sourceInitialized ClosSem.unitValue initRun
  cases bodyRun : ClosSem.evaluate expressions [] sourceInitialized with
  | mk bodyResult sourceLast =>
    rw [bodyRun] at sourceSequence
    have bodyNotTypeError : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      simp at sourceSequence
      have sourceRun : ClosSem.evaluate (compileInit true :: expressions) [] source = (result, sourceFinal) := by
        simpa [attachInterpreter, needsInterpreter] using run
      rw [sourceSequence] at sourceRun
      simp at sourceRun
      exact notTypeError sourceRun.1.symm
    obtain ⟨extra, targetLast, targetBody, finalRel⟩ :=
      evaluate_simulation.1 expressions [] sourceInitialized targetInitialized sourceLast bodyResult bodyRun
        initializedRel bodyNotTypeError
    have targetInitRun : ClosSem.evaluate [compileInit true] [] { target with clock := extra + target.clock } =
        (.val [ClosSem.unitValue], { targetInitialized with clock := extra + targetInitialized.clock }) := by
      simpa [targetInitialized] using evaluate_compileInit_true
        { target with clock := extra + target.clock } (by simpa using targetEmpty) (by simpa using targetPositive)
    have targetBody' : ClosSem.evaluate expressions [] { targetInitialized with clock := extra + targetInitialized.clock } =
        (bodyResult, targetLast) := targetBody
    have targetSequence := ClosProps.evaluate_cons_value (compileInit true) expressions []
      { target with clock := extra + target.clock } { targetInitialized with clock := extra + targetInitialized.clock }
      ClosSem.unitValue targetInitRun
    rw [targetBody'] at targetSequence
    have sourceRun : ClosSem.evaluate (compileInit true :: expressions) [] source = (result, sourceFinal) := by
      simpa [attachInterpreter, needsInterpreter] using run
    rw [sourceSequence] at sourceRun
    cases bodyResult with
    | err error =>
      simp at sourceRun targetSequence
      rcases sourceRun with ⟨rfl, rfl⟩
      refine ⟨extra, targetLast, ?_, finalRel⟩
      simpa [attachInterpreter, needsInterpreter] using targetSequence
    | val values =>
      simp at sourceRun targetSequence
      rcases sourceRun with ⟨rfl, rfl⟩
      refine ⟨extra, targetLast, ?_, finalRel⟩
      simpa [attachInterpreter, needsInterpreter] using targetSequence

/-- Attached programs that need installation simulate from the corresponding
initial compiler and oracle states. -/
theorem attachInterpreter_initial_simulation {C F : Type} (expressions : List ClosLang.Exp)
    (ffi : HolFfiState F) (maxApp clock : Nat) (oracle : ClosSem.CompileOracle C)
    (compiler : ClosSem.Compiler C) (sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (needsInterpreter : ClosLang.hasInstallList expressions = true)
    (safe : ∀ index, (oracle index).2.2 = []) (positive : 1 ≤ maxApp)
    (run : ClosSem.evaluate (attachInterpreter expressions) []
      (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty oracle (pureCc insertProgram compiler) clock) = (result, sourceFinal))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate (attachInterpreter expressions) []
        { ClosSem.initialState ffi maxApp HolFiniteMapExact.empty (pureCo insertProgram ∘ oracle) compiler clock with
          clock := extra + clock } = (result, targetFinal) ∧ StateRel sourceFinal targetFinal := by
  have simulation := attachInterpreter_installed_simulation expressions
    (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty oracle (pureCc insertProgram compiler) clock)
    (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty (pureCo insertProgram ∘ oracle) compiler clock)
    sourceFinal result needsInterpreter rfl rfl positive positive
    (initialized_states_related ffi maxApp clock oracle compiler safe positive) run notTypeError
  simpa [ClosSem.initialState] using simulation

end Flapjack.Compiler.Backend.ClosInterp
