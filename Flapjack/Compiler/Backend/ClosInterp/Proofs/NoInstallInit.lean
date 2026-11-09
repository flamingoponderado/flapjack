import Flapjack.Compiler.Backend.ClosInterp.Proofs.NoInstallFull

/-! Initial no-install states for interpreter insertion. The evaluator and
state carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendProps

/-- The empty code store contains no installation body. -/
theorem emptyCode_noInstall : codeNoInstall HolFiniteMapExact.empty := by
  intro location arity body found
  simp [HolFiniteMapExact.empty] at found

/-- Both sides of the no-install relation satisfy the evaluator invariant. -/
theorem stateRelNoInstall_evalStates {C F : Type} (source target : ClosSem.State C F)
    (related : StateRelNoInstall source target) : evalStateNoInstall source ∧ evalStateNoInstall target := by
  rcases related with ⟨⟨_, sourceCode, targetCode, _, _, _, _, globals, refs, _, _⟩, globalsOk, refsOk⟩
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · simpa [globalsNoInstall, globals] using globalsOk
    · simpa [refs] using refsOk
    · rw [sourceCode]; exact emptyCode_noInstall
  · exact ⟨globalsOk, refsOk, by rw [targetCode]; exact emptyCode_noInstall⟩

/-- Either related state can evaluate safe expressions without producing an
unsafe value or store. This does not assert that the two evaluations agree. -/
theorem stateRelNoInstall_evaluate_safe {C F : Type} (expressions : List ClosLang.Exp)
    (env : List ClosSem.Value) (source target sourceFinal targetFinal : ClosSem.State C F)
    (sourceResult targetResult : Result (List ClosSem.Value) ClosSem.Value)
    (related : StateRelNoInstall source target) (safe : ClosLang.hasInstallList expressions = false)
    (envOk : valuesNoInstall env = true)
    (sourceRun : ClosSem.evaluate expressions env source = (sourceResult, sourceFinal))
    (targetRun : ClosSem.evaluate expressions env target = (targetResult, targetFinal)) :
    (resultNoInstall sourceResult ∧ evalStateNoInstall sourceFinal) ∧
      (resultNoInstall targetResult ∧ evalStateNoInstall targetFinal) := by
  obtain ⟨sourceOk, targetOk⟩ := stateRelNoInstall_evalStates source target related
  exact ⟨evaluate_noInstall.1 expressions env source sourceFinal sourceResult safe envOk sourceOk sourceRun,
    evaluate_noInstall.1 expressions env target targetFinal targetResult safe envOk targetOk targetRun⟩

/-- If a program has no installation, its attached initializer has none either. -/
theorem attachInterpreter_noInstall (expressions : List ClosLang.Exp)
    (safe : ClosLang.hasInstallList expressions = false) :
    ClosLang.hasInstallList (attachInterpreter expressions) = false := by
  simp [attachInterpreter, safe, compileInit, interpreterCons_eq, interpreterVar_eq,
    ClosLang.hasInstallList, ClosLang.hasInstall]

/-- Initial closure states with empty code satisfy the evaluator invariant. -/
theorem initialState_evalNoInstall {C F : Type} (ffi : HolFfiState F) (maxApp clock : Nat)
    (oracle : ClosSem.CompileOracle C) (compiler : ClosSem.Compiler C) :
    evalStateNoInstall (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty oracle compiler clock) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [ClosSem.initialState, globalsNoInstall]
  · simp [ClosSem.initialState, refsNoInstall, HolFiniteMapExact.empty]
  · simpa [ClosSem.initialState] using emptyCode_noInstall

/-- Evaluating an attached program with no installation from an initial state
preserves safe returned values, globals, references, and code bodies. -/
theorem attachInterpreter_initial_noInstall {C F : Type} (expressions : List ClosLang.Exp)
    (ffi : HolFfiState F) (maxApp clock : Nat) (oracle : ClosSem.CompileOracle C)
    (compiler : ClosSem.Compiler C) (final : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (safe : ClosLang.hasInstallList expressions = false)
    (run : ClosSem.evaluate (attachInterpreter expressions) []
      (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty oracle compiler clock) = (result, final)) :
    resultNoInstall result ∧ evalStateNoInstall final := by
  exact evaluate_noInstall.1 (attachInterpreter expressions) [] _ final result
    (attachInterpreter_noInstall expressions safe) (by simp [valuesNoInstall])
    (initialState_evalNoInstall ffi maxApp clock oracle compiler) run

end Flapjack.Compiler.Backend.ClosInterp
