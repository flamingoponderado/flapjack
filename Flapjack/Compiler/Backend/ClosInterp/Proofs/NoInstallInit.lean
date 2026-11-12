module

public import Flapjack.Compiler.Backend.ClosInterp.Proofs.NoInstallFull

@[expose] public section


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

/-- If a program has no installation, its attached initializer has none either. -/
theorem attachInterpreter_noInstall (expressions : List ClosLang.Exp)
    (safe : ClosLang.hasInstallList expressions = false) :
    ClosLang.hasInstallList (attachInterpreter expressions) = false := by
  simp [attachInterpreter, safe, compileInit, interpreterCons_eq, interpreterVar_eq,
    ClosLang.hasInstallList, ClosLang.hasInstall]

end Flapjack.Compiler.Backend.ClosInterp
