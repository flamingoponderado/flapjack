module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateSequence

@[expose] public section

/-! Constructor composition for argument lists that may change state and
grow the preliminary factored global environment. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- An aborted argument evaluation makes the constructor abort with the
same related states, without needing a post-abort environment relation. -/
theorem exprSim_constructor_abort {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (source : State F) (flat : FlatSem.State C F) (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp)
    (check : doConCheck sourceEnv.c name args.length = true)
    (argsSim : ExprListSim genv compMap trace sourceEnv flatEnv source flat args.reverse)
    (nextSource : State F) (error : Abort)
    (sourceRun : EvaluateHOL.evaluate source sourceEnv args.reverse = (nextSource, .err (.abort error))) :
    ExprSim genv compMap trace sourceEnv flatEnv source flat (.con name args) := by
  unfold ExprListSim at argsSim
  rw [compileExps_reverse, sourceRun] at argsSim
  generalize flatRun : FlatSem.evaluate flatEnv flat (compileExps trace compMap args).reverse = result at argsSim
  obtain ⟨nextFlat, flatResult⟩ := result
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort =>
    unfold ExprSim
    rw [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate]
    simp only [check, if_true, sourceRun, flatRun]
    exact ⟨.abort error, states⟩

end Flapjack.Compiler.Backend.SourceToFlat
