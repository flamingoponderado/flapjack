module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalEnvironment
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateMatch

@[expose] public section

/-! Pattern row evaluation with growing global environments, using the reviewed
source-to-flat relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Pattern matching only needs the constructor environment; the ordinary
invariant also extends over local variables when all short names are shadowed. -/
theorem globalEnvInv_local_for_patterns (genv : GlobalEnv) (baseMap : Environment)
    (baseEnv : SemEnv Value) (sourceLocal : Namespace ModN VarN Value)
    (flatLocals : List (VarN × FlatSem.Value)) (localRel : EnvRel genv sourceLocal flatLocals)
    (envInv : GlobalEnvInv genv baseMap (fun n => n ∈ flatLocals.map Prod.fst) baseEnv) :
    GlobalEnvInv genv baseMap (fun _ => True) { baseEnv with v := nsAppend sourceLocal baseEnv.v } := by
  cases envInv with
  | intro _ _ _ values constructors =>
    apply GlobalEnvInv.intro
    · intro id value fresh lookup
      cases id with
      | short name => exact (fresh ⟨name, trivial, rfl⟩).elim
      | long moduleName rest =>
        apply values (.long moduleName rest) value (by intro ⟨_, _, impossible⟩; cases impossible)
        change nsLookup (nsAppend sourceLocal baseEnv.v) (.long moduleName rest) = some value at lookup
        rw [nsLookup_append_long, envRel_no_modules genv sourceLocal flatLocals localRel moduleName] at lookup
        exact lookup
    · exact constructors

end Flapjack.Compiler.Backend.SourceToFlat
