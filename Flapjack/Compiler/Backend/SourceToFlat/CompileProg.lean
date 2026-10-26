import Flapjack.Compiler.Backend.SourceToFlat.CompileDecs

/-! Program and incremental compilation before flat elimination and pattern compilation.
These definitions do not yet constitute the complete `source_to_flat$compile` pass. -/

namespace Flapjack.Compiler.Backend.SourceToFlat

open Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- Allocate the globals introduced by this compilation. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "glob_alloc_def"]
def globAlloc (next : NextIndices) (c : Config) : FlatLang.Exp :=
  .let_ omTra none (.app omTra (.globalVarAlloc (next.vidx - c.next.vidx)) [])
    (.con omTra none [])

/-- Initialize global slot zero with the environment reference. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "alloc_env_ref_def"]
def allocEnvRef : FlatLang.Exp :=
  .app .none (.globalVarInit 0) [.app .none (.src .opref) [.con .none none []]]

/-- Compile a source program and save its environment generation. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "compile_prog_def"]
def compileProg (c : Config) (p : List AstHOL.Dec) : Config × List FlatLang.Exp :=
  let next := { c.next with vidx := c.next.vidx + 1 }
  let envs : EnvironmentGenerationStore := { next := 0, generation := c.envs.next, envs := .ln }
  let (_, next, e, gen, p') := compileDecs [] 1 next c.modEnv envs p
  let envs2 : EnvironmentStore :=
    { next := c.envs.next + 1, envGens := sptInsert c.envs.next gen.envs c.envs.envGens }
  ({ c with next := next, envs := envs2, modEnv := e }, globAlloc next c :: allocEnvRef :: p')

/-- Retrieve an environment by generation and identifier, defaulting to the empty environment. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "lookup_env_id_def"]
def lookupEnvId (envId : Nat × Nat) (envs : EnvironmentStore) : Environment :=
  match sptLookup envId.1 envs.envGens with
  | none => emptyEnv
  | some gen => (sptLookup envId.2 gen).getD emptyEnv

/-- Store the identifier of the latest incremental environment in global slot zero. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "store_env_id_def"]
def storeEnvId (gen id : Nat) : FlatLang.Exp :=
  let r : MlString := .implode [114]
  .let_ .none (some r) (.app .none (.globalVarLookup 0) [])
    (.app .none (.src .opassign) [.varLocal .none r, envIdTuple gen id])

/-- Compile against a stored environment and save the extended environment. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "inc_compile_prog_def"]
def incCompileProg (envId : Nat × Nat) (c : Config) (p : List AstHOL.Dec) :
    Config × List FlatLang.Exp :=
  let env := lookupEnvId envId c.envs
  let envs : EnvironmentGenerationStore := { next := 0, generation := c.envs.next, envs := .ln }
  let (_, next, e, gen, p') := compileDecs [] 1 c.next env envs p
  let genEnvs := sptInsert gen.next (extendEnv e env) gen.envs
  let envs2 : EnvironmentStore :=
    { next := c.envs.next + 1, envGens := sptInsert c.envs.next genEnvs c.envs.envGens }
  ({ c with next := next, envs := envs2 },
    globAlloc next c :: (p' ++ [storeEnvId gen.generation gen.next]))

end Flapjack.Compiler.Backend.SourceToFlat
