import Flapjack.Compiler.Backend.SourceToFlat.CompileDecs
import Flapjack.PrimTypesHOL
import Flapjack.HolArb

/-!
# `backend$prim_src_config`

Counterpart of `cakeml/compiler/backend/backendScript.sml`'s
`prim_src_config_def` (lines 196-201): the source-to-flat configuration after
compiling the primitive-types program. HOL's `ARB` generation store is the shared
opaque `holArb`; `prim_types_program` has only `Dexn`/`Dtype` declarations, whose
`compile_decs` clauses return the store unchanged and never inspect it.
-/

namespace Flapjack.Compiler.Backend.Backend

open Flapjack.Compiler.Backend.SourceToFlat Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString

instance : Nonempty EnvironmentGenerationStore := ⟨{ next := 0, generation := 0, envs := .ln }⟩

/-- Exact HOL `prim_src_config_def`:
`let (_, next, env, _, _) = compile_decs [] 1 empty_config.next empty_env ARB
prim_types_program in empty_config with <| next := next; mod_env := env |>`. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "prim_src_config_def"]
noncomputable def primSrcConfig : SourceToFlat.Config :=
  let (_, next, env, _, _) := compileDecs [] 1 emptyConfig.next emptyEnv
    (holArb EnvironmentGenerationStore) PrimTypesHOL.primTypesProgram
  { emptyConfig with next := next, modEnv := env }

/-- Original `prim_src_config_eq` (`backendScript.sml:203`, `EVAL ``prim_src_config```):
the evaluated closed form, kernel-checked. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "prim_src_config_eq"]
theorem primSrcConfig_eq :
    primSrcConfig =
      { next := { vidx := 0, tidx := 2, eidx := 4 }
        modEnv :=
          { c := .bind
              [(ofString "::", 0, some (1, [(0, 0), (0, 2)])),
               (ofString "[]", 0, some (1, [(0, 0), (0, 2)])),
               (ofString "True", 1, some (0, [(0, 0), (1, 0)])),
               (ofString "False", 0, some (0, [(0, 0), (1, 0)])),
               (ofString "Subscript", 3, none),
               (ofString "Div", 2, none),
               (ofString "Chr", 1, none),
               (ofString "Bind", 0, none)] []
            v := .bind [] [] }
        patternCfg := { patHeuristic := 0 }
        envs := { next := 0, envGens := .ln } } := by
  simp [primSrcConfig, PrimTypesHOL.primTypesProgram, compileDecs, emptyConfig, emptyEnv,
    extendEnv, nsAppend, nsEmpty, nsSing, allocTags, allocTags1, lookupInc, nsBind, nsMap,
    Misc.Location.unknownLoc, FlatPattern.initConfig]
  refine ⟨?_, ?_⟩ <;> rfl

end Flapjack.Compiler.Backend.Backend
