import Flapjack.NamespaceHOL
import Flapjack.Basis.Pure.MlString
import Flapjack.Misc.Sptree
import Flapjack.Compiler.Backend.BackendCommon.Trace
import Flapjack.Compiler.Backend.FlatPattern.Config

namespace Flapjack.Compiler.Backend.SourceToFlat

open Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString

/-- Literal source variable-name alternatives, preserving trace and byte names. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "var_name"]
inductive VarName where
  | glob : BackendCommon.Tra → Nat → VarName
  | localName : BackendCommon.Tra → MlString → VarName

/-- Source ast modN/conN/varN are all mlstring (astScript29/32/35).
flatLang ctor_id is num, and type_group_id is (num # (num # num) list) option
(flatLangScript45/48). The concrete namespace value carriers retain those aliases. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "environment"]
structure Environment where
  c : Namespace MlString MlString (Nat × Option (Nat × List (Nat × Nat)))
  v : Namespace MlString MlString VarName

/-- Generation-indexed source environments; num_map is the original spt tree. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "environment_generation_store"]
structure EnvironmentGenerationStore where
  next : Nat
  generation : Nat
  envs : Spt Environment

/-- Original two-level generation map, with no finite-map carrier replacement. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "environment_store"]
structure EnvironmentStore where
  next : Nat
  envGens : Spt (Spt Environment)

/-- All three independent source indices. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "next_indices"]
structure NextIndices where
  vidx : Nat
  tidx : Nat
  eidx : Nat

/-- Complete source-to-flat configuration; every field has its concrete source carrier. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "config"]
structure Config where
  next : NextIndices
  modEnv : Environment
  patternCfg : FlatPattern.Config
  envs : EnvironmentStore

end Flapjack.Compiler.Backend.SourceToFlat
