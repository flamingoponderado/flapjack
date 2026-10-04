import Flapjack.Compiler.Backend.SourceToFlat.CompileDecs
import Flapjack.PrimTypesHOL

/-!
# `prim_src_config` closed-form replay

`scripts/hol-probes/source_to_flat_compile_probe.out` records HOL's evaluated
`backend$prim_src_config_eq`: running `compile_decs [] 1 empty_config.next
empty_env ARB prim_types_program` yields `next = <|vidx := 0; tidx := 2; eidx := 4|>`
and a constructor environment with the eight bindings below (in that order), an
empty value environment and no module bindings. The `ARB` generation store is
never inspected by the `Dexn`/`Dtype` clauses; any value replays the result.
This module evaluates the ported `compileDecs` on the ported `primTypesProgram`
and checks every component of that closed form.
-/

namespace Flapjack.Test.SourceToFlatPrimConfigParity

open Flapjack.Compiler.Backend.SourceToFlat Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString

def result := compileDecs [] 1 emptyConfig.next emptyEnv
  { next := 0, generation := 0, envs := .ln } PrimTypesHOL.primTypesProgram

def expectedCons : List (MlString × Nat × Option (Nat × List (Nat × Nat))) :=
  [(ofString "::", 0, some (1, [(0, 0), (0, 2)])),
   (ofString "[]", 0, some (1, [(0, 0), (0, 2)])),
   (ofString "True", 1, some (0, [(0, 0), (1, 0)])),
   (ofString "False", 0, some (0, [(0, 0), (1, 0)])),
   (ofString "Subscript", 3, none),
   (ofString "Div", 2, none),
   (ofString "Chr", 1, none),
   (ofString "Bind", 0, none)]

def checks : Bool :=
  let (n, next, env, _, decs) := result
  let consOk := match env.c with
    | .bind v m => v == expectedCons && m.isEmpty
  let valsOk := match env.v with
    | .bind v m => v.isEmpty && m.isEmpty
  n == 1 && next.vidx == 0 && next.tidx == 2 && next.eidx == 4 && consOk && valsOk &&
    decs.isEmpty

#guard checks

/-- Runtime entry for the test driver. -/
def runChecks : IO Bool := do
  if checks then
    IO.println "PASS source_to_flat compile_decs on prim_types_program matches prim_src_config_eq"
  else
    IO.println "FAIL source_to_flat compile_decs on prim_types_program vs prim_src_config_eq"
  pure checks

end Flapjack.Test.SourceToFlatPrimConfigParity
