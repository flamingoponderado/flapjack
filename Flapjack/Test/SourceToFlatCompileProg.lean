import Flapjack.Compiler.Backend.SourceToFlat.CompileProg

namespace Flapjack.Test.SourceToFlatCompileProg

open Flapjack.Compiler.Backend.SourceToFlat

-- A fresh compilation reserves the environment reference and records a generation.
example : (compileProg emptyConfig []).1.next.vidx = 1 := by simp [compileProg, compileDecs, emptyConfig]
example : (compileProg emptyConfig []).1.envs.next = 1 := by simp [compileProg, compileDecs, emptyConfig]
example : (compileProg emptyConfig []).2 = [globAlloc { emptyConfig.next with vidx := 1 }
    emptyConfig, allocEnvRef] := by simp [compileProg, compileDecs, emptyConfig]

-- Incremental compilation records the current environment at generation zero,
-- and does not allocate the initial environment reference a second time.
example : (incCompileProg (0, 0) emptyConfig []).1.envs.next = 1 := by simp [incCompileProg, compileDecs, lookupEnvId, emptyConfig]
example : lookupEnvId (0, 0) (incCompileProg (0, 0) emptyConfig []).1.envs = emptyEnv := by simp [incCompileProg, compileDecs, lookupEnvId, emptyConfig, sptLookup, extendEnv, emptyEnv, Flapjack.NamespaceHOL.nsEmpty, Flapjack.NamespaceHOL.nsAppend]
example : (incCompileProg (0, 0) emptyConfig []).2 =
    [globAlloc emptyConfig.next emptyConfig, storeEnvId 0 0] := by simp [incCompileProg, compileDecs, lookupEnvId, emptyConfig]

-- The original HOL incremental compiler emits these same two flat
-- declarations for an empty program after pattern compilation.
example : (incCompile (0, 0) emptyConfig []).2 =
    [globAlloc emptyConfig.next emptyConfig, storeEnvId 0 0] := by
  simp [incCompile, incCompileProg, compileDecs, lookupEnvId, emptyConfig, globAlloc,
    storeEnvId, envIdTuple, Flapjack.Compiler.Backend.FlatPattern.compileDec,
    Flapjack.Compiler.Backend.FlatPattern.compileExp, Flapjack.Compiler.Backend.FlatPattern.compileExps]

-- These complete outputs replay program_nonzero_next and
-- incremental_nonzero_next from source_to_flat_init_probe.out.
private def shiftedConfig : Config :=
  { emptyConfig with next := { emptyConfig.next with vidx := 4 } }

example :
    let (config, code) := compileProg shiftedConfig []
    (config.next.vidx, config.envs.next, code) =
      (5, 1, [.let_ omTra none (.app omTra (.globalVarAlloc 1) []) (.con omTra none []),
        .app .none (.globalVarInit 0) [.app .none (.src .opref) [.con .none none []]]]) := by
  simp [compileProg, compileDecs, shiftedConfig, emptyConfig, globAlloc, allocEnvRef]

example :
    let (config, code) := incCompileProg (3, 7) shiftedConfig []
    (config.next.vidx, config.envs.next, code) =
      (4, 1, [.let_ omTra none (.app omTra (.globalVarAlloc 0) []) (.con omTra none []),
        .let_ .none (some (.implode [114])) (.app .none (.globalVarLookup 0) [])
          (.app .none (.src .opassign) [.varLocal .none (.implode [114]),
            .con .none none [.lit .none (.intLit 0), .lit .none (.intLit 0)]])]) := by
  simp [incCompileProg, compileDecs, shiftedConfig, emptyConfig, lookupEnvId,
    globAlloc, storeEnvId, envIdTuple]

end Flapjack.Test.SourceToFlatCompileProg
