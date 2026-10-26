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

end Flapjack.Test.SourceToFlatCompileProg
