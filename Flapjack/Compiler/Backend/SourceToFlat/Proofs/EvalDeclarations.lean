import Flapjack.Compiler.Backend.FlatProps.EvaluateDecs
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.StoreEnvId

/-! Execution of the generated incremental declaration sequence. The flat
evaluator and factored relations remain subject to HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL
open OracleInvariant

/-- The incremental allocation declaration appends the exact number of
blank global slots and returns normally. -/
theorem evaluateDecs_globAlloc {C F : Type} (state : FlatSem.State C F)
    (next : NextIndices) (config : Config) :
    FlatSem.evaluateDecs state [globAlloc next config] =
      ({ state with globals := state.globals ++ List.replicate (next.vidx - config.next.vidx) none }, none) := by
  simp [FlatSem.evaluateDecs, FlatSem.evaluate, globAlloc, FlatSem.fixClock,
    FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat, FlatSem.unitValue]

/-- Once the declaration body succeeds, the incremental sequence continues
exactly with the generated environment-ID store. -/
theorem evaluateIncCompileProg_continue {C F : Type} (state middle : FlatSem.State C F)
    (envId : Nat × Nat) (config : Config) (decs : List Dec) (n : Nat) (next : NextIndices)
    (env : Environment) (gen : EnvironmentGenerationStore) (body : List FlatLang.Exp)
    (compiled : compileDecs [] 1 config.next (lookupEnvId envId config.envs)
      ⟨0, config.envs.next, .ln⟩ decs = (n, next, env, gen, body))
    (bodyRun : FlatSem.evaluateDecs
      { state with globals := state.globals ++ List.replicate (next.vidx - config.next.vidx) none } body =
      (middle, none)) :
    FlatSem.evaluateDecs state (incCompileProg envId config decs).2 =
      FlatSem.evaluateDecs middle [storeEnvId gen.generation gen.next] := by
  simp only [incCompileProg, compiled]
  rw [← List.singleton_append, FlatSem.evaluateDecs_append, evaluateDecs_globAlloc]
  simp only
  rw [FlatSem.evaluateDecs_append, bodyRun]

/-- When the compiled declaration body succeeds, the incremental sequence
allocates globals, runs that body, and stores its generation and next ID.
The body execution is the declaration induction hypothesis, not a claim of
the whole original compiler-correctness theorem. -/
theorem evaluateIncCompileProg_success {C F : Type} (state middle : FlatSem.State C F)
    (envId : Nat × Nat) (config : Config) (decs : List Dec) (n : Nat) (next : NextIndices)
    (env : Environment) (gen : EnvironmentGenerationStore) (body : List FlatLang.Exp)
    (compiled : compileDecs [] 1 config.next (lookupEnvId envId config.envs)
      ⟨0, config.envs.next, .ln⟩ decs = (n, next, env, gen, body))
    (bodyRun : FlatSem.evaluateDecs
      { state with globals := state.globals ++ List.replicate (next.vidx - config.next.vidx) none } body =
      (middle, none))
    (reserved : evalRefInv (middle.globals.take 1) (middle.refs.take 1)) :
    FlatSem.evaluateDecs state (incCompileProg envId config decs).2 =
      ({ middle with refs := .refv (.conv none
        [.litv (.intLit (gen.generation : Int)), .litv (.intLit (gen.next : Int))]) :: middle.refs.tail }, none) := by
  obtain ⟨globals, old, refs, globalEq, refsEq⟩ := evalRefInv_heads middle reserved
  simp only [incCompileProg, compiled]
  rw [← List.singleton_append, FlatSem.evaluateDecs_append, evaluateDecs_globAlloc]
  simp only
  rw [FlatSem.evaluateDecs_append, bodyRun]
  simpa [refsEq] using evaluateStoreEnvId middle gen.generation gen.next globals old refs globalEq refsEq

/-- A declaration-body error stops the incremental sequence before the ID
store, preserving the exact error and state returned by the body. -/
theorem evaluateIncCompileProg_error {C F : Type} (state middle : FlatSem.State C F)
    (envId : Nat × Nat) (config : Config) (decs : List Dec) (n : Nat) (next : NextIndices)
    (env : Environment) (gen : EnvironmentGenerationStore) (body : List FlatLang.Exp)
    (error : ErrorResult FlatSem.Value)
    (compiled : compileDecs [] 1 config.next (lookupEnvId envId config.envs)
      ⟨0, config.envs.next, .ln⟩ decs = (n, next, env, gen, body))
    (bodyRun : FlatSem.evaluateDecs
      { state with globals := state.globals ++ List.replicate (next.vidx - config.next.vidx) none } body =
      (middle, some error)) :
    FlatSem.evaluateDecs state (incCompileProg envId config decs).2 = (middle, some error) := by
  simp only [incCompileProg, compiled]
  rw [← List.singleton_append, FlatSem.evaluateDecs_append, evaluateDecs_globAlloc]
  simp only
  rw [FlatSem.evaluateDecs_append, bodyRun]

end Flapjack.Compiler.Backend.SourceToFlat
