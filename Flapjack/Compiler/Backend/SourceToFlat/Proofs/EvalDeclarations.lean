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

/-- The initial program prefix allocates global slots and installs the
reserved environment reference when the input stores are empty. -/
theorem evaluateCompileProg_prefix {C F : Type} (state : FlatSem.State C F)
    (next : NextIndices) (config : Config) (globalsEmpty : state.globals = []) (refsEmpty : state.refs = [])
    (positive : 0 < next.vidx - config.next.vidx) :
    FlatSem.evaluateDecs state [globAlloc next config, allocEnvRef] =
      ({ state with globals := some (.loc true 0) :: List.replicate (next.vidx - config.next.vidx - 1) none,
                    refs := [.refv (.conv none [])] }, none) := by
  rw [show [globAlloc next config, allocEnvRef] = [globAlloc next config] ++ [allocEnvRef] by rfl,
    FlatSem.evaluateDecs_append, evaluateDecs_globAlloc]
  simp only
  generalize countEq : next.vidx - config.next.vidx = count at *
  cases count with
  | zero => simp at positive
  | succ count =>
    simp [globalsEmpty, refsEmpty, allocEnvRef, FlatSem.evaluateDecs, FlatSem.evaluate, FlatSem.fixClock,
      FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat, FlatSem.doAppNumeric, FlatSem.doAppMemory,
      FlatSem.unitValue, storeAlloc, List.replicate_succ]

/-- Whole-program compilation runs its declaration body after allocating the
reserved reference and its global slots. This is an execution lemma; the body
simulation and initialization invariant are separate obligations. -/
theorem evaluateCompileProg_continue {C F : Type} (state : FlatSem.State C F)
    (config : Config) (decs : List Dec) (n : Nat) (next : NextIndices)
    (env : Environment) (gen : EnvironmentGenerationStore) (body : List FlatLang.Exp)
    (globalsEmpty : state.globals = []) (refsEmpty : state.refs = [])
    (compiled : compileDecs [] 1 { config.next with vidx := config.next.vidx + 1 } config.modEnv
      ⟨0, config.envs.next, .ln⟩ decs = (n, next, env, gen, body)) :
    FlatSem.evaluateDecs state (compileProg config decs).2 =
      FlatSem.evaluateDecs
        { state with globals := some (.loc true 0) :: List.replicate (next.vidx - config.next.vidx - 1) none,
                     refs := [.refv (.conv none [])] } body := by
  have indices := compileDecs_idxPrev [] 1 { config.next with vidx := config.next.vidx + 1 }
    config.modEnv ⟨0, config.envs.next, .ln⟩ decs n next env gen body compiled
  have positive : 0 < next.vidx - config.next.vidx := by
    simp only [idxPrev] at indices
    omega
  simp only [compileProg, compiled]
  rw [show globAlloc next config :: allocEnvRef :: body = [globAlloc next config, allocEnvRef] ++ body by rfl,
    FlatSem.evaluateDecs_append, evaluateCompileProg_prefix state next config globalsEmpty refsEmpty positive]

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
