import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvalOracleSimulation
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.MakeVarls
import Flapjack.EvaluateHOL.Definition

/-! Source-to-flat execution of the environment declaration. The flat
evaluator and factored relations still require HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL
open OracleInvariant

/-- The next declaration's first global slot is blank whenever its one-slot
allocation fits in the current index block. -/
theorem factoredInvariant_nextSlot_blank {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (valid : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (fits : start.vidx + 1 ≤ finish.vidx) : flat.globals[start.vidx]? = some none := by
  have ⟨_, _, _, range, _, _, globals, _, _, final⟩ := valid
  obtain ⟨pre, post, slots, size⟩ := idxRangeRel_blank interp genv source.nextTypeStamp
    source.nextExnStamp source.evalState start finish other 1
    ⟨range, by simpa [globals] using final, by omega⟩
  rw [← globals, slots, ← size]
  simp

/-- Initializing a blank global slot preserves all previously initialized
slots, so existing factored value relations remain valid. -/
theorem GlobalGrowth.fillSlot (genv : GlobalEnv) (idx : Nat) (value : FlatSem.Value)
    (empty : genv.v[idx]? = some none) :
    GlobalGrowth genv { genv with v := genv.v.set idx (some value) } := by
  refine ⟨by simp, ?_, fun _ _ h => h, fun _ _ h => h⟩
  intro i old slot
  by_cases same : i = idx
  · subst i
    simp [empty] at slot
  · simpa [List.getElem?_set, Ne.symm same] using slot

/-- A compiled environment declaration initializes its allocated global slot
with the current generation and environment ID. -/
theorem evaluate_compileDenv {C F : Type} (state : FlatSem.State C F)
    (trace : List VarN) (n : Nat) (next : NextIndices) (compMap : Environment)
    (gen : EnvironmentGenerationStore) (name : VarN)
    (empty : state.globals[next.vidx]? = some none) :
    FlatSem.evaluateDecs state (compileDecs trace n next compMap gen [.denv name]).2.2.2.2 =
      ({ state with globals := state.globals.set next.vidx (some
        (.conv none [.litv (.intLit (gen.generation : Int)), .litv (.intLit (gen.next : Int))])) }, none) := by
  simp [compileDecs, FlatSem.evaluateDecs, FlatSem.evaluate, envIdTuple, FlatSem.fixClock,
    FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat, FlatSem.unitValue, empty]

/-- A successful source environment declaration and its compiled flat code
produce related environment IDs and preserve the factored state relation.
This local result does not assert the full declaration invariant. -/
theorem evaluateDenv_oracle {C F : Type}
    (interp : Option (Value → Option (Config × C))) (genv : GlobalEnv)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (state : EvalOracleState) (env : SemEnv Value) (trace : List VarN) (n : Nat)
    (next : NextIndices) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (name : VarN) (value : Value) (after : Option EvalState)
    (sourceState : source.evalState = some (.evalOracle state))
    (generation : envGenRel gen source.evalState)
    (declared : declareEnv source.evalState env = some (value, after))
    (related : StateRel genv source flat)
    (globals : genv.v = flat.globals)
    (empty : flat.globals[next.vidx]? = some none) :
    let stored : FlatSem.Value := .conv none
      [.litv (.intLit (gen.generation : Int)), .litv (.intLit (gen.next : Int))]
    EvaluateHOL.evaluateDecs source env [.denv name] =
      ({ source with evalState := after }, .val { v := nsSing name value, c := nsEmpty }) ∧
    FlatSem.evaluateDecs flat (compileDecs trace n next compMap gen [.denv name]).2.2.2.2 =
      ({ flat with globals := flat.globals.set next.vidx (some stored) }, none) ∧
    ValueRel genv value stored ∧
    StateRel genv { source with evalState := after }
      { flat with globals := flat.globals.set next.vidx (some stored) } ∧
    GlobalGrowth genv { genv with v := genv.v.set next.vidx (some stored) } ∧
    ValueRel { genv with v := genv.v.set next.vidx (some stored) } value stored ∧
    StateRel { genv with v := genv.v.set next.vidx (some stored) }
      { source with evalState := after }
      { flat with globals := flat.globals.set next.vidx (some stored) } ∧
    envGenRel { gen with next := gen.next + 1 } after ∧
    oracForwardRel interp source.evalState after := by
  have genRel : envGenRel gen (some (.evalOracle state)) := by simpa [sourceState] using generation
  have decl : declareEnv (some (.evalOracle state)) env = some (value, after) := by
    simpa [sourceState] using declared
  have nextGen := declareEnv_oracle_generation state gen env value after genRel decl
  have forward := declareEnv_oracle_forward interp state env value after decl
  let stored : FlatSem.Value := .conv none
    [.litv (.intLit (gen.generation : Int)), .litv (.intLit (gen.next : Int))]
  have growth := GlobalGrowth.fillSlot genv next.vidx stored (by simpa [globals] using empty)
  have stateAfter : StateRel genv { source with evalState := after }
      { flat with globals := flat.globals.set next.vidx (some stored) } := by
    cases related with
    | intro nonempty refs clock ffi => exact .intro _ _ nonempty refs clock ffi
  have valueRelated : ValueRel genv value stored := by
    cases found : state.envs[state.generation]? with
    | none => simp [declareEnv, found] at decl
    | some storedEnvs =>
      have genEq : gen.generation = state.generation := genRel.1
      have idEq : gen.next = storedEnvs.length := by simpa [found] using genRel.2.2
      simp [declareEnv, found] at decl
      obtain ⟨valueEq, _⟩ := decl
      subst value
      dsimp [stored, natToValue]
      rw [genEq, idEq]
      apply valueRel_tuple
      exact .cons (.literal genv _) (.cons (.literal genv _) .nil)
  refine ⟨?_, evaluate_compileDenv flat trace n next compMap gen name empty, valueRelated, stateAfter,
    growth, valueRel_growth _ _ growth _ _ valueRelated, stateRel_growth _ _ growth _ _ stateAfter,
    nextGen, ?_⟩
  · simp [EvaluateHOL.evaluateDecs, declared]
  · simpa [sourceState] using forward

/-- The factored compiler invariant supplies the oracle mode and blank slot
needed for the concrete `Denv` simulation. -/
theorem evaluateDenv_factored {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (env : SemEnv Value) (trace : List VarN) (n : Nat) (start finish : NextIndices)
    (other : Set (Nat × IndexKind)) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (name : VarN) (value : Value) (after : Option EvalState)
    (valid : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (declared : declareEnv source.evalState env = some (value, after))
    (fits : start.vidx + 1 ≤ finish.vidx) :
    let stored : FlatSem.Value := .conv none
      [.litv (.intLit (gen.generation : Int)), .litv (.intLit (gen.next : Int))]
    EvaluateHOL.evaluateDecs source env [.denv name] =
      ({ source with evalState := after }, .val { v := nsSing name value, c := nsEmpty }) ∧
    FlatSem.evaluateDecs flat (compileDecs trace n start compMap gen [.denv name]).2.2.2.2 =
      ({ flat with globals := flat.globals.set start.vidx (some stored) }, none) ∧
    GlobalGrowth genv { genv with v := genv.v.set start.vidx (some stored) } ∧
    ValueRel { genv with v := genv.v.set start.vidx (some stored) } value stored ∧
    StateRel { genv with v := genv.v.set start.vidx (some stored) }
      { source with evalState := after }
      { flat with globals := flat.globals.set start.vidx (some stored) } ∧
    idxRangeRel interp { genv with v := genv.v.set start.vidx (some stored) }
      source.nextTypeStamp source.nextExnStamp after
      ({ start with vidx := start.vidx + 1 }, finish, other) ∧
    envGenRel { gen with next := gen.next + 1 } after ∧
    oracForwardRel interp source.evalState after := by
  have ⟨_, _, related, range, _, oracle, globals, _, _, _⟩ := valid
  have empty := factoredInvariant_nextSlot_blank interp transform gen genv start finish other
    source flat valid fits
  cases sourceState : source.evalState with
  | none => simp [sourceState, declareEnv] at declared
  | some mode =>
    obtain ⟨_, state, _, modeEq⟩ := oracRel_some interp transform mode flat.evalConfig
      (by simpa [sourceState] using oracle)
    subst mode
    have result := evaluateDenv_oracle interp genv source flat state env trace n start compMap gen
      name value after sourceState generation declared related globals empty
    have cfgEq : srcOracNextCfg interp after = srcOracNextCfg interp source.evalState := by
      have decl : declareEnv (some (.evalOracle state)) env = some (value, after) := by
        simpa [sourceState] using declared
      cases found : state.envs[state.generation]? with
      | none => simp [declareEnv, found] at decl
      | some storedEnvs =>
        simp [declareEnv, found] at decl
        obtain ⟨_, afterEq⟩ := decl
        subst after
        simp [sourceState, srcOracNextCfg]
    have range' := idxRangeRel_fillSlot interp genv source.nextTypeStamp source.nextExnStamp
      source.evalState start finish other
      (.conv none [.litv (.intLit (gen.generation : Int)), .litv (.intLit (gen.next : Int))])
      range (by simpa [globals] using empty) fits
    have nextRange : idxRangeRel interp
        { genv with v := genv.v.set start.vidx (some (.conv none
          [.litv (.intLit (gen.generation : Int)), .litv (.intLit (gen.next : Int))])) }
        source.nextTypeStamp source.nextExnStamp after
        ({ start with vidx := start.vidx + 1 }, finish, other) := by
      simpa [idxRangeRel, cfgEq] using range'
    exact ⟨result.1, result.2.1, result.2.2.2.2.1, result.2.2.2.2.2.1,
      result.2.2.2.2.2.2.1, nextRange, result.2.2.2.2.2.2.2.1,
      by simpa [sourceState] using result.2.2.2.2.2.2.2.2⟩

end Flapjack.Compiler.Backend.SourceToFlat
