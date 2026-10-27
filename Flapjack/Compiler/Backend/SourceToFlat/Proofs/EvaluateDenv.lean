import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvalOracleSimulation
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.MakeVarls
import Flapjack.EvaluateHOL.Definition
import Flapjack.HolRef

/-! Source-to-flat execution of the environment declaration. The flat
evaluator and factored relations still require HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL
open OracleInvariant

/-- Equality of value, constructor, and module domains for the compiler and
polymorphic source environments. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_domain_eq_def"]
def EnvDomainEq {α : Type} (compMap : Environment) (env : SemEnv α) : Prop :=
  nsDom compMap.v = nsDom env.v ∧ nsDomMod compMap.v = nsDomMod env.v ∧
    nsDom compMap.c = nsDom env.c ∧ nsDomMod compMap.c = nsDomMod env.c

/-- The compiler and source singleton bindings have the same value and module
domains, and their constructor namespaces are empty. -/
theorem envDomainEq_denv {α : Type} (name : VarN) (idx : Nat) (value : α) :
    EnvDomainEq { v := nsBind name (.glob .none idx) nsEmpty, c := nsEmpty }
      { v := nsSing name value, c := nsEmpty } := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext id
    apply propext
    cases id with
    | short key =>
      by_cases equal : key = name
      · subst key; simp [nsDom, nsLookup, nsBind, nsSing, nsEmpty]
      · simp [nsDom, nsLookup, nsBind, nsSing, nsEmpty, List.lookup, BEq.beq, equal]
    | long moduleName inner => simp [nsDom, nsLookup, nsBind, nsSing, nsEmpty]
  · funext path
    apply propext
    cases path <;> simp [nsDomMod, nsLookupMod, nsBind, nsSing, nsEmpty]
  · funext id
    apply propext
    cases id <;> simp [nsDom, nsLookup, nsEmpty]
  · funext path
    apply propext
    cases path <;> simp [nsDomMod, nsLookupMod, nsEmpty]

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

/-- The future compiler generation contains the environment inserted by the
current declaration. -/
theorem envGenFutureRel_insert_lookup {C : Type}
    (interp : Option (Value → Option (Config × C))) (gen : EnvironmentGenerationStore)
    (compMap : Environment) (evalState : Option EvalState) (config : Config)
    (future : envGenFutureRel interp
      { gen with next := gen.next + 1, envs := Flapjack.sptInsert gen.next compMap gen.envs } evalState)
    (next : srcOracNextCfg interp evalState = some config) :
    ∃ mapGen, Flapjack.sptLookup gen.generation config.envs.envGens = some mapGen ∧
      Flapjack.sptLookup gen.next mapGen = some compMap := by
  obtain ⟨mapGen, lookup, subspt⟩ := by simpa [envGenFutureRel, next] using future
  refine ⟨mapGen, lookup, ?_⟩
  exact (Flapjack.sptSubsptLookup _ _).mp subspt gen.next compMap
    (Flapjack.sptLookup_sptInsert_same _ _ _)

/-- The factored invariant is insensitive to the generation store beyond its
allocation-bound condition. -/
theorem factoredInvariant_changeGen {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen newGen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (valid : factoredInvariant interp transform gen genv idxs source flat)
    (newValid : envGenInv newGen) : factoredInvariant interp transform newGen genv idxs source flat := by
  obtain ⟨a, b, c, d, e, f, g, h, _, i⟩ := valid
  exact ⟨a, b, c, d, e, f, g, h, newValid, i⟩

/-- Filling the next blank global advances the current index block and
preserves the factored invariant. -/
theorem factoredInvariant_fillSlot {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F) (value : FlatSem.Value)
    (valid : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (fits : start.vidx + 1 ≤ finish.vidx) :
    factoredInvariant interp transform gen { genv with v := genv.v.set start.vidx (some value) }
      ({ start with vidx := start.vidx + 1 }, finish, other) source
      { flat with globals := flat.globals.set start.vidx (some value) } := by
  have empty := factoredInvariant_nextSlot_blank interp transform gen genv start finish other
    source flat valid fits
  obtain ⟨cOk, tysOk, states, range, invs, orac, globals, reserved, genInv, fin⟩ := valid
  have growth := GlobalGrowth.fillSlot genv start.vidx value (by simpa [globals] using empty)
  have nextStates := stateRel_after_global_growth genv _ growth source flat states
    (flat.globals.set start.vidx (some value))
  have nextRange := idxRangeRel_fillSlot interp genv source.nextTypeStamp source.nextExnStamp
    source.evalState start finish other value range (by simpa [globals] using empty) fits
  have nextReserved : evalRefInv
      ((flat.globals.set start.vidx (some value)).take 1) (flat.refs.take 1) := by
    obtain ⟨tail, old, refs, globalEq, refsEq⟩ := evalRefInv_heads flat reserved
    cases indexEq : start.vidx with
    | zero => simp [globalEq, indexEq] at empty
    | succ index => simp [evalRefInv, globalEq, refsEq]
  have nextInvs : srcOracInvs interp transform { genv with v := genv.v.set start.vidx (some value) }
      source.evalState := ⟨invs.1, srcOracEnvInvs_growth interp genv _ growth _ invs.2.1, invs.2.2⟩
  refine ⟨cOk, tysOk, nextStates, nextRange, nextInvs,
    orac, ?_, nextReserved, genInv, ?_⟩
  · simp [globals]
  · simpa using fin

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

/-- A singleton environment ID is related to the compiler's singleton global
binding when the global slot contains the related flat value. -/
theorem globalEnvInv_denv (genv : GlobalEnv) (name : VarN) (idx : Nat)
    (value : Value) (stored : FlatSem.Value) (bound : idx < genv.v.length)
    (slot : genv.v[idx]?.getD none = some stored) (related : ValueRel genv value stored) :
    GlobalEnvInv genv { v := nsBind name (.glob .none idx) nsEmpty, c := nsEmpty }
      (fun _ => False) { v := nsSing name value, c := nsEmpty } := by
  apply GlobalEnvInv.intro
  · intro id v _ lookup
    cases id with
    | short key =>
      by_cases keyEq : key = name
      · subst key
        simp [nsLookup, nsSing] at lookup
        subst v
        exact .intro _ _ _ _ idx stored .none (by simp [nsLookup, nsBind, nsEmpty]) bound slot related
      · simp [nsLookup, nsSing, List.lookup, BEq.beq, keyEq] at lookup
    | long moduleName inner => simp [nsLookup, nsSing] at lookup
  · intro id arity stamp lookup
    cases id <;> simp [nsLookup, nsEmpty] at lookup

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

/-- Under the declaration compiler's future-generation premise, `Denv`
preserves the complete factored simulation invariant. The factored value and
environment relations still require review against the original HOL ones. -/
theorem factoredInvariant_denv {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (env : SemEnv Value) (trace : List VarN) (n : Nat) (start finish : NextIndices)
    (other : Set (Nat × IndexKind)) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (name : VarN) (value : Value) (after : Option EvalState)
    (valid : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (declared : declareEnv source.evalState env = some (value, after))
    (envInv : GlobalEnvInv genv compMap (fun _ => False) env)
    (future : envGenFutureRel interp (compileDecs trace n start compMap gen [.denv name]).2.2.2.1
      source.evalState)
    (fits : start.vidx + 1 ≤ finish.vidx) :
    let stored : FlatSem.Value := .conv none
      [.litv (.intLit (gen.generation : Int)), .litv (.intLit (gen.next : Int))]
    factoredInvariant interp transform (compileDecs trace n start compMap gen [.denv name]).2.2.2.1
      { genv with v := genv.v.set start.vidx (some stored) }
      ((compileDecs trace n start compMap gen [.denv name]).2.1, finish, other)
      { source with evalState := after }
      { flat with globals := flat.globals.set start.vidx (some stored) } := by
  have ⟨_, _, _, _, _, oracle, _, _, genInv, _⟩ := valid
  cases sourceState : source.evalState with
  | none => simp [sourceState, declareEnv] at declared
  | some mode =>
    obtain ⟨_, state, _, modeEq⟩ := oracRel_some interp transform mode flat.evalConfig
      (by simpa [sourceState] using oracle)
    subst mode
    have genRel : envGenRel gen (some (.evalOracle state)) := by simpa [sourceState] using generation
    have decl : declareEnv (some (.evalOracle state)) env = some (value, after) := by
      simpa [sourceState] using declared
    cases found : state.envs[state.generation]? with
    | none => simp [declareEnv, found] at decl
    | some storedEnvs =>
      have genEq : gen.generation = state.generation := genRel.1
      have idEq : gen.next = storedEnvs.length := by simpa [found] using genRel.2.2
      have future' : envGenFutureRel interp
          { gen with next := gen.next + 1, envs := Flapjack.sptInsert gen.next compMap gen.envs }
          source.evalState := by simpa [compileDecs] using future
      have newMap : ∀ config, srcOracNextCfg interp (some (.evalOracle state)) = some config →
          ∃ mapGen compMap', Flapjack.sptLookup state.generation config.envs.envGens = some mapGen ∧
            Flapjack.sptLookup storedEnvs.length mapGen = some compMap' ∧
            GlobalEnvInv genv compMap' (fun _ => False) env := by
        intro config next
        obtain ⟨mapGen, lookup, mapLookup⟩ := envGenFutureRel_insert_lookup interp gen compMap
          source.evalState config future' (by simpa [sourceState] using next)
        exact ⟨mapGen, compMap, by simpa [genEq] using lookup, by simpa [idEq] using mapLookup, envInv⟩
      simp [declareEnv, found] at decl
      obtain ⟨_, afterEq⟩ := decl
      subst after
      have afterDecl := factoredInvariant_declareEnv interp transform gen genv (start, finish, other)
        source flat state env storedEnvs sourceState found valid newMap
      have newGenInv : envGenInv
          { gen with next := gen.next + 1, envs := Flapjack.sptInsert gen.next compMap gen.envs } := by
        simpa [compileDecs] using (compileDecs_envGenInv_core trace n start compMap gen [.denv name] genInv).1
      have changed := factoredInvariant_changeGen interp transform _ _ genv (start, finish, other)
        _ flat afterDecl newGenInv
      have final := factoredInvariant_fillSlot interp transform _ genv start finish other _ flat
        (.conv none [.litv (.intLit (gen.generation : Int)), .litv (.intLit (gen.next : Int))]) changed fits
      simpa [compileDecs] using final

/-- Successful `Denv` execution preserves the full factored invariant and
returns related environment IDs. This is not tagged as the HOL case until
the underlying factored relations and evaluator correspondence are reviewed. -/
theorem evaluateDenv_factored_complete {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (env : SemEnv Value) (trace : List VarN) (n : Nat) (start finish : NextIndices)
    (other : Set (Nat × IndexKind)) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (name : VarN) (value : Value) (after : Option EvalState)
    (valid : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (declared : declareEnv source.evalState env = some (value, after))
    (envInv : GlobalEnvInv genv compMap (fun _ => False) env)
    (future : envGenFutureRel interp (compileDecs trace n start compMap gen [.denv name]).2.2.2.1
      source.evalState)
    (fits : start.vidx + 1 ≤ finish.vidx) :
    let stored : FlatSem.Value := .conv none
      [.litv (.intLit (gen.generation : Int)), .litv (.intLit (gen.next : Int))]
    let newGen := (compileDecs trace n start compMap gen [.denv name]).2.2.2.1
    let newGenv := { genv with v := genv.v.set start.vidx (some stored) }
    let newSource := { source with evalState := after }
    let newFlat := { flat with globals := flat.globals.set start.vidx (some stored) }
    EvaluateHOL.evaluateDecs source env [.denv name] =
      (newSource, .val { v := nsSing name value, c := nsEmpty }) ∧
    FlatSem.evaluateDecs flat (compileDecs trace n start compMap gen [.denv name]).2.2.2.2 =
      (newFlat, none) ∧
    factoredInvariant interp transform newGen newGenv
      ((compileDecs trace n start compMap gen [.denv name]).2.1, finish, other) newSource newFlat ∧
    GlobalGrowth genv newGenv ∧ ValueRel newGenv value stored ∧ StateRel newGenv newSource newFlat ∧
    envGenRel newGen after ∧ oracForwardRel interp source.evalState after ∧
    GlobalEnvInv newGenv (compileDecs trace n start compMap gen [.denv name]).2.2.1
      (fun _ => False) { v := nsSing name value, c := nsEmpty } ∧
    EnvDomainEq (compileDecs trace n start compMap gen [.denv name]).2.2.1
      { v := nsSing name value, c := nsEmpty } := by
  have step := evaluateDenv_factored interp transform genv source flat env trace n start finish other
    compMap gen name value after valid generation declared fits
  have invariant := factoredInvariant_denv interp transform genv source flat env trace n start finish other
    compMap gen name value after valid generation declared envInv future fits
  have genRel : envGenRel (compileDecs trace n start compMap gen [.denv name]).2.2.2.1 after := by
    cases after with
    | none => trivial
    | some state => cases state <;> simpa [compileDecs, envGenRel] using step.2.2.2.2.2.2.1
  have ⟨_, _, _, _, _, _, globals, _, _, _⟩ := valid
  have blank := factoredInvariant_nextSlot_blank interp transform gen genv start finish other source flat valid fits
  have bound : start.vidx < genv.v.length := by
    rw [globals]
    exact (List.getElem?_eq_some_iff.mp blank).1
  have newEnvInv := globalEnvInv_denv
    { genv with v := genv.v.set start.vidx (some (.conv none
      [.litv (.intLit (gen.generation : Int)), .litv (.intLit (gen.next : Int))])) }
    name start.vidx value _ (by simpa using bound) (by simp [bound]) step.2.2.2.1
  exact ⟨step.1, step.2.1, invariant, step.2.2.1, step.2.2.2.1,
    step.2.2.2.2.1, genRel, step.2.2.2.2.2.2.2, by simpa [compileDecs] using newEnvInv,
    by simpa [compileDecs] using envDomainEq_denv name start.vidx value⟩

/-- A `Denv` evaluation that does not end in a source type error must have
successfully declared its environment. -/
theorem declareEnv_of_safeDenv {F : Type} (source : SemanticPrimitivesHOL.State F)
    (env : SemEnv Value) (name : VarN)
    (safe : ∀ next, EvaluateHOL.evaluateDecs source env [.denv name] ≠
      (next, .err (.abort .typeError))) :
    ∃ value after, declareEnv source.evalState env = some (value, after) := by
  cases declared : declareEnv source.evalState env with
  | none =>
    have bad : EvaluateHOL.evaluateDecs source env [.denv name] =
        (source, .err (.abort .typeError)) := by simp [EvaluateHOL.evaluateDecs, declared, EvaluateHOL.typeError]
    exact False.elim (safe source bad)
  | some pair =>
    obtain ⟨value, after⟩ := pair
    exact ⟨value, after, rfl⟩

/-- The `Denv` case under the source theorem's non-type-error premise. This
uses the factored relations and is not yet a reviewed HOL theorem port. -/
theorem evaluateDenv_factored_safe {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (env : SemEnv Value) (trace : List VarN) (n : Nat) (start finish : NextIndices)
    (other : Set (Nat × IndexKind)) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (name : VarN)
    (valid : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (safe : ∀ next, EvaluateHOL.evaluateDecs source env [.denv name] ≠
      (next, .err (.abort .typeError)))
    (envInv : GlobalEnvInv genv compMap (fun _ => False) env)
    (future : envGenFutureRel interp (compileDecs trace n start compMap gen [.denv name]).2.2.2.1
      source.evalState)
    (nextBound : idxPrev (compileDecs trace n start compMap gen [.denv name]).2.1 finish) :
    ∃ value after,
    let stored : FlatSem.Value := .conv none
      [.litv (.intLit (gen.generation : Int)), .litv (.intLit (gen.next : Int))]
    let newGen := (compileDecs trace n start compMap gen [.denv name]).2.2.2.1
    let newGenv := { genv with v := genv.v.set start.vidx (some stored) }
    let newSource := { source with evalState := after }
    let newFlat := { flat with globals := flat.globals.set start.vidx (some stored) }
    EvaluateHOL.evaluateDecs source env [.denv name] =
      (newSource, .val { v := nsSing name value, c := nsEmpty }) ∧
    FlatSem.evaluateDecs flat (compileDecs trace n start compMap gen [.denv name]).2.2.2.2 =
      (newFlat, none) ∧
    factoredInvariant interp transform newGen newGenv
      ((compileDecs trace n start compMap gen [.denv name]).2.1, finish, other) newSource newFlat ∧
    GlobalGrowth genv newGenv ∧ ValueRel newGenv value stored ∧ StateRel newGenv newSource newFlat ∧
    envGenRel newGen after ∧ oracForwardRel interp source.evalState after ∧
    GlobalEnvInv newGenv (compileDecs trace n start compMap gen [.denv name]).2.2.1
      (fun _ => False) { v := nsSing name value, c := nsEmpty } ∧
    EnvDomainEq (compileDecs trace n start compMap gen [.denv name]).2.2.1
      { v := nsSing name value, c := nsEmpty } := by
  obtain ⟨value, after, declared⟩ := declareEnv_of_safeDenv source env name safe
  have fits : start.vidx + 1 ≤ finish.vidx := by simpa [compileDecs] using nextBound.1
  exact ⟨value, after, evaluateDenv_factored_complete interp transform genv source flat env trace n
    start finish other compMap gen name value after valid generation declared envInv future fits⟩

/-- Source-result form of the `Denv` simulation. The flat state and global
environment are constructed by the proof, with no target evaluation assumed. -/
theorem evaluateDenv_factored_result {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (source sourceAfter : SemanticPrimitivesHOL.State F)
    (flat : FlatSem.State C F) (env : SemEnv Value)
    (sourceResult : Result (SemEnv Value) Value) (trace : List VarN) (n : Nat)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (compMap : Environment) (gen : EnvironmentGenerationStore) (name : VarN)
    (run : EvaluateHOL.evaluateDecs source env [.denv name] = (sourceAfter, sourceResult))
    (valid : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (safe : sourceResult ≠ .err (.abort .typeError))
    (envInv : GlobalEnvInv genv compMap (fun _ => False) env)
    (future : envGenFutureRel interp (compileDecs trace n start compMap gen [.denv name]).2.2.2.1
      source.evalState)
    (nextBound : idxPrev (compileDecs trace n start compMap gen [.denv name]).2.1 finish) :
    ∃ value after,
    let stored : FlatSem.Value := .conv none
      [.litv (.intLit (gen.generation : Int)), .litv (.intLit (gen.next : Int))]
    let newGen := (compileDecs trace n start compMap gen [.denv name]).2.2.2.1
    let newGenv := { genv with v := genv.v.set start.vidx (some stored) }
    let newFlat := { flat with globals := flat.globals.set start.vidx (some stored) }
    sourceAfter = { source with evalState := after } ∧
    sourceResult = .val { v := nsSing name value, c := nsEmpty } ∧
    FlatSem.evaluateDecs flat (compileDecs trace n start compMap gen [.denv name]).2.2.2.2 =
      (newFlat, none) ∧
    factoredInvariant interp transform newGen newGenv
      ((compileDecs trace n start compMap gen [.denv name]).2.1, finish, other) sourceAfter newFlat ∧
    GlobalGrowth genv newGenv ∧ ValueRel newGenv value stored ∧ StateRel newGenv sourceAfter newFlat ∧
    envGenRel newGen after ∧ oracForwardRel interp source.evalState after ∧
    GlobalEnvInv newGenv (compileDecs trace n start compMap gen [.denv name]).2.2.1
      (fun _ => False) { v := nsSing name value, c := nsEmpty } ∧
    EnvDomainEq (compileDecs trace n start compMap gen [.denv name]).2.2.1
      { v := nsSing name value, c := nsEmpty } := by
  have noError : ∀ next, EvaluateHOL.evaluateDecs source env [.denv name] ≠
      (next, .err (.abort .typeError)) := by
    intro next bad
    rw [run] at bad
    exact safe (congrArg Prod.snd bad)
  obtain ⟨value, after, sourceRun, flatRun, inv, growth, valueRel, states, genRel, forward, envRel, domain⟩ :=
    evaluateDenv_factored_safe interp transform genv source flat env trace n start finish other compMap gen
      name valid generation noError envInv future nextBound
  have eq := run.symm.trans sourceRun
  have stateEq := congrArg Prod.fst eq
  have resultEq := congrArg Prod.snd eq
  dsimp only at stateEq resultEq
  subst sourceAfter
  exact ⟨value, after, rfl, resultEq, flatRun, inv, growth, valueRel, states, genRel, forward, envRel, domain⟩

end Flapjack.Compiler.Backend.SourceToFlat
