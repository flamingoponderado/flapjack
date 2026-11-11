module

public import Flapjack.Compiler.Backend.FlatToClos.Proofs.ValueRelation
public import Flapjack.Compiler.Backend.Semantics.ClosSem.State
public import Flapjack.Compiler.Backend.Semantics.FlatSem.Semantics
public import Flapjack.Compiler.Backend.BackendProps.Pure
public import Flapjack.Misc.ShiftSeq
public import Flapjack.Misc.ListEl

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! State relations for the proof-side flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendProps

private def maptoBroadlookup {α β : Type} (f : HolFiniteMapExact α β) : α → Option β := f.lookup
private def mapofBroad {α β : Type} (lookup : α → Option β)
    (support : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact α β :=
  ⟨lookup, support⟩

/-- The canonical closure-reference map roundtrips through its lookup view. -/
theorem holFmapAsFiniteSupportParamWitness_StoreRel_target
    (target : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value)) :
    mapofBroad (maptoBroadlookup target) target.finiteSupport = target := by
  cases target
  rfl

/-- Correspondence between the flat list store and the closure finite map. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "store_rel_def"
  (fmap_as_finite_support_parameters := [target])]
def StoreRel (source : Store FlatSem.Value) (target : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value)) : Prop :=
  ∀ index, match (source[index]? : Option (StoreValue FlatSem.Value)) with
  | none => target.lookup index = none
  | some (.refv value) => ∃ value', target.lookup index = some (.valueArray [value']) ∧ ValueRel value value'
  | some (.w8array bytes) => target.lookup index = some (.byteArray bytes)
  | some (.varray values) => ∃ values', target.lookup index = some (.valueArray values') ∧ List.Forall₂ ValueRel values values'
  | some (.thunk mode value) => ∃ value', target.lookup index = some (.thunk mode value') ∧ ValueRel value value'

/-- Optional indexing in `StoreRel` has the source's bound-and-`EL` shape. -/
theorem storeRel_hol_cases (source : Store FlatSem.Value)
    (target : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value)) :
    StoreRel source target ↔ ∀ index,
      if source.length ≤ index then target.lookup index = none
      else match @Flapjack.holEl (StoreValue FlatSem.Value) ⟨.w8array []⟩ index source with
        | .refv value => ∃ value', target.lookup index = some (.valueArray [value']) ∧ ValueRel value value'
        | .w8array bytes => target.lookup index = some (.byteArray bytes)
        | .varray values => ∃ values', target.lookup index = some (.valueArray values') ∧ List.Forall₂ ValueRel values values'
        | .thunk mode value => ∃ value', target.lookup index = some (.thunk mode value') ∧ ValueRel value value' := by
  letI : Nonempty (StoreValue FlatSem.Value) := ⟨.w8array []⟩
  unfold StoreRel
  constructor <;> intro related index
  all_goals
    by_cases bound : index < source.length
    · cases entry : source[index]'bound <;>
        simpa [Nat.not_le_of_gt bound, List.getElem?_eq_getElem bound,
          Flapjack.holEl_eq_getElem index source bound, entry] using related index
    · have outside : source.length ≤ index := Nat.le_of_not_gt bound
      simpa [outside, List.getElem?_eq_none outside] using related index

/-- The unoptimized incremental program used in the proof's installation
relation. The executed incremental compiler additionally inserts the interpreter. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "inc_compile_decs'_def"]
def incCompileDecsProofSide {α : Type} (decs : List FlatLang.Exp) : List ClosLang.Exp × List α :=
  (compileDecs decs ++ compileDecs [.con .none none []], [])

/-- Dynamic compilation uses the same downstream callback after translating
each flat program; oracle and compiler payload types are independent. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "install_config_rel'_def"]
def installConfigRel {C OraclePayload CompilerPayload : Type} (source : FlatSem.InstallConfig C)
    (oracle : Nat → C × (List ClosLang.Exp × List OraclePayload))
    (compiler : C → (List ClosLang.Exp × List CompilerPayload) →
      Option (List (BitVec 8) × List (BitVec 64) × C)) : Prop :=
  (∀ index, FlatProps.noMatDecs (source.compileOracle index).2 = true) ∧
  oracle = pureCo incCompileDecsProofSide ∘ source.compileOracle ∧
  source.compile = pureCc incCompileDecsProofSide compiler

/-- Advancing both compilation oracles preserves the installation relation.
This is proof-side infrastructure; correspondence of its carriers is open. -/
theorem installConfigRel_shift {C : Type} (source : FlatSem.InstallConfig C)
    (oracle : ClosSem.CompileOracle C) (compiler : ClosSem.Compiler C)
    (related : installConfigRel source oracle compiler) (offset : Nat) :
    installConfigRel { source with compileOracle := Flapjack.holShiftSeq offset source.compileOracle }
      (Flapjack.holShiftSeq offset oracle) compiler := by
  rcases related with ⟨safe, oracleEq, compileEq⟩
  refine ⟨?_, ?_, compileEq⟩
  · intro index
    exact safe (index + offset)
  · rw [oracleEq]
    rfl

/-- Relation on optional global slots. -/
def optionalValueRel : Option FlatSem.Value → Option ClosSem.Value → Prop
  | none, none => True
  | some source, some target => ValueRel source target
  | _, _ => False

/-- The closure state's finite-map fields roundtrip through their lookup view. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- The source state relation for flat-to-closure evaluation. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "state_rel_def"
  (fmap_as_finite_support := [refs, code])]
def StateRel {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F) : Prop :=
  1 ≤ target.maxApp ∧ source.ffi = target.ffi ∧ source.clock = target.clock ∧
  StoreRel source.refs target.refs ∧ target.globals ≠ [] ∧
  List.Forall₂ optionalValueRel source.globals target.globals.tail ∧
  installConfigRel source.evalConfig target.compileOracle target.compile

/-- Advance the related source and closure installation oracles without
changing the rest of either state. -/
theorem stateRel_shiftInstall {C F : Type} {source : FlatSem.State C F} {target : ClosSem.State C F}
    (related : StateRel source target) (offset : Nat) :
    StateRel { source with evalConfig :=
      { source.evalConfig with compileOracle := Flapjack.holShiftSeq offset source.evalConfig.compileOracle } }
      { target with compileOracle := Flapjack.holShiftSeq offset target.compileOracle } := by
  rcases related with ⟨maxApp, ffi, clock, store, globals, values, install⟩
  exact ⟨maxApp, ffi, clock, store, globals, values, installConfigRel_shift _ _ _ install offset⟩

/-- A related scalar reference is represented by a singleton value array. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "lookup_refv"
  (fmap_as_finite_support := [refs, code])]
theorem lookup_ref {C F : Type} {source : FlatSem.State C F} {target : ClosSem.State C F}
    {index value} (related : StateRel source target)
    (found : storeLookup index source.refs = some (.refv value)) :
    ∃ value', target.refs.lookup index = some (.valueArray [value']) ∧ ValueRel value value' := by
  have store := related.2.2.2.1 index
  change source.refs[index]? = some (.refv value) at found
  simpa [found] using store

/-- A related byte array has exactly the same contents. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "lookup_byte_array"
  (fmap_as_finite_support := [refs, code])]
theorem lookup_byteArray {C F : Type} {source : FlatSem.State C F} {target : ClosSem.State C F}
    {index bytes} (related : StateRel source target)
    (found : storeLookup index source.refs = some (.w8array bytes)) :
    target.refs.lookup index = some (.byteArray bytes) := by
  have store := related.2.2.2.1 index
  change source.refs[index]? = some (.w8array bytes) at found
  simpa [found] using store

/-- A related value array has elementwise related contents. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "lookup_array"
  (fmap_as_finite_support := [refs, code])]
theorem lookup_array {C F : Type} {source : FlatSem.State C F} {target : ClosSem.State C F}
    {index values} (related : StateRel source target)
    (found : storeLookup index source.refs = some (.varray values)) :
    ∃ values', target.refs.lookup index = some (.valueArray values') ∧ List.Forall₂ ValueRel values values' := by
  have store := related.2.2.2.1 index
  change source.refs[index]? = some (.varray values) at found
  simpa [found] using store

/-- A related thunk retains its mode and has a related payload. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "lookup_thunk"
  (fmap_as_finite_support := [refs, code])]
theorem lookup_thunk {C F : Type} {source : FlatSem.State C F} {target : ClosSem.State C F}
    {index mode value} (related : StateRel source target)
    (found : storeLookup index source.refs = some (.thunk mode value)) :
    ∃ value', target.refs.lookup index = some (.thunk mode value') ∧ ValueRel value value' := by
  have store := related.2.2.2.1 index
  change source.refs[index]? = some (.thunk mode value) at found
  simpa [found] using store

/-- Related states have equal clocks. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "state_rel_IMP_clock"
  (fmap_as_finite_support := [refs, code])]
theorem stateRel_impClock {C F : Type} {source : FlatSem.State C F} {target : ClosSem.State C F}
    (related : StateRel source target) : source.clock = target.clock :=
  related.2.2.1

/-- Decrementing both clocks preserves the state relation. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "state_rel_dec_clock"
  (fmap_as_finite_support := [refs, code])]
theorem stateRel_decClock {C F : Type} {source : FlatSem.State C F} {target : ClosSem.State C F}
    (related : StateRel source target) :
    source.clock = target.clock ∧ StateRel (FlatSem.decClock source) (ClosSem.decClock 1 target) := by
  rcases related with ⟨maxApp, ffi, clock, store, globals, values, install⟩
  exact ⟨clock, maxApp, ffi, by simp [FlatSem.decClock, ClosSem.decClock, clock], store, globals, values, install⟩

/-- The closure state roundtrips through its canonical finite-map view. -/
theorem holFmapAsFiniteSupportRelationWitness_State {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportRelationWitness_State

/-- Initial closure state used in the original flat-to-closure proof. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "initial_state'_def"
  (fmap_as_finite_support_relation := [State.refs, State.code, code])]
def initialStateProofSide {C F : Type} (interpreter : Bool) (ffi : HolFfiState F)
    (maxApp : Nat) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (oracle : ClosSem.CompileOracle C) (compiler : ClosSem.Compiler C) (clock : Nat) : ClosSem.State C F :=
  { ClosSem.initialState ffi maxApp code oracle compiler clock with
    globals := [some (if interpreter then .closure none [] [] 1 ClosInterp.closInterpreter else ClosSem.unitValue)] }

/-- Initial states satisfy the proof-side relation when the installation
configurations agree and at least unary calls are supported. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "state_rel_initial_state"
  (fmap_as_finite_support := [refs, code])]
theorem initialStates_related {C F : Type} (maxApp : Nat) (config : FlatSem.InstallConfig C)
    (oracle : ClosSem.CompileOracle C) (compiler : ClosSem.Compiler C)
    (ffi : HolFfiState F) (clock : Nat) (interpreter : Bool)
    (premises : 0 < maxApp ∧ installConfigRel config oracle compiler) :
    StateRel (FlatSem.initialState ffi clock config)
      (initialStateProofSide interpreter ffi maxApp HolFiniteMapExact.empty oracle compiler clock : ClosSem.State C F) := by
  obtain ⟨positive, install⟩ := premises
  refine ⟨positive, rfl, rfl, ?_, by simp [initialStateProofSide, ClosSem.initialState], ?_, install⟩
  · intro index
    simp [FlatSem.initialState, initialStateProofSide, ClosSem.initialState, HolFiniteMapExact.empty]
  · exact .nil

end Flapjack.Compiler.Backend.FlatToClos
