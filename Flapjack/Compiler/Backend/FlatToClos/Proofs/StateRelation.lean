import Flapjack.Compiler.Backend.FlatToClos.Proofs.ValueRelation
import Flapjack.Compiler.Backend.Semantics.ClosSem.State
import Flapjack.Compiler.Backend.Semantics.FlatSem.Semantics
import Flapjack.Compiler.Backend.BackendProps.Pure
import Flapjack.Misc.ShiftSeq

/-! State relations for the proof-side flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendProps

/-- Correspondence between the flat list store and the closure finite map.
The proof-side finite-map representation and value relation remain under
cross-language review. -/
def StoreRel (source : Store FlatSem.Value) (target : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value)) : Prop :=
  ∀ index, match (source[index]? : Option (StoreValue FlatSem.Value)) with
  | none => target.lookup index = none
  | some (.refv value) => ∃ value', target.lookup index = some (.valueArray [value']) ∧ ValueRel value value'
  | some (.w8array bytes) => target.lookup index = some (.byteArray bytes)
  | some (.varray values) => ∃ values', target.lookup index = some (.valueArray values') ∧ List.Forall₂ ValueRel values values'
  | some (.thunk mode value) => ∃ value', target.lookup index = some (.thunk mode value') ∧ ValueRel value value'

/-- The unoptimized incremental program used in the installation relation. -/
def incCompileDecsProofSide (decs : List FlatLang.Exp) : ClosSem.Program :=
  (compileDecs decs ++ compileDecs [.con .none none []], [])

/-- Dynamic compilation uses the same downstream callback after translating
each flat program. Correspondence of these proof-side carriers remains open. -/
def installConfigRel {C : Type} (source : FlatSem.InstallConfig C)
    (oracle : ClosSem.CompileOracle C) (compiler : ClosSem.Compiler C) : Prop :=
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

/-- The source-shaped state relation, using the proof-side value and finite
map representations. It remains untagged pending correspondence review. -/
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
theorem lookup_ref {C F : Type} {source : FlatSem.State C F} {target : ClosSem.State C F}
    {index value} (related : StateRel source target)
    (found : storeLookup index source.refs = some (.refv value)) :
    ∃ value', target.refs.lookup index = some (.valueArray [value']) ∧ ValueRel value value' := by
  have store := related.2.2.2.1 index
  change source.refs[index]? = some (.refv value) at found
  simpa [found] using store

/-- A related byte array has exactly the same contents. -/
theorem lookup_byteArray {C F : Type} {source : FlatSem.State C F} {target : ClosSem.State C F}
    {index bytes} (related : StateRel source target)
    (found : storeLookup index source.refs = some (.w8array bytes)) :
    target.refs.lookup index = some (.byteArray bytes) := by
  have store := related.2.2.2.1 index
  change source.refs[index]? = some (.w8array bytes) at found
  simpa [found] using store

/-- A related value array has elementwise related contents. -/
theorem lookup_array {C F : Type} {source : FlatSem.State C F} {target : ClosSem.State C F}
    {index values} (related : StateRel source target)
    (found : storeLookup index source.refs = some (.varray values)) :
    ∃ values', target.refs.lookup index = some (.valueArray values') ∧ List.Forall₂ ValueRel values values' := by
  have store := related.2.2.2.1 index
  change source.refs[index]? = some (.varray values) at found
  simpa [found] using store

/-- A related thunk retains its mode and has a related payload. -/
theorem lookup_thunk {C F : Type} {source : FlatSem.State C F} {target : ClosSem.State C F}
    {index mode value} (related : StateRel source target)
    (found : storeLookup index source.refs = some (.thunk mode value)) :
    ∃ value', target.refs.lookup index = some (.thunk mode value') ∧ ValueRel value value' := by
  have store := related.2.2.2.1 index
  change source.refs[index]? = some (.thunk mode value) at found
  simpa [found] using store

/-- Decrementing both clocks preserves the state relation. -/
theorem stateRel_decClock {C F : Type} {source : FlatSem.State C F} {target : ClosSem.State C F}
    (related : StateRel source target) :
    StateRel (FlatSem.decClock source) (ClosSem.decClock 1 target) := by
  rcases related with ⟨maxApp, ffi, clock, store, globals, values, install⟩
  exact ⟨maxApp, ffi, by simp [FlatSem.decClock, ClosSem.decClock, clock], store, globals, values, install⟩

/-- Initial closure state used in the original flat-to-closure proof. -/
def initialStateProofSide {C F : Type} (interpreter : Bool) (ffi : HolFfiState F)
    (maxApp : Nat) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (oracle : ClosSem.CompileOracle C) (compiler : ClosSem.Compiler C) (clock : Nat) : ClosSem.State C F :=
  { ClosSem.initialState ffi maxApp code oracle compiler clock with
    globals := [some (if interpreter then .closure none [] [] 1 ClosInterp.closInterpreter else ClosSem.unitValue)] }

/-- Initial states satisfy the proof-side relation when the installation
configurations agree and at least unary calls are supported. -/
theorem initialStates_related {C F : Type} (interpreter : Bool) (ffi : HolFfiState F)
    (maxApp clock : Nat) (config : FlatSem.InstallConfig C)
    (oracle : ClosSem.CompileOracle C) (compiler : ClosSem.Compiler C)
    (positive : 0 < maxApp) (install : installConfigRel config oracle compiler) :
    StateRel (FlatSem.initialState ffi clock config)
      (initialStateProofSide interpreter ffi maxApp HolFiniteMapExact.empty oracle compiler clock) := by
  refine ⟨positive, rfl, rfl, ?_, by simp [initialStateProofSide, ClosSem.initialState], ?_, install⟩
  · intro index
    simp [FlatSem.initialState, initialStateProofSide, ClosSem.initialState, HolFiniteMapExact.empty]
  · exact .nil

end Flapjack.Compiler.Backend.FlatToClos
