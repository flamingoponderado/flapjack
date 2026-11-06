import Flapjack.Compiler.Backend.BvlToBvi.Proofs.Refs
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.Names
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.AuxCode
import Flapjack.Compiler.Backend.BvlToBvi.SourceProgram
import Flapjack.Compiler.Backend.BvlToBvi.Stubs
import Flapjack.Compiler.Backend.BackendProps.StateCompiler

/-! Source-shaped state relation for BVL-to-BVI correctness. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value Ref)
open Flapjack.Compiler.Backend.BackendProps (stateCo stateCc)

/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_State {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness

/-- Canonical BVI reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness

/-- Source BVL and target BVI states are related by reference relocation,
global-array representation, compiler callbacks, installed stubs, code names,
and compiled function bodies. The source singleton-conversion theorem
identifies its last clause with `compileSingSource`. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "state_rel_def"
  (fmap_as_finite_support_relation := [State.refs, BviState.refs])]
def stateRel {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F) : Prop :=
  refsRel relocate source.refs target.refs ∧
  source.ffi = target.ffi ∧
  (∀ ptr, target.global = some ptr →
    (∀ key, source.refs.lookup key ≠ none → ptr ≠ relocate key) ∧
    ∃ size, target.refs.lookup ptr = some (.valueArray
      (.number (Int.ofNat (source.globals.length + 1)) ::
        (source.globals.map (fun value => (value.map (adjustBv relocate)).getD (.number 0)) ++
          List.replicate (size - (source.globals.length + 1)) (.number 0)))) ∧
      source.globals.length + 1 ≤ size) ∧
  source.clock = target.clock ∧
  target.compileOracle = stateCo compileIncSource source.compileOracle ∧
  source.compile = stateCc compileIncSource target.compile ∧
  sptLookup allocGlobalLocation target.code = some allocGlobalCode ∧
  sptLookup copyGlobalsLocation target.code = some copyGlobalsCode ∧
  sptLookup listLengthLocation target.code = some listLengthCode ∧
  sptLookup fromListByteLocation target.code = some fromListByteCode ∧
  sptLookup toListByteLocation target.code = some toListByteCode ∧
  sptLookup sumListLengthLocation target.code = some sumListLengthCode ∧
  sptLookup concatByteLocation target.code = some concatByteCode ∧
  namesOk source.code target.code source.compileOracle ∧
  ∀ name arity body, sptLookup name source.code = some (arity, body) →
    ∃ n, let (converted, aux, _) := compileSingSource n body
      sptLookup (bvlNumStubs + bvlToBviNamespaces * name) target.code =
        some (arity, BviLet.compileSing [] 0 converted) ∧
      auxCodeInstalled (appListAppend aux) target.code ∧
      BvlHandle.Proofs.handleOk [body]

/-- Matching clock decrements preserve the state relation. This is Flapjack
infrastructure derived from the source relation's unchanged fields. -/
theorem stateRel_decClock {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (related : stateRel relocate source target) (n : Nat) :
    stateRel relocate (BvlSem.decClock n source) (BviSem.decClock n target) := by
  simp only [stateRel, BvlSem.decClock, BviSem.decClock] at related ⊢
  exact ⟨related.1, related.2.1, related.2.2.1,
    congrArg (fun clock => clock - n) related.2.2.2.1, related.2.2.2.2⟩

/-- Related byte-array cells are unchanged. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "state_rel_FLOOKUP_byteArray"
  (fmap_as_finite_support_relation := [State.refs, BviState.refs])]
theorem stateRel_byteArray {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (mutableRef : Bool) (bytes : List (BitVec 8)) (key : Nat)
    (related : stateRel relocate source target)
    (lookup : source.refs.lookup key = some (.byteArray mutableRef bytes)) :
    target.refs.lookup (relocate key) = some (.byteArray mutableRef bytes) :=
  refsRel_byteArray related.1 lookup

/-- Related value-array cells contain relocated values. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "state_rel_FLOOKUP_valueArray"
  (fmap_as_finite_support_relation := [State.refs, BviState.refs])]
theorem stateRel_valueArray {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (key : Nat) (values : List Value) (related : stateRel relocate source target)
    (lookup : source.refs.lookup key = some (.valueArray values)) :
    target.refs.lookup (relocate key) = some (.valueArray (values.map (adjustBv relocate))) :=
  refsRel_valueArray related.1 lookup

/-- Related mutable-block cells are unchanged. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "state_rel_FLOOKUP_MutBlock"
  (fmap_as_finite_support_relation := [State.refs, BviState.refs])]
theorem stateRel_mutBlock {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (key tag : Nat) (flag : Bool) (before : List Value) (value : Value) (after : List Value)
    (related : stateRel relocate source target)
    (lookup : source.refs.lookup key = some (.mutBlock tag flag before value after)) :
    target.refs.lookup (relocate key) = some (.mutBlock tag flag before value after) :=
  refsRel_mutBlock related.1 lookup

/-- Related thunk cells relocate their stored value. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "state_rel_FLOOKUP_Thunk"
  (fmap_as_finite_support_relation := [State.refs, BviState.refs])]
theorem stateRel_thunk {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (key : Nat) (mode : AstHOL.ThunkMode) (value : Value) (related : stateRel relocate source target)
    (lookup : source.refs.lookup key = some (.thunk mode value)) :
    target.refs.lookup (relocate key) = some (.thunk mode (adjustBv relocate value)) :=
  refsRel_thunk related.1 lookup

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
