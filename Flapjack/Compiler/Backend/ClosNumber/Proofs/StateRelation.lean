import Flapjack.Misc.List
import Flapjack.Misc.Option.Rel
import Flapjack.Compiler.Backend.ClosNumber.Proofs.ValueRelation
import Flapjack.Compiler.Backend.Semantics.ClosSem.State
import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyMemory
import Flapjack.Compiler.Backend.BackendProps.StateCompiler

/-! State relation for the closure-numbering simulation. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.BackendProps

/-- Relate closure reference payloads using the numbering value relation. -/
def RefRel (maxApp : Nat) : Ref Value → Ref Value → Prop
  | .valueArray left, .valueArray right => List.Forall₂ (ValueRel maxApp) left right
  | .byteArray left, .byteArray right => left = right
  | .thunk leftMode left, .thunk rightMode right => leftMode = rightMode ∧ ValueRel maxApp left right
  | _, _ => False

/-- Pointwise option lifting states the same domain equality and related
lookup results as HOL's finite-map relation. This helper has no separate HOL
declaration. -/
theorem optionRel_lookup_iff {K A B : Type} (relation : A → B → Prop)
    (left : HolFiniteMapExact K A) (right : HolFiniteMapExact K B) :
    (∀ key, optionRel relation (left.lookup key) (right.lookup key)) ↔
      (∀ key, (∃ value, left.lookup key = some value) ↔
        ∃ value, right.lookup key = some value) ∧
      (∀ key a b, left.lookup key = some a → right.lookup key = some b → relation a b) := by
  constructor
  · intro h
    constructor
    · intro key
      specialize h key
      cases leftEq : left.lookup key <;> cases rightEq : right.lookup key <;>
        simp_all [optionRel]
    · intro key a b ha hb
      simpa [ha, hb, optionRel] using h key
  · intro ⟨domains, entries⟩ key
    have same := domains key
    cases leftEq : left.lookup key with
    | none =>
      cases rightEq : right.lookup key with
      | none => trivial
      | some b => simp [leftEq, rightEq] at same
    | some a =>
      cases rightEq : right.lookup key with
      | none => simp [leftEq, rightEq] at same
      | some b => exact entries key a b leftEq rightEq

namespace StateRelationPort
/-- The closure state retains both finite maps through the canonical view. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end StateRelationPort

/-- Numbering state relation over canonical finite-support maps. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "state_rel_def"
  (fmap_as_finite_support := [refs, code])]
def StateRel {C F : Type} (source : State (Nat × C) F) (target : State C F) : Prop :=
  source.clock = target.clock ∧ source.ffi = target.ffi ∧ target.maxApp = source.maxApp ∧
  source.compile = stateCc (ignoreTable compileInc) target.compile ∧
  target.compileOracle = stateCo (ignoreTable compileInc) source.compileOracle ∧
  (∀ key, optionRel (RefRel source.maxApp) (source.refs.lookup key) (target.refs.lookup key)) ∧
  List.Forall₂ (optionRel (ValueRel source.maxApp)) source.globals target.globals ∧
  (∀ index, (source.compileOracle index).2.2 = [] ∧
    ¬ ClosProps.containsAppSome source.maxApp (source.compileOracle index).2.1) ∧
  source.code = HolFiniteMapExact.empty ∧ target.code = HolFiniteMapExact.empty

/-- Related states expose identical clocks and maximum application arities. -/
theorem stateRel_clock_maxApp {C F : Type} {source : State (Nat × C) F} {target : State C F}
    (related : StateRel source target) : source.clock = target.clock ∧ source.maxApp = target.maxApp :=
  ⟨related.1, related.2.2.1.symm⟩

/-- Updating both clocks preserves the numbering state relation. -/
theorem stateRel_withClock {C F : Type} {source : State (Nat × C) F} {target : State C F}
    (clock : Nat) (related : StateRel source target) :
    StateRel { source with clock := clock } { target with clock := clock } := by
  simpa [StateRel] using related.2

/-- Replacing both global stores with pointwise-related stores preserves all
    other components of the numbering state relation. -/
theorem stateRel_withGlobals {C F : Type} {source : State (Nat × C) F} {target : State C F}
    (sourceGlobals targetGlobals : List (Option Value)) (related : StateRel source target)
    (globalsRel : List.Forall₂ (optionRel (ValueRel source.maxApp)) sourceGlobals targetGlobals) :
    StateRel { source with globals := sourceGlobals } { target with globals := targetGlobals } := by
  rcases related with ⟨clock, ffi, maxApp, compiler, oracle, refs, globals, safe, sourceCode, targetCode⟩
  exact ⟨clock, ffi, maxApp, compiler, oracle, refs, globalsRel, safe, sourceCode, targetCode⟩

/-- Lookup distinguishes missing entries and present entries while lifting the
    element relation through the resulting option. -/
theorem forall₂_getGlobal {α β : Type} {relation : α → β → Prop} {left : List α} {right : List β}
    (related : List.Forall₂ relation left right) (index : Nat) :
    optionRel relation (getGlobal index left) (getGlobal index right) := by
  induction related generalizing index with
  | nil => simp [getGlobal, optionRel]
  | cons head tail ih =>
    cases index with
    | zero => simpa [getGlobal, optionRel] using head
    | succ index => simpa [getGlobal] using ih index

/-- Reading corresponding global slots preserves both uninitialized and
    out-of-range behavior, and relates every initialized value. -/
theorem stateRel_getGlobal {C F : Type} {source : State (Nat × C) F} {target : State C F}
    (related : StateRel source target) (index : Nat) :
    optionRel (ValueRel source.maxApp) (getGlobal index source.globals).join
      (getGlobal index target.globals).join := by
  have h := forall₂_getGlobal related.2.2.2.2.2.2.1 index
  cases left : getGlobal index source.globals with
  | none =>
    cases right : getGlobal index target.globals <;> simp_all [optionRel]
  | some leftSlot =>
    cases right : getGlobal index target.globals with
    | none => simp_all [optionRel]
    | some rightSlot =>
      cases leftSlot <;> cases rightSlot <;> simp_all [optionRel]

/-- Appending the same number of uninitialized global slots preserves the
    state relation. -/
theorem stateRel_allocGlobals {C F : Type} {source : State (Nat × C) F} {target : State C F}
    (count : Nat) (related : StateRel source target) :
    StateRel { source with globals := source.globals ++ List.replicate count none }
      { target with globals := target.globals ++ List.replicate count none } := by
  have blanks : List.Forall₂ (optionRel (ValueRel source.maxApp))
      (List.replicate count none) (List.replicate count none) := by
    induction count with
    | zero => exact .nil
    | succ n ih => exact .cons trivial ih
  exact stateRel_withGlobals _ _ related (List.rel_append related.2.2.2.2.2.2.1 blanks)

/-- Writing related references at the same address preserves the reference
    store and the rest of the numbering state relation. -/
theorem stateRel_updateRefs {C F : Type} {source : State (Nat × C) F} {target : State C F}
    (index : Nat) (left right : Ref Value) (related : StateRel source target)
    (refRel : RefRel source.maxApp left right) :
    StateRel { source with refs := source.refs.updateEq (index, left) }
      { target with refs := target.refs.updateEq (index, right) } := by
  rcases related with ⟨clock, ffi, maxApp, compiler, oracle, refs, globals, safe, sourceCode, targetCode⟩
  refine ⟨clock, ffi, maxApp, compiler, oracle, ?_, globals, safe, sourceCode, targetCode⟩
  intro key
  by_cases equal : key = index
  · simp [HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL, equal, optionRel, refRel]
  · simpa [HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL, equal] using refs key

/-- Replacing both FFI states by the same state preserves the relation. -/
theorem stateRel_withFfi {C F : Type} {source : State (Nat × C) F} {target : State C F}
    (ffi : Flapjack.HolFfiState F) (related : StateRel source target) :
    StateRel { source with ffi := ffi } { target with ffi := ffi } := by
  rcases related with ⟨clock, oldFfi, maxApp, compiler, oracle, refs, globals, safe, sourceCode, targetCode⟩
  exact ⟨clock, rfl, maxApp, compiler, oracle, refs, globals, safe, sourceCode, targetCode⟩

/-- Related reference stores agree on the presence and contents of a byte
    array at any address. -/
theorem stateRel_byteArray_lookup {C F : Type} {source : State (Nat × C) F} {target : State C F}
    (related : StateRel source target) (index : Nat) (bytes : List (BitVec 8)) :
    source.refs.lookup index = some (.byteArray bytes) ↔
      target.refs.lookup index = some (.byteArray bytes) := by
  have h := related.2.2.2.2.2.1 index
  cases left : source.refs.lookup index <;> cases right : target.refs.lookup index <;>
    simp_all [optionRel, RefRel]
  rename_i leftRef rightRef
  cases leftRef <;> cases rightRef <;> simp_all

/-- Related reference stores have the same allocated addresses. -/
theorem stateRel_ref_unused {C F : Type} {source : State (Nat × C) F} {target : State C F}
    (related : StateRel source target) (index : Nat) :
    source.refs.lookup index = none ↔ target.refs.lookup index = none := by
  have h := related.2.2.2.2.2.1 index
  cases left : source.refs.lookup index <;> cases right : target.refs.lookup index <;>
    simp_all [optionRel]

/-- Allocation chooses the same least free reference in related stores. -/
theorem stateRel_leastUnusedRef {C F : Type} {source : State (Nat × C) F} {target : State C F}
    (related : StateRel source target) : leastUnusedRef source.refs = leastUnusedRef target.refs := by
  apply Nat.le_antisymm
  · by_contra notLe
    have smaller : leastUnusedRef target.refs < leastUnusedRef source.refs := by omega
    have occupied := leastUnusedRef_minimal source.refs _ smaller
    have free := (stateRel_ref_unused related _).mpr (leastUnusedRef_unused target.refs)
    exact occupied free
  · by_contra notLe
    have smaller : leastUnusedRef source.refs < leastUnusedRef target.refs := by omega
    have occupied := leastUnusedRef_minimal target.refs _ smaller
    have free := (stateRel_ref_unused related _).mp (leastUnusedRef_unused source.refs)
    exact occupied free

/-- Related stores agree on whether an address contains a value array and
    relate its fields pointwise whenever it does. -/
theorem stateRel_valueArray_lookup {C F : Type} {source : State (Nat × C) F} {target : State C F}
    (related : StateRel source target) (index : Nat) :
    optionRel (List.Forall₂ (ValueRel source.maxApp))
      (match source.refs.lookup index with | some (.valueArray values) => some values | _ => none)
      (match target.refs.lookup index with | some (.valueArray values) => some values | _ => none) := by
  have h := related.2.2.2.2.2.1 index
  cases left : source.refs.lookup index <;> cases right : target.refs.lookup index <;>
    simp_all [optionRel, RefRel]
  rename_i leftRef rightRef
  cases leftRef <;> cases rightRef <;> simp_all

/-- Initial states satisfy the relation whenever future incremental source
programs contain no pre-numbered applications or auxiliary code. This shows
that the state relation is inhabited under its intended oracle conditions. -/
theorem initialState_stateRel {C F : Type} (ffi : HolFfiState F) (maxApp clock : Nat)
    (oracle : CompileOracle (Nat × C)) (compiler : Compiler C)
    (safe : ∀ index, (oracle index).2.2 = [] ∧ ¬ ClosProps.containsAppSome maxApp (oracle index).2.1) :
    StateRel (initialState ffi maxApp HolFiniteMapExact.empty oracle
        (stateCc (ignoreTable compileInc) compiler) clock)
      (initialState ffi maxApp HolFiniteMapExact.empty
        (stateCo (ignoreTable compileInc) oracle) compiler clock) := by
  simp [StateRel, initialState, HolFiniteMapExact.empty, optionRel, safe]

end Flapjack.Compiler.Backend.ClosNumber
