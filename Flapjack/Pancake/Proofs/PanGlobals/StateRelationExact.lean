import Flapjack.HolRef
import Flapjack.Misc.GoodDimindex
import Flapjack.Compiler.Backend.StackRemove
import Flapjack.Pancake.PanGlobals.CompileExpExact
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanSem.MemLoadHOL
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
import Flapjack.Pancake.Semantics.PanSemStateEval

/-!
# Exact finite-carrier ports of the PanGlobals state relation

The source declarations are `disjoint_globals_def` and `state_rel_def` in
`cakeml/pancake/proofs/pan_globalsProofScript.sml:12-42`.  The latter relates
two finite-map `panSem$state` records through the exact `pan_globals$context`
record.  This module uses those existing reviewed carriers rather than the
function-backed production context/state: `PanSemStateFiniteExact` and
`PanGlobalsContextExact`.

The `fmap_as_finite_support_relation` qualifiers list every finite-map field
traversed by each declaration.  `words_as_type_indexed_bitvec` records only
HOL's positive-dimension word translation.  HOL's standard-library
`byte_aligned` is rendered by the local predicate `panGlobalsByteAlignedHOL`;
it is the fixed-point condition of `byte_align` (clear the low
`LOG2 (width / 8)` bits), with no claim that the external HOL library
declaration is itself a CakeML-script port.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString (MlString)
open Flapjack.Pancake.PanLang
  (MlS ShapeHOL StructContextExact StructInfoHOLExact ProgHOL sizeOfShapeHOL)

/-- HOL `byte_aligned` at a positive HOL word dimension.  The source is
    `aligned (LOG2 (dimindex DIV 8)) address`, i.e. the corresponding
    `byte_align` fixed point.  This uses the same source-shaped
    `panByteAlignHOL` rendering already used by the Pan evaluator.  The HOL
    standard-library declaration lives outside the CakeML scripts, so this
    named predicate is local representation support. -/
def panGlobalsByteAlignedHOL {width : Nat} [NeZero width]
    (address : BitVec width) : Prop :=
  panByteAlignHOL address = address

/-- Exact finite-map rendering of HOL `disjoint_globals_def`
    (`pan_globalsProofScript.sml:12-16`).  HOL's two `|->` inputs are
    independently carried by `HolFiniteMapExact`; `addresses` is the reviewed
    exact definition from `stack_removeProofScript.sml`, and set disjointness
    is expanded pointwise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "disjoint_globals_def"
  (fmap_as_finite_support_relation := [cglobals, globals])
  (words_as_type_indexed_bitvec)]
def disjointGlobalsHOLExact {width : Nat} [NeZero width]
    (topAddress : BitVec width)
    (cglobals : HolFiniteMapExact MlS (ShapeHOL × BitVec width))
    (globals : HolFiniteMapExact MlS (ValueHOL width)) : Prop :=
  ∀ name name' shape address shape' address',
    name ≠ name' →
    globals.lookup name ≠ none →
    globals.lookup name' ≠ none →
    cglobals.lookup name = some (shape, address) →
    cglobals.lookup name' = some (shape', address') →
    ∀ slot,
      ¬ (Flapjack.Compiler.Backend.StackRemove.addresses
          (topAddress - address) (sizeOfShapeHOL shape) slot ∧
        Flapjack.Compiler.Backend.StackRemove.addresses
          (topAddress - address') (sizeOfShapeHOL shape') slot)

/-- Same-module canonical finite-map relation witness for the exact
    `PanSemStateFiniteExact` carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Same-module canonical finite-map relation witness for the exact
    `PanGlobalsContextExact` carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

/-- HOL `state_rel_def` (`pan_globalsProofScript.sml:18-42`) over the exact
    finite-map state and context carriers.  The conjuncts preserve the HOL
    order: adjusted top address; conditional locals equality; base address,
    endianness, exception-shape map, and clock; empty source and target struct
    contexts; global-to-memory lookup; context shape validity; memory-domain
    inclusion; shared-memory-domain equality; memory agreement on source
    addresses; FFI equality; compiled code lookup; global-address disjointness;
    top-address exclusion and alignment; then `good_dimindex`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_def"
  (fmap_as_finite_support_relation :=
    [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals,
     PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes,
     PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
noncomputable def panGlobalsStateRelHOLExact {width : Nat} {σ : Type} [NeZero width]
    (localsEqual : Bool) (context : PanGlobalsContextExact width)
    (source target : PanSemStateFiniteExact width σ) : Prop :=
  letI : DecidablePred target.memaddrs :=
    fun address => Classical.propDecidable (target.memaddrs address)
  source.topAddr = target.topAddr - context.maxGlobalsSize ∧
  (localsEqual = true → source.locals = target.locals) ∧
  source.baseAddr = target.baseAddr ∧
  source.be = target.be ∧
  source.eshapes = target.eshapes ∧
  source.clock = target.clock ∧
  source.structs = ([] : StructContextExact) ∧
  target.structs = ([] : StructContextExact) ∧
  (∀ name value,
    source.globals.lookup name = some value →
      ∃ address,
        context.globals.lookup name = some (shapeOfHOLExact value, address) ∧
        isWfShapeNilHOL (shapeOfHOLExact value) = true ∧
        memLoadHOLExact (shapeOfHOLExact value) (target.topAddr - address)
          target.memaddrs target.memory ([] : List (MlString × StructInfoHOLExact)) =
            some value ∧
        (∀ slot, source.memaddrs slot →
          ¬ Flapjack.Compiler.Backend.StackRemove.addresses
            (target.topAddr - address) (sizeOfShapeHOL (shapeOfHOLExact value)) slot) ∧
        panGlobalsByteAlignedHOL address) ∧
  (∀ name shape address,
    context.globals.lookup name = some (shape, address) →
      isWfShapeNilHOL shape = true) ∧
  (∀ address, source.memaddrs address → target.memaddrs address) ∧
  source.shMemaddrs = target.shMemaddrs ∧
  (∀ address, source.memaddrs address → source.memory address = target.memory address) ∧
  source.ffi = target.ffi ∧
  (∀ function parameters program returnShape,
    source.code.lookup function = some (parameters, program, returnShape) →
      target.code.lookup function =
        some (parameters,
          compileProgExactHOL context program,
          returnShape)) ∧
  disjointGlobalsHOLExact target.topAddr context.globals source.globals ∧
  (¬ target.memaddrs target.topAddr) ∧
  panGlobalsByteAlignedHOL target.topAddr ∧
  goodDimindex width

/-- HOL `state_rel_structs[local]` (`pan_globalsProofScript.sml:50-54`): the
    empty-structure conjuncts are direct projections of `state_rel_def`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_structs" 50
  (fmap_as_finite_support_relation :=
    [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals,
     PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes,
     PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem panGlobalsStateRelStructsHOLExact {width : Nat} {σ : Type}
    [NeZero width] (localsEqual : Bool) (context : PanGlobalsContextExact width)
    (source target : PanSemStateFiniteExact width σ)
    (hrel : panGlobalsStateRelHOLExact localsEqual context source target) :
    source.structs = ([] : StructContextExact) ∧
      target.structs = ([] : StructContextExact) :=
  ⟨hrel.2.2.2.2.2.2.1, hrel.2.2.2.2.2.2.2.1⟩

/-- HOL `state_rel_globals_wf[local]` (`pan_globalsProofScript.sml:57-63`):
    a present context entry has a well-formed empty-context shape, by the
    `FEVERY` conjunct in `state_rel_def`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_globals_wf" 57
  (fmap_as_finite_support_relation :=
    [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals,
     PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes,
     PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem panGlobalsStateRelGlobalsWfHOLExact {width : Nat} {σ : Type}
    [NeZero width] (localsEqual : Bool) (context : PanGlobalsContextExact width)
    (source target : PanSemStateFiniteExact width σ)
    (name : MlS) (entry : ShapeHOL × BitVec width) :
    context.globals.lookup name = some entry ∧
      panGlobalsStateRelHOLExact localsEqual context source target →
    isWfShapeNilHOL entry.1 = true := by
  intro ⟨hlookup, hrel⟩
  exact hrel.2.2.2.2.2.2.2.2.2.1 name entry.1 entry.2 hlookup

/-- Local support for `state_rel_mem_load`: with the empty structure context,
    a load succeeds on any larger domain whose memory agrees on the smaller
    domain.  This is the `mem_load`/`mem_loads` part of HOL's `mem_load_ind`
    proof (named shapes fail in the empty context); no separate HOL
    declaration. -/
private theorem memLoadHOLExact_nil_mono {width : Nat} [NeZero width]
    (domain domain' : BitVec width → Prop) [DecidablePred domain] [DecidablePred domain']
    (memory memory' : BitVec width → HolWordLab width)
    (hdomain : ∀ address, domain address → domain' address)
    (hmemory : ∀ address, domain address → memory address = memory' address) :
    (∀ (shape : ShapeHOL) (address : BitVec width) (value : ValueHOL width),
      memLoadHOLExact shape address domain memory [] = some value →
        memLoadHOLExact shape address domain' memory' [] = some value) ∧
    (∀ (shapes : List ShapeHOL) (address : BitVec width) (values : List (ValueHOL width)),
      memLoadsHOLExact shapes address domain memory [] = some values →
        memLoadsHOLExact shapes address domain' memory' [] = some values) := by
  have hcons : ∀ (shape : ShapeHOL) (rest : List ShapeHOL),
      (∀ (address : BitVec width) (value : ValueHOL width),
        memLoadHOLExact shape address domain memory [] = some value →
          memLoadHOLExact shape address domain' memory' [] = some value) →
      (∀ (address : BitVec width) (values : List (ValueHOL width)),
        memLoadsHOLExact rest address domain memory [] = some values →
          memLoadsHOLExact rest address domain' memory' [] = some values) →
      ∀ (address : BitVec width) (values : List (ValueHOL width)),
        memLoadsHOLExact (shape :: rest) address domain memory [] = some values →
          memLoadsHOLExact (shape :: rest) address domain' memory' [] = some values := by
    intro shape rest ihShape ihRest address values h
    rw [memLoadsHOLExact] at h ⊢
    cases h1 : memLoadHOLExact shape address domain memory [] with
    | none => rw [h1] at h; cases h
    | some value =>
        cases h2 : memLoadsHOLExact rest
            (address + bytesInWordHOL width *
              BitVec.ofNat width (Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL [] shape))
            domain memory [] with
        | none => rw [h1, h2] at h; cases h
        | some vs =>
            rw [h1, h2] at h
            rw [ihShape address value h1, ihRest _ vs h2]
            exact h
  have hnil : ∀ (address : BitVec width) (values : List (ValueHOL width)),
      memLoadsHOLExact [] address domain memory [] = some values →
        memLoadsHOLExact [] address domain' memory' [] = some values := by
    intro address values h
    rw [memLoadsHOLExact] at h ⊢
    exact h
  have hshape : ∀ (shape : ShapeHOL) (address : BitVec width) (value : ValueHOL width),
      memLoadHOLExact shape address domain memory [] = some value →
        memLoadHOLExact shape address domain' memory' [] = some value := by
    intro shape
    induction shape using ShapeHOL.rec (motive_2 := fun shapes =>
        ∀ (address : BitVec width) (values : List (ValueHOL width)),
          memLoadsHOLExact shapes address domain memory [] = some values →
            memLoadsHOLExact shapes address domain' memory' [] = some values) with
    | one =>
        intro address value h
        rw [memLoadHOLExact] at h ⊢
        by_cases hd : domain address
        · rw [if_pos hd] at h
          rw [if_pos (hdomain address hd), ← hmemory address hd]
          exact h
        · rw [if_neg hd] at h
          cases h
    | comb shapes ih =>
        intro address value h
        rw [memLoadHOLExact] at h ⊢
        cases hs : memLoadsHOLExact shapes address domain memory [] with
        | none => rw [hs] at h; cases h
        | some values =>
            rw [hs] at h
            rw [ih address values hs]
            exact h
    | named name =>
        intro address value h
        rw [memLoadHOLExact] at h
        cases h
    | nil => rename_i address values h; exact hnil address values h
    | cons shape rest ihShape ihRest =>
        rename_i address values h; exact hcons shape rest ihShape ihRest address values h
  refine ⟨hshape, fun shapes => ?_⟩
  induction shapes with
  | nil => exact hnil
  | cons shape rest ihRest => exact hcons shape rest (hshape shape) ihRest

/-- HOL `state_rel_mem_load` (`pan_globalsProofScript.sml:67-70`).  Both
    loads use the empty structure context, as in HOL, and classical
    decidability of the memory domains is fixed internally (no binder). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_mem_load"
  (fmap_as_finite_support_relation :=
    [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals,
     PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes,
     PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem panGlobalsStateRelMemLoadHOLExact {width : Nat} {σ : Type}
    [NeZero width] (localsEqual : Bool) (context : PanGlobalsContextExact width)
    (source target : PanSemStateFiniteExact width σ)
    (shape : ShapeHOL) (address : BitVec width) (value : ValueHOL width) :
    panGlobalsStateRelHOLExact localsEqual context source target ∧
      @memLoadHOLExact width _ shape address source.memaddrs
        (fun a => Classical.propDecidable (source.memaddrs a)) source.memory [] = some value →
    @memLoadHOLExact width _ shape address target.memaddrs
        (fun a => Classical.propDecidable (target.memaddrs a)) target.memory [] = some value := by
  intro ⟨hrel, hload⟩
  have hsub := hrel.2.2.2.2.2.2.2.2.2.2.1
  have hmem := hrel.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact (@memLoadHOLExact_nil_mono width _ source.memaddrs target.memaddrs
    (fun a => Classical.propDecidable (source.memaddrs a))
    (fun a => Classical.propDecidable (target.memaddrs a))
    source.memory target.memory hsub hmem).1 shape address value hload

end Flapjack
