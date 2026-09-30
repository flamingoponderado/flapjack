import Flapjack.HolRef
import Flapjack.Misc.GoodDimindex
import Flapjack.Compiler.Backend.StackRemove
import Flapjack.Pancake.PanGlobals.CompileExpExact
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanSem.MemLoadHOL
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
import Flapjack.Pancake.Semantics.PanSem.EvalFinite
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

open Flapjack.Pancake.PanLang

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

/-- HOL `compile_exp_correct`, `Var Global` case
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:103-119`).  The source
    proof is a `recInduct eval_ind` case split; this piece keeps the same
    hypotheses (`state_rel T ctxt s t` and the source evaluation equation), the
    same source-shaped conclusion, and no extra premise.  The state relation
    exposes the globals finite map and its memory-load image, and `compile_exp`
    renders the global read as `Load sh (Op Sub [TopAddr; Const address])`, so
    the compilable address is `target.topAddr - address`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support_relation :=
    [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals,
     PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes,
     PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem panGlobalsCompileExpCorrectGlobalVarCaseExact {width : Nat} {σ : Type}
    [NeZero width]
    (source : PanSemStateFiniteExact width σ) (name : MlS)
    (value : ValueHOL width) (context : PanGlobalsContextExact width)
    (target : PanSemStateFiniteExact width σ) :
    (panGlobalsStateRelHOLExact true context source target ∧
      @PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun address => Classical.propDecidable (source.memaddrs address))
        (.var .global name) = some value) →
    @PanSemStateFiniteExact.evalHOLFinite width σ _ target
      (fun address => Classical.propDecidable (target.memaddrs address))
      (compileExpExactHOL context (.var .global name)) = some value := by
  intro ⟨hrel, heval⟩
  simp only [PanSemStateFiniteExact.evalHOLFinite_var_global] at heval
  obtain ⟨_, hstructsT⟩ := panGlobalsStateRelStructsHOLExact true context source target hrel
  obtain ⟨address, hlookup, hwf, hmemload, _⟩ :=
    hrel.2.2.2.2.2.2.2.2.1 name value heval
  have hwf' : Flapjack.Pancake.PanLang.isWfShapeExactHOL ([] : StructContextExact)
      (shapeOfHOLExact value) = true := by
    simpa only [isWfShapeNilHOL] using hwf
  simp only [compileExpExactHOL, hlookup]
  rw [PanSemStateFiniteExact.evalHOLFinite_load]
  rw [hstructsT]
  rw [if_pos hwf']
  have hop :
      @PanSemStateFiniteExact.evalHOLFinite width σ _ target
        (fun address => Classical.propDecidable (target.memaddrs address))
        (.op .sub [.topAddr, .const address]) =
        some (.val (.word (target.topAddr - address))) := by
    rfl
  rw [hop]
  exact hmemload


/-! ### Memory-load monotonicity helpers

HOL's `Load`/`Load32`/`LoadByte` cases of `compile_exp_correct` inline the
`mem_load`/`mem_load_32`/`mem_load_byte` definitions and the `state_rel_def`
memory conjuncts.  The following two lemmas are the same transfer step stated
once for the `panMemLoad32HOL` and `panMemLoadByteHOL` helpers (Flapjack
infrastructure, no separate HOL declaration to cite). -/

/-- `panMemLoad32HOL` is monotone in the address domain and memory: if the
    target domain contains the source domain and the two memories agree there,
    then the target reads the same `word32`. -/
theorem panMemLoad32HOL_mono {width : Nat} [NeZero width]
    (sm tm : RiscV.Word width → HolWordLab width)
    (sd td : RiscV.Word width → Prop)
    (be : Bool) (address : RiscV.Word width) (v : RiscV.Word 32)
    (hsub : ∀ a, sd a → td a) (hmem : ∀ a, sd a → sm a = tm a)
    (h : @panMemLoad32HOL width _ sm sd (fun a => Classical.propDecidable (sd a))
      be address = some v) :
    @panMemLoad32HOL width _ tm td (fun a => Classical.propDecidable (td a))
      be address = some v := by
  unfold panMemLoad32HOL at h ⊢
  by_cases hal : address.toNat % 4 = 0
  · rw [if_pos hal] at h ⊢
    dsimp only at h ⊢
    cases hm : sm (panByteAlignHOL (width := width) address) with
    | word value =>
      rw [hm] at h
      by_cases hsd : sd (panByteAlignHOL (width := width) address)
      · rw [if_pos hsd] at h
        rw [if_pos (hsub _ hsd)]
        rw [← hmem _ hsd, hm]
        exact h
      · rw [if_neg hsd] at h
        exact absurd h (by simp)
  · rw [if_neg hal] at h ⊢
    simp at h

/-- `panMemLoadByteHOL` is monotone in the address domain and memory, with the
    same statement shape as `panMemLoad32HOL_mono`. -/
theorem panMemLoadByteHOL_mono {width : Nat} [NeZero width]
    (sm tm : RiscV.Word width → HolWordLab width)
    (sd td : RiscV.Word width → Prop)
    (be : Bool) (address : RiscV.Word width) (v : UInt8)
    (hsub : ∀ a, sd a → td a) (hmem : ∀ a, sd a → sm a = tm a)
    (h : @panMemLoadByteHOL width _ sm sd (fun a => Classical.propDecidable (sd a))
      be address = some v) :
    @panMemLoadByteHOL width _ tm td (fun a => Classical.propDecidable (td a))
      be address = some v := by
  unfold panMemLoadByteHOL at h ⊢
  dsimp only at h ⊢
  cases hm : sm (panByteAlignHOL (width := width) address) with
  | word value =>
    rw [hm] at h
    by_cases hsd : sd (panByteAlignHOL (width := width) address)
    · rw [if_pos hsd] at h
      rw [if_pos (hsub _ hsd)]
      rw [← hmem _ hsd, hm]
      exact h
    · rw [if_neg hsd] at h
      exact absurd h (by simp)

/-- HOL `compile_exp_correct`, `Load` case
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:103-131`).  The address
    subexpression is compiled by the same pass, so the case carries the
    original `eval_ind` induction hypothesis for the address expression; the
    state relation and evaluation premise and the conclusion keep HOL's shape
    and add no stronger premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support_relation :=
    [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals,
     PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes,
     PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem panGlobalsCompileExpCorrectLoadCaseExact {width : Nat} {σ : Type}
    [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width)
    (shape : ShapeHOL) (address : ExpHOL width) (value : ValueHOL width)
    (addressIH : ∀ (addressValue : ValueHOL width),
      @PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a)) address = some addressValue →
      @PanSemStateFiniteExact.evalHOLFinite width σ _ target
        (fun a => Classical.propDecidable (target.memaddrs a))
        (compileExpExactHOL context address) = some addressValue)
    (h : panGlobalsStateRelHOLExact true context source target ∧
      @PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a))
        (.load shape address) = some value) :
    @PanSemStateFiniteExact.evalHOLFinite width σ _ target
      (fun a => Classical.propDecidable (target.memaddrs a))
      (compileExpExactHOL context (.load shape address)) = some value := by
  obtain ⟨hrel, heval⟩ := h
  obtain ⟨hstructsS, hstructsT⟩ := panGlobalsStateRelStructsHOLExact true context source target hrel
  simp only [compileExpExactHOL, PanSemStateFiniteExact.evalHOLFinite_load] at heval ⊢
  rw [hstructsS] at heval
  rw [hstructsT]
  by_cases hwf : isWfShapeExactHOL ([] : StructContextExact) shape = true
  · rw [if_pos hwf] at heval ⊢
    cases haddr : @PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a)) address with
    | none => simp only [haddr] at heval; simp at heval
    | some av =>
        cases av with
        | val wv =>
            cases wv with
            | word word =>
                simp only [haddr] at heval
                have haddrT := addressIH (.val (.word word)) (by rw [haddr])
                simp only [haddrT]
                exact panGlobalsStateRelMemLoadHOLExact true context source target
                  shape word value ⟨hrel, heval⟩
        | rStruct fields => simp only [haddr] at heval; simp at heval
        | nStruct name fields => simp only [haddr] at heval; simp at heval
  · rw [if_neg hwf] at heval ⊢
    simp at heval

/-- HOL `compile_exp_correct`, `Load32` case
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:103-131`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support_relation :=
    [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals,
     PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes,
     PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem panGlobalsCompileExpCorrectLoad32CaseExact {width : Nat} {σ : Type}
    [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width)
    (address : ExpHOL width) (value : ValueHOL width)
    (addressIH : ∀ (addressValue : ValueHOL width),
      @PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a)) address = some addressValue →
      @PanSemStateFiniteExact.evalHOLFinite width σ _ target
        (fun a => Classical.propDecidable (target.memaddrs a))
        (compileExpExactHOL context address) = some addressValue)
    (h : panGlobalsStateRelHOLExact true context source target ∧
      @PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a))
        (.load32 address) = some value) :
    @PanSemStateFiniteExact.evalHOLFinite width σ _ target
      (fun a => Classical.propDecidable (target.memaddrs a))
      (compileExpExactHOL context (.load32 address)) = some value := by
  obtain ⟨hrel, heval⟩ := h
  obtain ⟨_hTop, _hloc, _hbase, hbe, _heshapes, _hclock, _hstructsS, _hstructsT, _hglob, _hwf,
    hsub, _hshmem, hmem, _hffi, _hcode, _hdis, _htopmem, _halign, _hgood⟩ := hrel
  simp only [compileExpExactHOL, PanSemStateFiniteExact.evalHOLFinite_load32] at heval ⊢
  rw [← hbe]
  cases haddr : @PanSemStateFiniteExact.evalHOLFinite width σ _ source
      (fun a => Classical.propDecidable (source.memaddrs a)) address with
  | none => simp only [haddr] at heval; simp at heval
  | some av =>
      cases av with
      | val wv =>
          cases wv with
          | word word =>
              simp only [haddr] at heval
              have haddrT := addressIH (.val (.word word)) (by rw [haddr])
              cases h32 : @panMemLoad32HOL width _ source.memory source.memaddrs
                  (fun a => Classical.propDecidable (source.memaddrs a)) source.be word with
              | none => simp only [h32] at heval; simp at heval
              | some w32 =>
                  simp only [h32, Option.map_some] at heval
                  have hval : value = .val (.word (BitVec.ofNat width w32.toNat)) :=
                    (Option.some.inj heval).symm
                  subst hval
                  have h32t := panMemLoad32HOL_mono source.memory target.memory
                    source.memaddrs target.memaddrs source.be word w32 hsub hmem h32
                  simp only [haddrT, Option.map_some, h32t]
      | rStruct fields => simp only [haddr] at heval; simp at heval
      | nStruct name fields => simp only [haddr] at heval; simp at heval

/-- HOL `compile_exp_correct`, `LoadByte` case
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:103-131`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support_relation :=
    [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals,
     PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes,
     PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem panGlobalsCompileExpCorrectLoadByteCaseExact {width : Nat} {σ : Type}
    [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width)
    (address : ExpHOL width) (value : ValueHOL width)
    (addressIH : ∀ (addressValue : ValueHOL width),
      @PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a)) address = some addressValue →
      @PanSemStateFiniteExact.evalHOLFinite width σ _ target
        (fun a => Classical.propDecidable (target.memaddrs a))
        (compileExpExactHOL context address) = some addressValue)
    (h : panGlobalsStateRelHOLExact true context source target ∧
      @PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a))
        (.loadByte address) = some value) :
    @PanSemStateFiniteExact.evalHOLFinite width σ _ target
      (fun a => Classical.propDecidable (target.memaddrs a))
      (compileExpExactHOL context (.loadByte address)) = some value := by
  obtain ⟨hrel, heval⟩ := h
  obtain ⟨_hTop, _hloc, _hbase, hbe, _heshapes, _hclock, _hstructsS, _hstructsT, _hglob, _hwf,
    hsub, _hshmem, hmem, _hffi, _hcode, _hdis, _htopmem, _halign, _hgood⟩ := hrel
  simp only [compileExpExactHOL, PanSemStateFiniteExact.evalHOLFinite_loadByte] at heval ⊢
  rw [← hbe]
  cases haddr : @PanSemStateFiniteExact.evalHOLFinite width σ _ source
      (fun a => Classical.propDecidable (source.memaddrs a)) address with
  | none => simp only [haddr] at heval; simp at heval
  | some av =>
      cases av with
      | val wv =>
          cases wv with
          | word word =>
              simp only [haddr] at heval
              have haddrT := addressIH (.val (.word word)) (by rw [haddr])
              cases h8 : @panMemLoadByteHOL width _ source.memory source.memaddrs
                  (fun a => Classical.propDecidable (source.memaddrs a)) source.be word with
              | none => simp only [h8] at heval; simp at heval
              | some w8 =>
                  simp only [h8, Option.map_some] at heval
                  have hval : value = .val (.word (BitVec.ofNat width w8.toNat)) :=
                    (Option.some.inj heval).symm
                  subst hval
                  have h8t := panMemLoadByteHOL_mono source.memory target.memory
                    source.memaddrs target.memaddrs source.be word w8 hsub hmem h8
                  simp only [haddrT, Option.map_some, h8t]
      | rStruct fields => simp only [haddr] at heval; simp at heval
      | nStruct name fields => simp only [haddr] at heval; simp at heval

end Flapjack
