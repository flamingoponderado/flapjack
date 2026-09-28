import Flapjack.Pancake.Semantics.PanSem.TotalEvalBridge
import Flapjack.Pancake.Semantics.PanSem.EvalFinite
import Flapjack.Pancake.Semantics.PanSem.MemLoadHOL
import Flapjack.Pancake.Semantics.PanSem.StateExactFinite
import Flapjack.Pancake.PanStructsByteRanged
import Flapjack.Pancake.Semantics.PanProps

/-!
# Production/exact expression-evaluation agreement for the total `panSem` bridge

`Flapjack/Pancake/Semantics/PanSem/TotalEvalBridge.lean` records
`PanSemStateRelExec` between the executable production `PanSemState` and the
exact `PanSemStateFiniteExact`, but only the expression-free `Prog` leaf clauses.

This module proves the missing prerequisite: for every production `Exp`
constructor, the executable expression evaluator agrees with the exact
`evalHOLExact` on the `expToHOL` image.  The agreement is stated through the
value codec `panValueToHOL` (the executable `PanValue` is mapped into the exact
`ValueHOL` carrier), for arbitrary hosts `σ`.

All sixteen production `Exp` constructors (`const`, `var`, `rStruct`, `rField`,
`baseAddr`, `topAddr`, `bytesInWord`, `op`, `panOp`, `cmp`, `shift`, `load32`,
`loadByte`, `nStruct`, `nField`, and `load`) now have per-constructor
production/exact agreement lemmas, together with the
list/field/name/shape/memory bridge infrastructure and the production
`StructContext` / `panMemLoadHOL` versus exact `StructContextExact` /
`memLoadHOLExact` carrier bridges for the structured clauses.  The all-16
assembly `evalPanValueExp_agree`, its state-owned wrapper
`evalPanSemStateExp_agree`, and the companion result-rangedness theorem
`evalPanValueExp_byteRanged` (with the `panValueFlatLoad_*` rangedness lemmas)
are kernel-checked.  This establishes agreement between the *production
evaluator* and the exact HOL-shaped evaluator; it does **not** yet establish
that the executed compiler path runs these definitions, and the agreement is not
unconditional for arbitrary production states (see the preservation obligation
below).

## Representation premises

`PanSemStateRelExec` compares the executable `String`-keyed state with the exact
`mlstring`-keyed state only at byte-ranged names, and its `structs`/`memory`
comparison does not constrain the production `String` names or value field names
to the byte range that HOL `char`/`mlstring` represents.  Two representation
premises are therefore relevant:

* `ExpByteRanged e` / `ShapeByteRanged shape` -- every identifier and shape name
  occurring in the expression is byte-ranged, so its `expToHOL` image (through the
  low-byte `ofString`) round-trips and name comparisons transfer;
* `PanSemStateRelExecRanged state` -- the executable local/global values and the
  structure context are byte-ranged, so a stored record's field-name lookups and
  a context shape comparison agree with their `mlstring` images.

The **expression** half is discharged from the executed compiler path: the
parser-backed entrypoints (`Pipeline.lean:634-671`) thread `DeclByteRanged` for
their declarations, a function body carries `ProgByteRanged`
(`FunDeclByteRanged`), and `expsOf_byteRanged`
(`Flapjack/Pancake/PanLang/Prog.lean`) proves that every expression occurring
directly in a `ProgByteRanged` program is `ExpByteRanged` (a loaded shape is
covered because `ExpByteRanged (.load shape _)` requires `ShapeByteRanged
shape`, and the declaration-level shapes are the other `DeclByteRanged`
conjuncts).  Accordingly the wrappers `evalPanValueExp_agree_of_mem_expsOf`,
`evalPanSemStateExp_agree_of_mem_expsOf`,
`evalPanValueExp_agree_of_funDeclByteRanged`, and
`panSemTotalEvaluate_assign_agree_of_progByteRanged` replace the explicit
`ExpByteRanged`/`NameRanged` premises by a `ProgByteRanged`/`FunDeclByteRanged`
hypothesis.  Parser origin itself does not prove `ProgByteRanged`; it is the
premise the executed path carries, and the projection above is the bridge from
that premise.

The **state** premise `PanSemStateRelExecRanged` remains explicit and is *not*
a consequence of parser origin: parsing constrains program syntax and identifier
bytes, but does not constrain runtime FFI return values, initial/stored globals,
or stored record structures to the byte range that HOL `char`/`mlstring`
represents.  The precise residual boundary is recorded in the "Rangedness
preservation and the `PanSemStateRelExec`/rangedness boundary" section below: the
value-map updates preserve the premise (`updatePanValueMap_byteRanged`,
`PanSemStateRelExecRanged.updateLocals`/`.updateGlobals`), the production
`ExtCall` clause preserves it unconditionally, the production `Primitive` clause
preserves it under `PanPrimitiveHandlerByteRanged`, and a non-byte-ranged
initial/stored global crosses the boundary (`extCallClause_not_ranged_of_global_nonRanged`).
Consequently the agreement theorems still carry the state premise as an explicit
hypothesis and are *not* unconditional for arbitrary production states; the
remaining runtime/initial-global obligation is tracked by the blocker bead
`flapjack-pxn.18.4.3.77.2.15`, which blocks the full total-evaluate assembly bead
`flapjack-pxn.18.4.3.77.2.14`.  Everything in this module is untagged
Flapjack-specific bridge infrastructure; no `@[hol]` tag is attached.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open PanSemStateFiniteExact

/-- Forward value codec: the executable value encodes to the exact value. -/
def PanValueExactRel {width : Nat} [NeZero width]
    (production : PanValue (BitVec width)) (exact : ValueHOL width) : Prop :=
  panValueToHOL production = exact

/-- Forward option codec. -/
def PanValueOptionExactRel {width : Nat} [NeZero width]
    (production : Option (PanValue (BitVec width)))
    (exact : Option (ValueHOL width)) : Prop :=
  Option.map panValueToHOL production = exact

/-- Forward list codec. -/
def PanValueListExactRel {width : Nat} [NeZero width] :
    List (PanValue (BitVec width)) → List (ValueHOL width) → Prop
  | productions, exacts => productions.map panValueToHOL = exacts

/-- Forward named-field-list codec. -/
def PanFieldListExactRel {width : Nat} [NeZero width] :
    List (String × PanValue (BitVec width)) → List (MlS × ValueHOL width) → Prop
  | productions, exacts => productions.map (fun p => (ofString p.1, panValueToHOL p.2)) = exacts

/-- Representation premise on the executable state: every stored local/global
    value and the structure context are byte-ranged. -/
def PanSemStateRelExecRanged {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) : Prop :=
  (∀ name value, state.locals name = some value → PanValueByteRanged value) ∧
  (∀ name value, state.globals name = some value → PanValueByteRanged value) ∧
  StructContextByteRanged state.structs.toHOL

/-- Representation premise on the executable state: every production exception
    shape stored in `exceptionShapes` is byte-ranged.  `PanSemStateRelExec`
    compares exception shapes only through the lossy `shapeToHOL`, so this
    premise is what makes the production `panShapeMatches` test agree with the
    exact `shapeEqHOL`; it is intrinsic to the compiled initial state and
    preserved by every production state update (see
    `panSemTotalEvaluate_exceptionShapes` below). -/
def PanSemExceptionShapesRanged {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) : Prop :=
  ∀ exceptionId shape, state.exceptionShapes exceptionId = some shape → ShapeByteRanged shape

@[simp] theorem panValueToHOL_rStruct {width : Nat} [NeZero width]
    (fields : List (PanValue (BitVec width))) :
    panValueToHOL (.rStruct fields) = .rStruct (fields.map panValueToHOL) := by
  simp only [panValueToHOL]

@[simp] theorem panValueToHOL_nStruct {width : Nat} [NeZero width]
    (name : StructName) (fields : List (FieldName × PanValue (BitVec width))) :
    panValueToHOL (.nStruct name fields) =
      .nStruct (ofString name)
        (fields.map (fun p => (ofString p.1, panValueToHOL p.2))) := by
  simp only [panValueToHOL]

@[simp] theorem panValueToHOL_comp_word {width : Nat} [NeZero width] :
    (panValueToHOL ∘ PanValue.word) =
      (fun w : BitVec width => (ValueHOL.val (HolWordLab.word w) : ValueHOL width)) := by
  funext w
  exact panValueToHOL_word w

/-- List-level agreement: if every element agrees, the executable list step
    agrees with the exact `OPT_MMAP` step under `panValueToHOL`. -/
theorem evalPanValueExps_eq_evalListHOLExact_of {σ : Type}
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (baseAddress topAddress bytesInWord : RiscV.Word 64)
    (access : Option (PanValueMemoryAccess (RiscV.Word 64)))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (expressions : List (Exp (RiscV.Word 64)))
    (hexp : ∀ e ∈ expressions,
      Option.map panValueToHOL
          (evalPanValueExp structs locals globals memory baseAddress topAddress
            bytesInWord e (memoryAccess := access))
        = exact.evalHOLFinite (expToHOL e)) :
    Option.map (List.map panValueToHOL)
        (evalPanValueExp.evalPanValueExps structs locals globals memory baseAddress
          topAddress bytesInWord expressions (memoryAccess := access))
      = exact.evalListHOLFinite (expressions.map expToHOL) := by
  induction expressions with
  | nil =>
      simp only [List.map_nil, evalPanValueExp.evalPanValueExps, PanSemStateFiniteExact.evalListHOLFinite_eq_toExact]
      rfl
  | cons expression expressions ih =>
      have hhead := hexp expression List.mem_cons_self
      have htail : ∀ e ∈ expressions,
          Option.map panValueToHOL
              (evalPanValueExp structs locals globals memory baseAddress topAddress
                bytesInWord e (memoryAccess := access))
            = exact.evalHOLFinite (expToHOL e) :=
        fun e he => hexp e (List.mem_cons_of_mem expression he)
      have hih := ih htail
      rw [PanSemStateFiniteExact.evalHOLFinite_eq_toExact] at hhead
      rw [PanSemStateFiniteExact.evalListHOLFinite_eq_toExact] at hih
      rw [evalPanValueExp.evalPanValueExps]
      simp only [List.map_cons]
      rw [PanSemStateFiniteExact.evalListHOLFinite_eq_toExact]
      rw [evalListHOLExact]
      cases h1 : evalPanValueExp structs locals globals memory baseAddress topAddress
          bytesInWord expression (memoryAccess := access) with
      | none =>
          rw [h1] at hhead
          simp only [Option.map_none] at hhead
          rw [← hhead]
          simp
      | some value =>
          rw [h1] at hhead
          simp only [Option.map_some] at hhead
          rw [← hhead]
          cases h3 : evalPanValueExp.evalPanValueExps structs locals globals memory
              baseAddress topAddress bytesInWord expressions (memoryAccess := access) with
          | none =>
              rw [h3] at hih
              simp only [Option.map_none] at hih
              rw [← hih]
              simp
          | some restValues =>
              rw [h3] at hih
              simp only [Option.map_some] at hih
              rw [← hih]
              simp

/-- Field-list agreement: if every field expression agrees, the executable
    named-field step agrees with the exact `OPT_MMAP` step under
    `panValueToHOL` (field names through `ofString`). -/
theorem evalPanValueFields_eq_evalListFieldsHOLExact_of {σ : Type}
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (baseAddress topAddress bytesInWord : RiscV.Word 64)
    (access : Option (PanValueMemoryAccess (RiscV.Word 64)))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (fields : List (FieldName × Exp (RiscV.Word 64)))
    (hexp : ∀ p ∈ fields,
      Option.map panValueToHOL
          (evalPanValueExp structs locals globals memory baseAddress topAddress
            bytesInWord p.2 (memoryAccess := access))
        = exact.evalHOLFinite (expToHOL p.2)) :
    Option.map (List.map (fun p => (ofString p.1, panValueToHOL p.2)))
        (evalPanValueExp.evalPanValueFields structs locals globals memory baseAddress
          topAddress bytesInWord fields (memoryAccess := access))
      = exact.evalListFieldsHOLFinite
          (fields.map (fun p => (ofString p.1, expToHOL p.2))) := by
  induction fields with
  | nil =>
      simp only [List.map_nil, evalPanValueExp.evalPanValueFields,
        PanSemStateFiniteExact.evalListFieldsHOLFinite_eq_toExact]
      rfl
  | cons pair fields ih =>
      obtain ⟨name, expression⟩ := pair
      have hhead := hexp (name, expression) List.mem_cons_self
      have htail : ∀ p ∈ fields,
          Option.map panValueToHOL
              (evalPanValueExp structs locals globals memory baseAddress topAddress
                bytesInWord p.2 (memoryAccess := access))
            = exact.evalHOLFinite (expToHOL p.2) :=
        fun p hp => hexp p (List.mem_cons_of_mem (name, expression) hp)
      have hih := ih htail
      rw [PanSemStateFiniteExact.evalHOLFinite_eq_toExact] at hhead
      rw [PanSemStateFiniteExact.evalListFieldsHOLFinite_eq_toExact] at hih
      rw [evalPanValueExp.evalPanValueFields]
      simp only [List.map_cons]
      rw [PanSemStateFiniteExact.evalListFieldsHOLFinite_eq_toExact]
      rw [evalListFieldsHOLExact]
      cases h1 : evalPanValueExp structs locals globals memory baseAddress topAddress
          bytesInWord expression (memoryAccess := access) with
      | none =>
          rw [h1] at hhead
          simp only [Option.map_none] at hhead
          rw [← hhead]
          simp
      | some value =>
          rw [h1] at hhead
          simp only [Option.map_some] at hhead
          rw [← hhead]
          cases h3 : evalPanValueExp.evalPanValueFields structs locals globals memory
              baseAddress topAddress bytesInWord fields (memoryAccess := access) with
          | none =>
              rw [h3] at hih
              simp only [Option.map_none] at hih
              rw [← hih]
              simp
          | some restValues =>
              rw [h3] at hih
              simp only [Option.map_some] at hih
              rw [← hih]
              simp

/-- The exact shape of the encoding of a production value is the encoding of
    its production shape. -/
theorem shapeOfHOLExact_panValueToHOL {width : Nat} [NeZero width]
    (structs : StructContext) (v : PanValue (BitVec width)) :
    shapeOfHOLExact (panValueToHOL v) = shapeToHOL (panValueShape structs v) := by
  induction v using panValueToHOL.induct with
  | case1 b => simp only [panValueToHOL, shapeOfHOLExact, panValueShape, shapeToHOL]
  | case2 fields ih =>
      simp only [panValueToHOL, shapeOfHOLExact, panValueShape, shapeToHOL, List.map_map]
      congr 1
      apply List.map_congr_left
      intro x hx
      exact ih x hx
  | case3 name fields ih =>
      simp only [panValueToHOL, shapeOfHOLExact, panValueShape, shapeToHOL]

/-- The production shape of a byte-ranged value is byte-ranged. -/
theorem panValueShape_byteRanged {width : Nat} [NeZero width]
    (structs : StructContext) (v : PanValue (BitVec width))
    (hv : PanValueByteRanged v) : ShapeByteRanged (panValueShape structs v) := by
  induction v using panValueToHOL.induct with
  | case1 b => simp only [panValueShape, ShapeByteRanged]
  | case2 fields ih =>
      simp only [PanValueByteRanged] at hv
      simp only [panValueShape, ShapeByteRanged, List.mem_map]
      rintro s ⟨x, hx, rfl⟩
      exact ih x hx (hv x hx)
  | case3 name fields ih =>
      simp only [PanValueByteRanged] at hv
      obtain ⟨hname, _⟩ := hv
      simpa only [panValueShape, ShapeByteRanged] using hname

/-- Two byte-ranged production shapes match exactly when their exact encodings
    are equal. -/
theorem panShapeMatches_eq_shapeEqHOL (a b : Shape)
    (ha : ShapeByteRanged a) (hb : ShapeByteRanged b) :
    panShapeMatches a b = shapeEqHOL (shapeToHOL a) (shapeToHOL b) := by
  apply Bool.eq_iff_iff.mpr
  rw [panShapeMatches_eq_true, shapeEqHOL_eq_true]
  constructor
  · intro h; rw [h]
  · intro h
    have h' := congrArg shapeOfHOL h
    rwa [shapeOfHOL_shapeToHOL a ha, shapeOfHOL_shapeToHOL b hb] at h'

/-- Head equation for `panStructContextToHOL`. -/
@[simp] theorem panStructContextToHOL_cons (c : StructName) (info : StructInfo)
    (rest : StructContext) :
    panStructContextToHOL ((c, info) :: rest) =
      (ofString c,
        { fields := info.fields.map (fun f => (ofString f.1, shapeToHOL f.2)),
          size := info.size }) :: panStructContextToHOL rest := by
  simp only [panStructContextToHOL, StructContext.toHOL, structContextToHOL,
    structInfoToHOL, List.map_cons]
  rfl

/-- Lookup commutes with `panStructContextToHOL` on byte-ranged contexts. -/
theorem lookupInfo_panStructContextToHOL (name : String) (structs : StructContext)
    (hname : NameRanged name) (hrange : ∀ p ∈ structs, NameRanged p.1) :
    structContextLookupHOL (ofString name) (panStructContextToHOL structs)
      = (lookupInfo name structs).map (fun info =>
          { fields := info.fields.map (fun f => (ofString f.1, shapeToHOL f.2)),
            size := info.size }) := by
  induction structs with
  | nil =>
      simp only [panStructContextToHOL, StructContext.toHOL, structContextToHOL,
        List.map_nil, lookupInfo, structContextLookupHOL, Option.map_none]
  | cons entry rest ih =>
      obtain ⟨candidate, info⟩ := entry
      have hrangeTail : ∀ p ∈ rest, NameRanged p.1 :=
        fun p hp => hrange p (by simp [hp])
      have hcandidate : NameRanged candidate := hrange (candidate, info) (by simp)
      rw [panStructContextToHOL_cons]
      simp only [lookupInfo, structContextLookupHOL]
      by_cases hc : candidate == name
      · have heq : candidate = name := beq_iff_eq.mp hc
        rw [heq]
        simp only [beq_self_eq_true, if_pos, Option.map_some]
      · have hne : candidate ≠ name := fun h => hc (beq_iff_eq.mpr h)
        have hofne : ofString name ≠ ofString candidate :=
          fun h => hne (ofString_injective_of_ranged hname hcandidate h).symm
        rw [if_neg hc, if_neg hofne]
        exact ih hrangeTail

/-! ## Memory-view helpers for the load clauses -/

/-- Under `PanSemStateRelExec`, the executable `memaddrs`-gated word-defined
    domain is the exact `memaddrs` proposition. -/
theorem panValueFlatMachineDomain_iff {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hm : PanSemMemoryRel state.memaddrs state.memory exact.toExact.memory)
    (hmd : ∀ address, state.memaddrs address = true ↔ exact.toExact.memaddrs address)
    (address : RiscV.Word 64) :
    (state.memaddrs address && panValueWordDefined state.memory address = true) ↔
      exact.toExact.memaddrs address := by
  constructor
  · intro h
    have h1 : state.memaddrs address = true := by
      cases hv : state.memaddrs address <;> simp_all
    exact (hmd address).mp h1
  · intro h
    have hstate : state.memaddrs address = true := (hmd address).mpr h
    have hcell := hm address hstate
    have hdef : panValueWordDefined state.memory address = true := by
      simp [panValueWordDefined, hcell]
    simp [hstate, hdef]

/-- On the exact address domain the executable word view is the exact total
    memory. -/
theorem panValueWordHOL_eq_of_memRel {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hm : PanSemMemoryRel state.memaddrs state.memory exact.toExact.memory)
    (hmd : ∀ address, state.memaddrs address = true ↔ exact.toExact.memaddrs address)
    (address : RiscV.Word 64) (h : exact.toExact.memaddrs address) :
    panValueWordHOL state.memory address = exact.toExact.memory address := by
  have hstate : state.memaddrs address = true := (hmd address).mpr h
  have hcell := hm address hstate
  rw [panValueWordHOL, hcell]
  cases exact.memory address with
  | word bits => rfl

/-- The executed and exact `mem_load_32` agree under `PanSemStateRelExec`. -/
theorem panMemLoad32HOL_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact) (address : RiscV.Word 64) :
    panMemLoad32HOL (panValueWordHOL state.memory)
        (fun a => state.memaddrs a && panValueWordDefined state.memory a = true)
        state.be address
      = panMemLoad32HOL exact.memory exact.memaddrs exact.be address := by
  obtain ⟨_, _, _, _, _, hm, hmd, _, _, hbe, _, _, _⟩ := hrel
  by_cases halign : address.toNat % 4 = 0
  · simp only [panMemLoad32HOL, if_pos halign]
    by_cases hexact : exact.memaddrs (panByteAlignHOL (width := 64) address)
    · have hmem := panValueWordHOL_eq_of_memRel state exact hm hmd _ hexact
      have hdom : state.memaddrs (panByteAlignHOL (width := 64) address)
          && panValueWordDefined state.memory (panByteAlignHOL (width := 64) address) = true :=
        (panValueFlatMachineDomain_iff state exact hm hmd _).mpr hexact
      rw [if_pos hdom, if_pos hexact, hmem, ← hbe]
    · have hdom : ¬ (state.memaddrs (panByteAlignHOL (width := 64) address)
          && panValueWordDefined state.memory (panByteAlignHOL (width := 64) address) = true) :=
        fun h => hexact ((panValueFlatMachineDomain_iff state exact hm hmd _).mp h)
      rw [if_neg hdom, if_neg hexact]
  · simp only [panMemLoad32HOL, if_neg halign]

/-- The executed and exact `mem_load_byte` agree under `PanSemStateRelExec`. -/
theorem panMemLoadByteHOL_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact) (address : RiscV.Word 64) :
    panMemLoadByteHOL (panValueWordHOL state.memory)
        (fun a => state.memaddrs a && panValueWordDefined state.memory a = true)
        state.be address
      = panMemLoadByteHOL exact.memory exact.memaddrs exact.be address := by
  obtain ⟨_, _, _, _, _, hm, hmd, _, _, hbe, _, _, _⟩ := hrel
  by_cases hexact : exact.memaddrs (panByteAlignHOL (width := 64) address)
  · have hmem := panValueWordHOL_eq_of_memRel state exact hm hmd _ hexact
    have hdom : state.memaddrs (panByteAlignHOL (width := 64) address)
        && panValueWordDefined state.memory (panByteAlignHOL (width := 64) address) = true :=
      (panValueFlatMachineDomain_iff state exact hm hmd _).mpr hexact
    simp only [panMemLoadByteHOL, if_pos hdom, if_pos hexact]
    rw [hmem, ← hbe]
  · have hdom : ¬ (state.memaddrs (panByteAlignHOL (width := 64) address)
        && panValueWordDefined state.memory (panByteAlignHOL (width := 64) address) = true) :=
      fun h => hexact ((panValueFlatMachineDomain_iff state exact hm hmd _).mp h)
    simp only [panMemLoadByteHOL, if_neg hdom, if_neg hexact]

/-- The executed comparison is the exact `word_cmp` word encoding. -/
theorem panSemBitVec64MemoryAccess_compare {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (operator : Cmp)
    (left right : RiscV.Word 64) :
    (panSemBitVec64MemoryAccess state).compare operator left right =
      (if Compiler.Encoders.Asm.wordCmpHOL operator left right then 1 else 0) := by
  change RiscV.panRiscVCmp operator left right = _
  rw [panRiscVCmp_eq_wordCmpResultHOL]
  rfl

/-- The executed shift is the exact `word_sh`. -/
theorem panSemBitVec64MemoryAccess_shift {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (operator : Shift)
    (left right : RiscV.Word 64) :
    (panSemBitVec64MemoryAccess state).shift operator left right =
      wordShiftHOL operator left right.toNat := by
  change RiscV.panRiscVShift operator left right = _
  rw [panRiscVShift_eq_wordShiftHOL]

/-- A 32-bit value widened by `ofNat` is its `setWidth` image. -/
@[simp] theorem bitVecOfNat64_eq_setWidth (v : RiscV.Word 32) :
    BitVec.ofNat 64 v.toNat = BitVec.setWidth 64 v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := v.isLt; omega),
    BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt]
  have := v.isLt
  omega

/-- The production `bytes_in_word` is the exact `bytesInWordHOL`. -/
theorem panSemBitVec64BytesInWord_eq : panSemBitVec64BytesInWord = bytesInWordHOL 64 := rfl

/-- Word projection of the encoding. -/
theorem panValueWordProjection_panValueToHOL {width : Nat} [NeZero width]
    (v : PanValue (BitVec width)) :
    panValueWordProjection v =
      (if valueIsWord (panValueToHOL v) then some (valueWord (panValueToHOL v)) else none) := by
  induction v using panValueToHOL.induct with
  | case1 b => simp [panValueWordProjection, valueIsWord, valueWord]
  | case2 fields ih => simp [panValueWordProjection, valueIsWord]
  | case3 name fields ih => simp [panValueWordProjection, valueIsWord]

/-- List map with the word projection. -/
theorem mapM_panValueWordProjection_panValueToHOL {width : Nat} [NeZero width]
    (values : List (PanValue (BitVec width))) :
    values.mapM panValueWordProjection =
      (if (values.map panValueToHOL).all valueIsWord
        then some ((values.map panValueToHOL).map valueWord) else none) := by
  induction values with
  | nil => simp
  | cons v vs ih =>
      simp only [List.map_cons, List.mapM_cons, List.all_cons]
      rw [panValueWordProjection_panValueToHOL v]
      cases hw : valueIsWord (panValueToHOL v) <;>
        cases hr : (vs.map panValueToHOL).all valueIsWord <;> simp_all

/-! ## Per-constructor agreement lemmas -/

theorem evalPanValueExp_const_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (access : Option (PanValueMemoryAccess (RiscV.Word 64))) (value : RiscV.Word 64) :
    Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord (.const value)
          (memoryAccess := access))
      = exact.evalHOLFinite (.const value) := by
  simp only [evalPanValueExp, PanSemStateFiniteExact.evalHOLFinite_const,
    Option.map_some, panValueToHOL_word]

theorem evalPanValueExp_var_local_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (access : Option (PanValueMemoryAccess (RiscV.Word 64))) (name : String)
    (hname : NameRanged name) :
    Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord (.var .local name)
          (memoryAccess := access))
      = exact.evalHOLFinite (.var .local (ofString name)) := by
  simpa only [evalPanValueExp, PanSemStateFiniteExact.evalHOLFinite_var_local] using
    hrel.1 name hname

theorem evalPanValueExp_var_global_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (access : Option (PanValueMemoryAccess (RiscV.Word 64))) (name : String)
    (hname : NameRanged name) :
    Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord (.var .global name)
          (memoryAccess := access))
      = exact.evalHOLFinite (.var .global (ofString name)) := by
  simpa only [evalPanValueExp, PanSemStateFiniteExact.evalHOLFinite_var_global] using
    hrel.2.1 name hname

theorem evalPanValueExp_baseAddr_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (access : Option (PanValueMemoryAccess (RiscV.Word 64))) :
    Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord .baseAddr
          (memoryAccess := access))
      = exact.evalHOLFinite .baseAddr := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hbase, _⟩ := hrel
  have hbase' : exact.baseAddr = state.baseAddress := hbase
  simp only [evalPanValueExp, PanSemStateFiniteExact.evalHOLFinite_baseAddr,
    Option.map_some, panValueToHOL_word, hbase']

theorem evalPanValueExp_topAddr_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (access : Option (PanValueMemoryAccess (RiscV.Word 64))) :
    Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord .topAddr
          (memoryAccess := access))
      = exact.evalHOLFinite .topAddr := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, htop⟩ := hrel
  have htop' : exact.topAddr = state.topAddress := htop
  simp only [evalPanValueExp, PanSemStateFiniteExact.evalHOLFinite_topAddr,
    Option.map_some, panValueToHOL_word, htop']

theorem evalPanValueExp_bytesInWord_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (access : Option (PanValueMemoryAccess (RiscV.Word 64))) :
    Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord .bytesInWord
          (memoryAccess := access))
      = exact.evalHOLFinite .bytesInWord := by
  simp only [evalPanValueExp, PanSemStateFiniteExact.evalHOLFinite_bytesInWord,
    Option.map_some, panValueToHOL_word, panSemBitVec64BytesInWord_eq]

theorem evalPanValueExp_rStruct_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (access : Option (PanValueMemoryAccess (RiscV.Word 64)))
    (fields : List (Exp (RiscV.Word 64)))
    (hfields : ∀ e ∈ fields,
      Option.map panValueToHOL
          (evalPanValueExp state.structs state.locals state.globals state.memory
            state.baseAddress state.topAddress panSemBitVec64BytesInWord e
            (memoryAccess := access))
        = exact.evalHOLFinite (expToHOL e)) :
    Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord (.rStruct fields)
          (memoryAccess := access))
      = exact.evalHOLFinite (.rstruct (fields.map expToHOL)) := by
  simp only [evalPanValueExp, PanSemStateFiniteExact.evalHOLFinite_rstruct]
  have hl := evalPanValueExps_eq_evalListHOLExact_of state.structs state.locals state.globals
    state.memory state.baseAddress state.topAddress panSemBitVec64BytesInWord access exact fields hfields
  have key : Option.map panValueToHOL
      (Option.map PanValue.rStruct
        (evalPanValueExp.evalPanValueExps state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord fields (memoryAccess := access)))
      = Option.map ValueHOL.rStruct
          (Option.map (List.map panValueToHOL)
            (evalPanValueExp.evalPanValueExps state.structs state.locals state.globals state.memory
              state.baseAddress state.topAddress panSemBitVec64BytesInWord fields (memoryAccess := access))) := by
    rw [Option.map_map, Option.map_map]
    congr 1
    funext fs
    simp [Function.comp_apply, panValueToHOL_rStruct]
  rw [key, hl]

theorem evalPanValueExp_rField_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (access : Option (PanValueMemoryAccess (RiscV.Word 64)))
    (index : Nat) (value : Exp (RiscV.Word 64))
    (hvalue : Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord value
          (memoryAccess := access))
      = exact.evalHOLFinite (expToHOL value)) :
    Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord (.rField index value)
          (memoryAccess := access))
      = exact.evalHOLFinite (.rfield index (expToHOL value)) := by
  simp only [evalPanValueExp, PanSemStateFiniteExact.evalHOLFinite_rfield]
  cases hp : evalPanValueExp state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress panSemBitVec64BytesInWord value
      (memoryAccess := access) with
  | none =>
      rw [hp] at hvalue
      simp only [Option.map_none] at hvalue
      rw [← hvalue]
      simp
  | some pv =>
      rw [hp] at hvalue
      simp only [Option.map_some] at hvalue
      rw [← hvalue]
      cases pv with
      | word bits => simp [panValueToHOL_word]
      | rStruct fs => simp [panValueToHOL_rStruct, List.getElem?_map]
      | nStruct name fs => simp [panValueToHOL_nStruct]

theorem evalPanValueExp_op_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (access : PanValueMemoryAccess (RiscV.Word 64))
    (operator : BinOp) (arguments : List (Exp (RiscV.Word 64)))
    (hargs : ∀ e ∈ arguments,
      Option.map panValueToHOL
          (evalPanValueExp state.structs state.locals state.globals state.memory
            state.baseAddress state.topAddress panSemBitVec64BytesInWord e
            (memoryAccess := some access))
        = exact.evalHOLFinite (expToHOL e))
    (hwordOp : ∀ (op : BinOp) (values : List (RiscV.Word 64)),
      access.wordOp op values = wordOpHOL op values) :
    Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord (.op operator arguments)
          (memoryAccess := some access))
      = exact.evalHOLFinite (.op operator (arguments.map expToHOL)) := by
  simp only [evalPanValueExp, PanSemStateFiniteExact.evalHOLFinite_op]
  have hl := evalPanValueExps_eq_evalListHOLExact_of state.structs state.locals state.globals
    state.memory state.baseAddress state.topAddress panSemBitVec64BytesInWord (some access) exact
    arguments hargs
  cases hv : evalPanValueExp.evalPanValueExps state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress panSemBitVec64BytesInWord arguments
      (memoryAccess := some access) with
  | none =>
      rw [hv] at hl
      simp only [Option.map_none] at hl
      rw [← hl]
      simp
  | some values =>
      rw [hv] at hl
      simp only [Option.map_some] at hl
      rw [← hl]
      dsimp only
      change Option.map panValueToHOL
          (Option.bind (some values) (fun v => Option.bind (List.mapM panValueWordProjection v)
            (fun words => Option.map PanValue.word (access.wordOp operator words))))
        = (if (values.map panValueToHOL).all valueIsWord = true
            then Option.map (fun w => ValueHOL.val (HolWordLab.word w))
              (wordOpHOL operator ((values.map panValueToHOL).map valueWord))
            else none)
      rw [Option.bind_some]
      by_cases hall : (values.map panValueToHOL).all valueIsWord = true
      · rw [if_pos hall]
        rw [mapM_panValueWordProjection_panValueToHOL values, if_pos hall, Option.bind_some,
          hwordOp, Option.map_map]
        congr 1
        funext w
        simp [Function.comp_apply, panValueToHOL_word]
      · rw [if_neg hall]
        rw [mapM_panValueWordProjection_panValueToHOL values, if_neg hall]
        simp

theorem evalPanValueExp_panOp_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (access : Option (PanValueMemoryAccess (RiscV.Word 64)))
    (operator : PanOp) (arguments : List (Exp (RiscV.Word 64)))
    (hargs : ∀ e ∈ arguments,
      Option.map panValueToHOL
          (evalPanValueExp state.structs state.locals state.globals state.memory
            state.baseAddress state.topAddress panSemBitVec64BytesInWord e
            (memoryAccess := access))
        = exact.evalHOLFinite (expToHOL e)) :
    Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord (.panOp operator arguments)
          (memoryAccess := access))
      = exact.evalHOLFinite (.panop operator (arguments.map expToHOL)) := by
  simp only [evalPanValueExp, PanSemStateFiniteExact.evalHOLFinite_panop]
  have hl := evalPanValueExps_eq_evalListHOLExact_of state.structs state.locals state.globals
    state.memory state.baseAddress state.topAddress panSemBitVec64BytesInWord access exact
    arguments hargs
  cases hv : evalPanValueExp.evalPanValueExps state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress panSemBitVec64BytesInWord arguments
      (memoryAccess := access) with
  | none =>
      rw [hv] at hl
      simp only [Option.map_none] at hl
      rw [← hl]
      simp
  | some values =>
      rw [hv] at hl
      simp only [Option.map_some] at hl
      rw [← hl]
      dsimp only
      cases values with
      | nil => simp [panOpHOL_nil]
      | cons a as =>
          cases as with
          | nil =>
              cases a <;>
                simp [valueIsWord, panOpHOL_one, panValueToHOL_rStruct, panValueToHOL_nStruct]
          | cons b bs =>
              cases bs with
              | nil =>
                  cases a <;> cases b <;>
                    simp [valueIsWord, valueWord, panOpHOL, evalPanOp_eq_panOpHOL,
                      panValueToHOL_rStruct, panValueToHOL_nStruct]
              | cons c cs =>
                  cases a <;> cases b <;> cases c <;>
                    simp [valueIsWord, panOpHOL_three, panValueToHOL_rStruct,
                      panValueToHOL_nStruct]

theorem evalPanValueExp_cmp_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (access : PanValueMemoryAccess (RiscV.Word 64))
    (operator : Cmp) (left right : Exp (RiscV.Word 64))
    (hleft : Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord left
          (memoryAccess := some access))
      = exact.evalHOLFinite (expToHOL left))
    (hright : Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord right
          (memoryAccess := some access))
      = exact.evalHOLFinite (expToHOL right))
    (hcmp : ∀ (op : Cmp) (l r : RiscV.Word 64),
      access.compare op l r =
        (if Compiler.Encoders.Asm.wordCmpHOL op l r then 1 else 0)) :
    Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord (.cmp operator left right)
          (memoryAccess := some access))
      = exact.evalHOLFinite (.cmp operator (expToHOL left) (expToHOL right)) := by
  simp only [evalPanValueExp, PanSemStateFiniteExact.evalHOLFinite_cmp]
  cases hl : evalPanValueExp state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress panSemBitVec64BytesInWord left
      (memoryAccess := some access) with
  | none =>
      rw [hl] at hleft
      simp only [Option.map_none] at hleft
      rw [← hleft]
      simp
  | some lv =>
      rw [hl] at hleft
      simp only [Option.map_some] at hleft
      cases hr : evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord right
          (memoryAccess := some access) with
      | none =>
          rw [hr] at hright
          simp only [Option.map_none] at hright
          rw [← hleft, ← hright]
          simp
      | some rv =>
          rw [hr] at hright
          simp only [Option.map_some] at hright
          rw [← hleft, ← hright]
          cases lv <;> cases rv <;>
            simp [hcmp, panValueToHOL_word, panValueToHOL_rStruct, panValueToHOL_nStruct]

theorem evalPanValueExp_shift_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (access : PanValueMemoryAccess (RiscV.Word 64))
    (operator : Shift) (left right : Exp (RiscV.Word 64))
    (hleft : Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord left
          (memoryAccess := some access))
      = exact.evalHOLFinite (expToHOL left))
    (hright : Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord right
          (memoryAccess := some access))
      = exact.evalHOLFinite (expToHOL right))
    (hshift : ∀ (op : Shift) (l r : RiscV.Word 64),
      access.shift op l r = wordShiftHOL op l r.toNat) :
    Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord (.shift operator left right)
          (memoryAccess := some access))
      = exact.evalHOLFinite (.shift operator (expToHOL left) (expToHOL right)) := by
  simp only [evalPanValueExp, PanSemStateFiniteExact.evalHOLFinite_shift]
  cases hl : evalPanValueExp state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress panSemBitVec64BytesInWord left
      (memoryAccess := some access) with
  | none =>
      rw [hl] at hleft
      simp only [Option.map_none] at hleft
      rw [← hleft]
      simp
  | some lv =>
      rw [hl] at hleft
      simp only [Option.map_some] at hleft
      cases hr : evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord right
          (memoryAccess := some access) with
      | none =>
          rw [hr] at hright
          simp only [Option.map_none] at hright
          rw [← hleft, ← hright]
          simp
      | some rv =>
          rw [hr] at hright
          simp only [Option.map_some] at hright
          rw [← hleft, ← hright]
          cases lv <;> cases rv <;>
            simp [hshift, panValueToHOL_word, panValueToHOL_comp_word,
              panValueToHOL_rStruct, panValueToHOL_nStruct]

theorem evalPanValueExp_load32_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (address : Exp (RiscV.Word 64))
    (haddress : Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord address
          (memoryAccess := some (panSemBitVec64MemoryAccess state)))
      = exact.evalHOLFinite (expToHOL address)) :
    Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord (.load32 address)
          (memoryAccess := some (panSemBitVec64MemoryAccess state)))
      = exact.evalHOLFinite (.load32 (expToHOL address)) := by
  simp only [evalPanValueExp, PanSemStateFiniteExact.evalHOLFinite_load32]
  cases hp : evalPanValueExp state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress panSemBitVec64BytesInWord address
      (memoryAccess := some (panSemBitVec64MemoryAccess state)) with
  | none =>
      rw [hp] at haddress
      simp only [Option.map_none] at haddress
      rw [← haddress]
      rfl
  | some pv =>
      rw [hp] at haddress
      simp only [Option.map_some] at haddress
      rw [← haddress]
      cases pv with
      | word bits =>
          simp
          rw [panSemBitVec64Read32_eq_panMemLoad32HOL,
            panMemLoad32HOL_agree state exact hrel bits]
          rw [Option.map_map]
          congr 1
          funext value
          rw [Function.comp_apply, bitVecOfNat64_eq_setWidth]
      | rStruct fs => simp [panValueToHOL_rStruct]
      | nStruct nm fs => simp [panValueToHOL_nStruct]

theorem evalPanValueExp_loadByte_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (address : Exp (RiscV.Word 64))
    (haddress : Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord address
          (memoryAccess := some (panSemBitVec64MemoryAccess state)))
      = exact.evalHOLFinite (expToHOL address)) :
    Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord (.loadByte address)
          (memoryAccess := some (panSemBitVec64MemoryAccess state)))
      = exact.evalHOLFinite (.loadByte (expToHOL address)) := by
  simp only [evalPanValueExp, PanSemStateFiniteExact.evalHOLFinite_loadByte]
  cases hp : evalPanValueExp state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress panSemBitVec64BytesInWord address
      (memoryAccess := some (panSemBitVec64MemoryAccess state)) with
  | none =>
      rw [hp] at haddress
      simp only [Option.map_none] at haddress
      rw [← haddress]
      rfl
  | some pv =>
      rw [hp] at haddress
      simp only [Option.map_some] at haddress
      rw [← haddress]
      cases pv with
      | word bits =>
          simp
          rw [panSemBitVec64ReadByte_eq_panMemLoadByteHOL,
            panMemLoadByteHOL_agree state exact hrel bits]
          rw [Option.map_map]
          congr 1
      | rStruct fs => simp [panValueToHOL_rStruct]
      | nStruct nm fs => simp [panValueToHOL_nStruct]

/-! ## Structured-carrier bridges for the `.nStruct`/`.nField`/`.load` clauses

The three structured constructors (`nStruct`/`nField`/`load`) need the
production `String`-keyed carriers
(`StructContext`/`StructContextHOL`/`HolValue`/`Shape`) bridged to the
exact `MlString`-keyed carriers (`StructContextExact`/`ValueHOL`/`ShapeHOL`)
under the byte-range premises.  `holValueToHOL` is the forward value codec,
`structContextLookupHOL_structContextToHOL` the context lookup bridge,
`sizeOfShWithCtxt_eq_sizeOfShapeWithContextHOL` the context-sensitive size
bridge, and `isWfShapeHOL_eq_isWfShapeExactHOL` the well-formedness bridge.
Everything below is untagged Flapjack bridge infrastructure. -/

/-- Forward codec from the production-shaped `HolValue` to the exact `ValueHOL`;
    names go through `ofString` and word payloads are preserved. -/
def holValueToHOL {width : Nat} [NeZero width] : HolValue width → ValueHOL width
  | .val (.word bits) => .val (.word bits)
  | .rStruct fields => .rStruct (fields.map holValueToHOL)
  | .nStruct name fields =>
      .nStruct (ofString name) (fields.map (fun p => (ofString p.1, holValueToHOL p.2)))
termination_by value => sizeOf value
decreasing_by
  all_goals
    simp_wf
    first
      | (rename_i hmem
         have hlt := List.sizeOf_lt_of_mem hmem
         omega)
      | (rename_i hmem
         have hsnd : sizeOf p.snd < sizeOf p := by cases p; simp +arith
         have hlt := List.sizeOf_lt_of_mem hmem
         omega)

/-- The `HolValue` codec is the composition of the production value codec with
    the `HolValue`/`PanValue` isomorphism. -/
theorem panValueToHOL_toPanValue {width : Nat} [NeZero width] (value : HolValue width) :
    panValueToHOL (HolValue.toPanValue value) = holValueToHOL value := by
  induction value using HolValue.toPanValue.induct with
  | case1 bits => simp only [HolValue.toPanValue, panValueToHOL, holValueToHOL]
  | case2 fields ih =>
      simp only [HolValue.toPanValue, panValueToHOL, holValueToHOL, List.map_map]
      congr 1
      apply List.map_congr_left
      intro x hx
      exact ih x hx
  | case3 name fields ih =>
      simp only [HolValue.toPanValue, panValueToHOL, holValueToHOL, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      obtain ⟨an, av⟩ := a
      simp only [Function.comp_apply]
      exact congrArg (fun v => (ofString an, v)) (ih (an, av) ha)

/-- Lookup commutes with `structContextToHOL` on byte-ranged contexts. -/
theorem structContextLookupHOL_structContextToHOL (name : String)
    (ctx : StructContextHOL) (hname : NameRanged name)
    (hrange : ∀ p ∈ ctx, NameRanged p.1) :
    structContextLookupHOL (ofString name) (structContextToHOL ctx)
      = (lookupInfo name ctx).map structInfoToHOL := by
  induction ctx with
  | nil => simp only [structContextToHOL, List.map_nil, lookupInfo, structContextLookupHOL,
      Option.map_none]
  | cons entry rest ih =>
      obtain ⟨candidate, info⟩ := entry
      have hrangeTail : ∀ p ∈ rest, NameRanged p.1 := fun p hp => hrange p (by simp [hp])
      have hcandidate : NameRanged candidate := hrange (candidate, info) (by simp)
      simp only [structContextToHOL, List.map_cons, lookupInfo, structContextLookupHOL]
      by_cases hc : candidate == name
      · have heq : candidate = name := beq_iff_eq.mp hc
        subst heq
        simp only [beq_self_eq_true, if_pos, Option.map_some]
      · have hne : candidate ≠ name := fun h => hc (beq_iff_eq.mpr h)
        have hofne : ofString name ≠ ofString candidate :=
          fun h => hne (ofString_injective_of_ranged hname hcandidate h).symm
        rw [if_neg hc, if_neg hofne]
        exact ih hrangeTail

/-- Encode a production cache-augmented `StructInfo` (dropping `shapedFields`)
    into the exact `mlstring`-keyed `struct_info`. -/
def structInfoCacheToHOL (info : StructInfo) : StructInfoHOLExact :=
  { fields := info.fields.map (fun f => (ofString f.1, shapeToHOL f.2)), size := info.size }

/-- Context lookup bridges to the cache-augmented `struct_info` encoding. -/
theorem lookupInfo_panStructContextToHOL' (name : String) (context : StructContext)
    (hname : NameRanged name) (hrange : ∀ p ∈ context, NameRanged p.1) :
    structContextLookupHOL (ofString name) (panStructContextToHOL context)
      = (lookupInfo name context).map structInfoCacheToHOL := by
  rw [lookupInfo_panStructContextToHOL name context hname hrange]
  rfl

/-- The context-sensitive shape size agrees with its exact `MlString`-keyed
    counterpart under byte-range premises. -/
theorem sizeOfShWithCtxt_eq_sizeOfShapeWithContextHOL (ctx : StructContextHOL)
    (hrange : ∀ p ∈ ctx, NameRanged p.1) :
    ∀ (shape : Shape), ShapeByteRanged shape →
      sizeOfShWithCtxt ctx shape =
        sizeOfShapeWithContextHOL (structContextToHOL ctx) (shapeToHOL shape) := by
  intro shape
  induction shape using sizeOfShWithCtxt.induct (context := ctx) with
  | case1 => intro _; simp only [sizeOfShWithCtxt, sizeOfShapeWithContextHOL, shapeToHOL]
  | case2 shapes ih =>
      intro h
      have hcomb : ∀ s ∈ shapes, ShapeByteRanged s := by
        simpa only [ShapeByteRanged] using h
      simp only [sizeOfShWithCtxt, sizeOfShapeWithContextHOL, shapeToHOL]
      refine (foldl_sizeOfShWithCtxt_eq_sizeOfShapesHOL ctx shapes 0 ?_).trans ?_
      · intro s hs
        exact ih s hs (hcomb s hs)
      · simp only [Nat.zero_add]
  | case3 name info hlookup =>
      intro h
      have hname : NameRanged name := by simpa only [ShapeByteRanged] using h
      simp only [sizeOfShWithCtxt, sizeOfShapeWithContextHOL, shapeToHOL]
      rw [structContextLookupHOL_structContextToHOL name ctx hname hrange, hlookup]
      rfl
  | case4 name hlookup =>
      intro h
      have hname : NameRanged name := by simpa only [ShapeByteRanged] using h
      simp only [sizeOfShWithCtxt, sizeOfShapeWithContextHOL, shapeToHOL]
      rw [structContextLookupHOL_structContextToHOL name ctx hname hrange, hlookup]
      rfl
where
  foldl_sizeOfShWithCtxt_eq_sizeOfShapesHOL (ctx : StructContextHOL)
      (shapes : List Shape) (acc : Nat)
      (h : ∀ s ∈ shapes,
        sizeOfShWithCtxt ctx s = sizeOfShapeWithContextHOL (structContextToHOL ctx) (shapeToHOL s)) :
      shapes.foldl (fun total shape => total + sizeOfShWithCtxt ctx shape) acc =
        acc + sizeOfShapesWithContextHOL (structContextToHOL ctx) (shapes.map shapeToHOL) := by
    induction shapes generalizing acc with
    | nil => simp only [List.foldl_nil, List.map_nil, sizeOfShapesWithContextHOL, Nat.add_zero]
    | cons s ss ih =>
        rw [List.foldl_cons, ih (acc + sizeOfShWithCtxt ctx s)
          (fun x hx => h x (by simp [hx]))]
        rw [List.map_cons, sizeOfShapesWithContextHOL_cons, h s (by simp)]
        omega

/-- The production well-formedness predicate agrees with the exact one under
    byte-range premises. -/
theorem isWfShapeHOL_eq_isWfShapeExactHOL (ctx : StructContextHOL)
    (hrange : ∀ p ∈ ctx, NameRanged p.1) :
    ∀ (shape : Shape), ShapeByteRanged shape →
      isWfShapeHOL ctx shape = isWfShapeExactHOL (structContextToHOL ctx) (shapeToHOL shape) := by
  apply isWfShapeHOL.induct
    (motive1 := fun shape => ShapeByteRanged shape →
      isWfShapeHOL ctx shape = isWfShapeExactHOL (structContextToHOL ctx) (shapeToHOL shape))
    (motive2 := fun shapes => (∀ s ∈ shapes, ShapeByteRanged s) →
      isWfShapeListHOL ctx shapes =
        isWfShapesExactHOL (structContextToHOL ctx) (shapes.map shapeToHOL))
  · intro _; simp only [isWfShapeHOL, isWfShapeExactHOL, shapeToHOL]
  · intro a ih h
    have ha : ∀ s ∈ a, ShapeByteRanged s := by simpa only [ShapeByteRanged] using h
    simp only [isWfShapeHOL, isWfShapeExactHOL, shapeToHOL]
    exact ih ha
  · intro a h
    have hname : NameRanged a := by simpa only [ShapeByteRanged] using h
    simp only [isWfShapeHOL, isWfShapeExactHOL, shapeToHOL]
    rw [structContextLookupHOL_structContextToHOL a ctx hname hrange, Option.isSome_map]
  · intro _; simp only [isWfShapeListHOL, isWfShapesExactHOL, List.map_nil]
  · intro shape shapes ihShape ihShapes h
    have hshape : ShapeByteRanged shape := h shape (by simp)
    have hshapes : ∀ s ∈ shapes, ShapeByteRanged s := fun s hs => h s (by simp [hs])
    simp only [isWfShapeListHOL, isWfShapesExactHOL, List.map_cons]
    rw [ihShape hshape, ihShapes hshapes]

/-- The production `panMemLoadHOL` load over `String`-keyed contexts agrees with
    the exact `memLoadHOLExact` load over `mlstring`-keyed contexts, under the
    name/shape byte-range premises. -/
theorem panMemLoadHOL_map_holValueToHOL {width : Nat} [NeZero width]
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (memory : RiscV.Word width → HolWordLab width)
    (domainE : RiscV.Word width → Prop) [DecidablePred domainE]
    (memoryE : RiscV.Word width → HolWordLab width)
    (hdom : ∀ a, domain a ↔ domainE a) (hmem : ∀ a, domainE a → memory a = memoryE a) :
    ∀ (shape : Shape) (address : RiscV.Word width) (ctx : StructContextHOL),
      (∀ p ∈ ctx, NameRanged p.1) →
      (∀ p ∈ ctx, StructInfoByteRanged p.2) →
      ShapeByteRanged shape →
      ((panMemLoadHOL shape address domain memory ctx).map
          (holValueToHOL (width := width)) : Option (ValueHOL width)) =
        memLoadHOLExact (shapeToHOL shape) address domainE memoryE (structContextToHOL ctx) := by
  apply panMemLoadHOL.induct (domain := domain) (memory := memory)
    (motive1 := fun shape address ctx =>
      (∀ p ∈ ctx, NameRanged p.1) →
      (∀ p ∈ ctx, StructInfoByteRanged p.2) →
      ShapeByteRanged shape →
      ((panMemLoadHOL shape address domain memory ctx).map
          (holValueToHOL (width := width)) : Option (ValueHOL width)) =
        memLoadHOLExact (shapeToHOL shape) address domainE memoryE (structContextToHOL ctx))
    (motive2 := fun fields address ctx =>
      (∀ p ∈ ctx, NameRanged p.1) →
      (∀ p ∈ ctx, StructInfoByteRanged p.2) →
      ListParamByteRanged fields →
      ((panMemLoadFldsHOL fields address domain memory ctx).map
          (List.map (fun p => (ofString p.1, holValueToHOL (width := width) p.2))) :
        Option (List (MlS × ValueHOL width))) =
        memLoadFldsHOLExact (fields.map paramToHOL) address domainE memoryE (structContextToHOL ctx))
    (motive3 := fun shapes address ctx =>
      (∀ p ∈ ctx, NameRanged p.1) →
      (∀ p ∈ ctx, StructInfoByteRanged p.2) →
      (∀ s ∈ shapes, ShapeByteRanged s) →
      ((panMemLoadsHOL shapes address domain memory ctx).map
          (List.map (holValueToHOL (width := width))) : Option (List (ValueHOL width))) =
        memLoadsHOLExact (shapes.map shapeToHOL) address domainE memoryE (structContextToHOL ctx))
  case case1 =>
    intro address ctx hdomA hr hi hs
    simp only [panMemLoadHOL, shapeToHOL, memLoadHOLExact]
    rw [if_pos hdomA, if_pos ((hdom address).mp hdomA),
      hmem address ((hdom address).mp hdomA)]
    cases memoryE address with
    | word bits =>
        simp only [HolWordLab.toPanWordLab, holValueToHOL, Option.map_some]
  case case2 =>
    intro address ctx hndomA hr hi hs
    have hndomE : ¬ domainE address := fun h => hndomA ((hdom address).mpr h)
    simp only [panMemLoadHOL, shapeToHOL, memLoadHOLExact, hndomA, hndomE, if_false,
      Option.map_none]
  case case3 =>
    intro address ctx shapes values hloads ih hr hi hs
    have hshapes : ∀ s ∈ shapes, ShapeByteRanged s := by
      simpa only [ShapeByteRanged] using hs
    have hih := ih hr hi hshapes
    rw [hloads] at hih
    simp only [Option.map_some] at hih
    simp only [panMemLoadHOL, hloads, Option.map_some, holValueToHOL, shapeToHOL, memLoadHOLExact]
    rw [show memLoadsHOLExact (shapes.map shapeToHOL) address domainE memoryE
          (structContextToHOL ctx) = some (values.map holValueToHOL) from hih.symm]
  case case4 =>
    intro address ctx shapes hloads ih hr hi hs
    have hshapes : ∀ s ∈ shapes, ShapeByteRanged s := by
      simpa only [ShapeByteRanged] using hs
    have hih := ih hr hi hshapes
    rw [hloads] at hih
    simp only [Option.map_none] at hih
    simp only [panMemLoadHOL, hloads, Option.map_none, shapeToHOL, memLoadHOLExact]
    rw [hih.symm]
  case case5 =>
    intro address name hr hi hs
    simp only [panMemLoadHOL, memLoadHOLExact, structContextToHOL, List.map_nil,
      Option.map_none, shapeToHOL]
  case case6 =>
    intro address name candidate info rest hc fields hfields ih hr hi hs
    have hname : NameRanged name := by simpa only [ShapeByteRanged] using hs
    have hcand : NameRanged candidate := hr (candidate, info) (by simp)
    have heq : candidate = name := beq_iff_eq.mp hc
    have hrTail : ∀ p ∈ rest, NameRanged p.1 := fun p hp => hr p (by simp [hp])
    have hiTail : ∀ p ∈ rest, StructInfoByteRanged p.2 := fun p hp => hi p (by simp [hp])
    have hfr : ListParamByteRanged info.fields := by
      simpa only [StructInfoByteRanged] using hi (candidate, info) (by simp)
    have hih := ih hrTail hiTail hfr
    rw [hfields] at hih
    simp only [Option.map_some] at hih
    simp only [panMemLoadHOL, hc, if_true, hfields, Option.map_some, holValueToHOL]
    rw [heq]
    simp only [shapeToHOL, memLoadHOLExact, structContextToHOL, List.map_cons, structInfoToHOL]
    simp only [if_true]
    rw [show memLoadFldsHOLExact (info.fields.map paramToHOL) address domainE memoryE
          (List.map (fun p => (ofString p.fst, { fields := List.map paramToHOL p.snd.fields, size := p.snd.size })) rest) =
          some (fields.map (fun p => (ofString p.1, holValueToHOL (width := width) p.2))) from
        hih.symm]
  case case7 =>
    intro address name candidate info rest hc hfields ih hr hi hs
    have hname : NameRanged name := by simpa only [ShapeByteRanged] using hs
    have hcand : NameRanged candidate := hr (candidate, info) (by simp)
    have heq : candidate = name := beq_iff_eq.mp hc
    have hrTail : ∀ p ∈ rest, NameRanged p.1 := fun p hp => hr p (by simp [hp])
    have hiTail : ∀ p ∈ rest, StructInfoByteRanged p.2 := fun p hp => hi p (by simp [hp])
    have hfr : ListParamByteRanged info.fields := by
      simpa only [StructInfoByteRanged] using hi (candidate, info) (by simp)
    have hih := ih hrTail hiTail hfr
    rw [hfields] at hih
    simp only [Option.map_none] at hih
    simp only [panMemLoadHOL, hc, if_true, hfields, Option.map_none]
    rw [heq]
    simp only [shapeToHOL, memLoadHOLExact, structContextToHOL, List.map_cons, structInfoToHOL]
    simp only [if_true]
    rw [show memLoadFldsHOLExact (info.fields.map paramToHOL) address domainE memoryE
          (List.map (fun p => (ofString p.fst, { fields := List.map paramToHOL p.snd.fields, size := p.snd.size })) rest) = none from hih.symm]
  case case8 =>
    intro address name candidate info rest hc ih hr hi hs
    have hname : NameRanged name := by simpa only [ShapeByteRanged] using hs
    have hcand : NameRanged candidate := hr (candidate, info) (by simp)
    have hc' : (candidate == name) = false := by simpa using hc
    have hne : candidate ≠ name := fun h => by
      rw [beq_iff_eq.mpr h] at hc'
      exact Bool.noConfusion hc'
    have hofne : ofString candidate ≠ ofString name :=
      fun h => hne (ofString_injective_of_ranged hcand hname h)
    have hrTail : ∀ p ∈ rest, NameRanged p.1 := fun p hp => hr p (by simp [hp])
    have hiTail : ∀ p ∈ rest, StructInfoByteRanged p.2 := fun p hp => hi p (by simp [hp])
    have hih := ih hrTail hiTail hs
    simp only [panMemLoadHOL, hc', Bool.false_eq_true, if_false, shapeToHOL, memLoadHOLExact,
      structContextToHOL, List.map_cons]
    rw [if_neg hofne]
    simpa only [shapeToHOL, structContextToHOL] using hih
  case case9 =>
    intro address ctx hr hi hfields
    simp only [panMemLoadFldsHOL, memLoadFldsHOLExact, List.map_nil, Option.map_some]
  case case10 =>
    intro address ctx field shape rest value values htail hhead ihHead ihTail hr hi hfields
    have hfr : ParamByteRanged (field, shape) := by
      simpa only [ListParamByteRanged] using hfields (field, shape) (by simp)
    obtain ⟨hfieldName, hshape⟩ := hfr
    have hrestRanged : ListParamByteRanged rest := by
      intro p hp
      exact hfields p (by simp [hp])
    have hsize : panBytesInWord width * BitVec.ofNat width (sizeOfShWithCtxt ctx shape) =
        bytesInWordHOL width * BitVec.ofNat width
          (sizeOfShapeWithContextHOL (structContextToHOL ctx) (shapeToHOL shape)) := by
      rw [show panBytesInWord width = bytesInWordHOL width from rfl,
        sizeOfShWithCtxt_eq_sizeOfShapeWithContextHOL ctx hr shape hshape]
    have hihHead := ihHead hr hi hshape
    rw [hhead] at hihHead
    simp only [Option.map_some] at hihHead
    have htailE := htail
    rw [hsize] at htailE
    have hihTail := ihTail hr hi hrestRanged
    rw [hsize] at hihTail
    rw [htailE] at hihTail
    simp only [Option.map_some] at hihTail
    simp only [panMemLoadFldsHOL, memLoadFldsHOLExact, hhead, htailE, hsize, List.map_cons,
      Option.map_some, paramToHOL, hihHead.symm, hihTail.symm]
  case case11 =>
    intro address ctx field shape rest hfail ihHead ihTail hr hi hfields
    have hfr : ParamByteRanged (field, shape) := by
      simpa only [ListParamByteRanged] using hfields (field, shape) (by simp)
    obtain ⟨hfieldName, hshape⟩ := hfr
    have hrestRanged : ListParamByteRanged rest := by
      intro p hp
      exact hfields p (by simp [hp])
    have hsize : panBytesInWord width * BitVec.ofNat width (sizeOfShWithCtxt ctx shape) =
        bytesInWordHOL width * BitVec.ofNat width
          (sizeOfShapeWithContextHOL (structContextToHOL ctx) (shapeToHOL shape)) := by
      rw [show panBytesInWord width = bytesInWordHOL width from rfl,
        sizeOfShWithCtxt_eq_sizeOfShapeWithContextHOL ctx hr shape hshape]
    have hihHead := ihHead hr hi hshape
    have hihTail := ihTail hr hi hrestRanged
    rw [hsize] at hihTail
    simp only [panMemLoadFldsHOL, memLoadFldsHOLExact, hsize, List.map_cons, paramToHOL]
    cases hh : panMemLoadHOL shape address domain memory ctx with
    | none =>
        rw [hh] at hihHead
        simp only [Option.map_none] at hihHead
        rw [show memLoadHOLExact (shapeToHOL shape) address domainE memoryE
              (structContextToHOL ctx) = none from hihHead.symm]
        simp only [Option.map_none]
    | some v =>
        rw [hh] at hihHead
        simp only [Option.map_some] at hihHead
        cases ht : panMemLoadFldsHOL rest
            (address + bytesInWordHOL width * BitVec.ofNat width
              (sizeOfShapeWithContextHOL (structContextToHOL ctx) (shapeToHOL shape)))
            domain memory ctx with
        | none =>
            rw [ht] at hihTail
            simp only [Option.map_none] at hihTail
            rw [show memLoadHOLExact (shapeToHOL shape) address domainE memoryE
                  (structContextToHOL ctx) = some (holValueToHOL (width := width) v) from
                hihHead.symm]
            rw [show memLoadFldsHOLExact (rest.map paramToHOL)
                  (address + bytesInWordHOL width * BitVec.ofNat width
                    (sizeOfShapeWithContextHOL (structContextToHOL ctx) (shapeToHOL shape)))
                  domainE memoryE (structContextToHOL ctx) = none from hihTail.symm]
            rfl
        | some vs =>
            have ht' : panMemLoadFldsHOL rest
                (address + panBytesInWord width * BitVec.ofNat width (sizeOfShWithCtxt ctx shape))
                domain memory ctx = some vs := by
              rw [hsize]; exact ht
            exact (hfail v vs hh ht').elim
  case case12 =>
    intro address ctx hr hi hshapes
    simp only [panMemLoadsHOL, memLoadsHOLExact, List.map_nil, Option.map_some]
  case case13 =>
    intro address ctx shape rest value values htail hhead ihHead ihTail hr hi hshapes
    have hshape : ShapeByteRanged shape := hshapes shape (by simp)
    have hshapesRest : ∀ s ∈ rest, ShapeByteRanged s := fun s hs => hshapes s (by simp [hs])
    have hsize : panBytesInWord width * BitVec.ofNat width (sizeOfShWithCtxt ctx shape) =
        bytesInWordHOL width * BitVec.ofNat width
          (sizeOfShapeWithContextHOL (structContextToHOL ctx) (shapeToHOL shape)) := by
      rw [show panBytesInWord width = bytesInWordHOL width from rfl,
        sizeOfShWithCtxt_eq_sizeOfShapeWithContextHOL ctx hr shape hshape]
    have hihHead := ihHead hr hi hshape
    rw [hhead] at hihHead
    simp only [Option.map_some] at hihHead
    have htailE := htail
    rw [hsize] at htailE
    have hihTail := ihTail hr hi hshapesRest
    rw [hsize] at hihTail
    rw [htailE] at hihTail
    simp only [Option.map_some] at hihTail
    simp only [panMemLoadsHOL, memLoadsHOLExact, hhead, htailE, hsize, List.map_cons,
      Option.map_some, hihHead.symm, hihTail.symm]
  case case14 =>
    intro address ctx shape rest hfail ihHead ihTail hr hi hshapes
    have hshape : ShapeByteRanged shape := hshapes shape (by simp)
    have hshapesRest : ∀ s ∈ rest, ShapeByteRanged s := fun s hs => hshapes s (by simp [hs])
    have hsize : panBytesInWord width * BitVec.ofNat width (sizeOfShWithCtxt ctx shape) =
        bytesInWordHOL width * BitVec.ofNat width
          (sizeOfShapeWithContextHOL (structContextToHOL ctx) (shapeToHOL shape)) := by
      rw [show panBytesInWord width = bytesInWordHOL width from rfl,
        sizeOfShWithCtxt_eq_sizeOfShapeWithContextHOL ctx hr shape hshape]
    have hihHead := ihHead hr hi hshape
    have hihTail := ihTail hr hi hshapesRest
    rw [hsize] at hihTail
    simp only [panMemLoadsHOL, memLoadsHOLExact, hsize, List.map_cons]
    cases hh : panMemLoadHOL shape address domain memory ctx with
    | none =>
        rw [hh] at hihHead
        simp only [Option.map_none] at hihHead
        rw [show memLoadHOLExact (shapeToHOL shape) address domainE memoryE
              (structContextToHOL ctx) = none from hihHead.symm]
        simp only [Option.map_none]
    | some v =>
        rw [hh] at hihHead
        simp only [Option.map_some] at hihHead
        cases ht : panMemLoadsHOL rest
            (address + bytesInWordHOL width * BitVec.ofNat width
              (sizeOfShapeWithContextHOL (structContextToHOL ctx) (shapeToHOL shape)))
            domain memory ctx with
        | none =>
            rw [ht] at hihTail
            simp only [Option.map_none] at hihTail
            rw [show memLoadHOLExact (shapeToHOL shape) address domainE memoryE
                  (structContextToHOL ctx) = some (holValueToHOL (width := width) v) from
                hihHead.symm]
            rw [show memLoadsHOLExact (rest.map shapeToHOL)
                  (address + bytesInWordHOL width * BitVec.ofNat width
                    (sizeOfShapeWithContextHOL (structContextToHOL ctx) (shapeToHOL shape)))
                  domainE memoryE (structContextToHOL ctx) = none from hihTail.symm]
            rfl
        | some vs =>
            have ht' : panMemLoadsHOL rest
                (address + panBytesInWord width * BitVec.ofNat width (sizeOfShWithCtxt ctx shape))
                domain memory ctx = some vs := by
              rw [hsize]; exact ht
            exact (hfail v vs hh ht').elim

/-! ## Name-list and field-shape helpers for `.nStruct`/`.nField` -/

/-- `ofString` is injective on byte-ranged name lists. -/
theorem list_map_ofString_inj {a b : List String}
    (ha : ∀ x ∈ a, NameRanged x) (hb : ∀ x ∈ b, NameRanged x)
    (h : a.map ofString = b.map ofString) : a = b := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => rfl
      | cons y ys => simp at h
  | cons x xs ih =>
      cases b with
      | nil => simp at h
      | cons y ys =>
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨hxy, hxs⟩ := h
          have hxy' : x = y :=
            ofString_injective_of_ranged (ha x (by simp)) (hb y (by simp)) hxy
          subst hxy'
          rw [ih (fun z hz => ha z (by simp [hz])) (fun z hz => hb z (by simp [hz])) hxs]

/-- The production `==` name-list check is the exact `ofString`-image equality. -/
theorem list_beq_ofString_map_true {a b : List String}
    (ha : ∀ x ∈ a, NameRanged x) (hb : ∀ x ∈ b, NameRanged x) :
    (a == b) = true ↔ a.map ofString = b.map ofString := by
  rw [beq_iff_eq]
  exact ⟨fun h => by rw [h], fun h => list_map_ofString_inj ha hb h⟩

/-- The production field-shape check agrees with the exact `shapeEqHOL` check of
    the encoded shapes under the byte-range premises. -/
theorem panValueFieldsExactHOL_shape_check_eq (structs : StructContext)
    (expected : List (FieldName × Shape)) (values : List (FieldName × PanValue (RiscV.Word 64)))
    (hexpShapes : ∀ f ∈ expected, ShapeByteRanged f.2)
    (hvalRanged : ∀ v ∈ values, PanValueByteRanged v.2) :
    ((expected.map Prod.snd).zip (values.map Prod.snd)).all
        (fun p => panShapeMatches p.1 (panValueShape structs p.2)) =
      ((expected.map (fun f => shapeToHOL f.2)).zip
        (values.map (fun v => shapeOfHOLExact (panValueToHOL v.2)))).all
        (fun p => shapeEqHOL p.1 p.2) := by
  induction expected generalizing values with
  | nil => cases values <;> simp
  | cons f fs ih =>
      obtain ⟨fname, fshape⟩ := f
      cases values with
      | nil => simp
      | cons v vs =>
          obtain ⟨vname, vval⟩ := v
          have hfshape : ShapeByteRanged fshape := hexpShapes (fname, fshape) (by simp)
          have hvRanged : PanValueByteRanged vval := hvalRanged (vname, vval) (by simp)
          simp only [List.map_cons, List.zip_cons_cons, List.all_cons]
          rw [show panShapeMatches fshape (panValueShape structs vval) =
                shapeEqHOL (shapeToHOL fshape) (shapeOfHOLExact (panValueToHOL vval)) from by
                rw [shapeOfHOLExact_panValueToHOL]
                exact panShapeMatches_eq_shapeEqHOL fshape (panValueShape structs vval)
                  hfshape (panValueShape_byteRanged structs vval hvRanged)]
          rw [ih vs (fun f hf => hexpShapes f (by simp [hf]))
            (fun v hv => hvalRanged v (by simp [hv]))]

/-- `panValueFieldsExactHOL` rewritten as the production name check conjoined with
    the exact encoded-shape check. -/
theorem panValueFieldsExactHOL_eq_shapeEqCheck (structs : StructContext)
    (expected : List (FieldName × Shape)) (values : List (FieldName × PanValue (RiscV.Word 64)))
    (hexpShapes : ∀ f ∈ expected, ShapeByteRanged f.2)
    (hvalRanged : ∀ v ∈ values, PanValueByteRanged v.2) :
    panValueFieldsExactHOL structs expected values =
      ((expected.map Prod.fst == values.map Prod.fst) &&
        ((expected.map (fun f => shapeToHOL f.2)).zip
          (values.map (fun v => shapeOfHOLExact (panValueToHOL v.2)))).all
          (fun p => shapeEqHOL p.1 p.2)) := by
  rw [panValueFieldsExactHOL, panValueFieldsExactHOL_shape_check_eq structs expected values
    hexpShapes hvalRanged]

/-- Byte-ranged field names are ranged names. -/
theorem listFieldByteRanged_names {width : Nat} :
    ∀ {fields : List (String × Exp (BitVec width))}, ListFieldByteRanged fields →
      ∀ p ∈ fields, NameRanged p.1 := by
  intro fields
  induction fields with
  | nil => intro _ p hp; simp at hp
  | cons f fs ih =>
      intro h p hp
      simp only [ListFieldByteRanged] at h
      obtain ⟨hname, _, hrest⟩ := h
      rcases List.mem_cons.mp hp with hhead | htail
      · subst hhead
        exact hname
      · exact ih hrest p htail

/-- Evaluated named fields are byte-ranged when every field expression's result
    is byte-ranged. -/
theorem evalPanValueFields_byteRanged
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (baseAddress topAddress bytesInWord : RiscV.Word 64)
    (access : Option (PanValueMemoryAccess (RiscV.Word 64)))
    (fields : List (FieldName × Exp (RiscV.Word 64)))
    (values : List (FieldName × PanValue (RiscV.Word 64)))
    (hfields : ∀ p ∈ fields, ∀ v,
      evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord p.2
        (memoryAccess := access) = some v → PanValueByteRanged v)
    (h : evalPanValueExp.evalPanValueFields structs locals globals memory baseAddress
        topAddress bytesInWord fields (memoryAccess := access) = some values) :
    ∀ v ∈ values, PanValueByteRanged v.2 := by
  induction fields generalizing values with
  | nil => simp [evalPanValueExp.evalPanValueFields] at h; subst h; simp
  | cons f fs ih =>
      obtain ⟨fname, fexp⟩ := f
      cases hhead : evalPanValueExp structs locals globals memory baseAddress topAddress
          bytesInWord fexp (memoryAccess := access) with
      | none => simp [evalPanValueExp.evalPanValueFields, hhead] at h
      | some head =>
          cases htail : evalPanValueExp.evalPanValueFields structs locals globals memory
              baseAddress topAddress bytesInWord fs (memoryAccess := access) with
          | none => simp [evalPanValueExp.evalPanValueFields, hhead, htail] at h
          | some tail =>
              simp [evalPanValueExp.evalPanValueFields, hhead, htail] at h
              subst h
              intro v hv
              rcases List.mem_cons.mp hv with hvv | hvt
              · subst hvv
                exact hfields (fname, fexp) (by simp) head hhead
              · exact ih tail (fun p hp w hw => hfields p (by simp [hp]) w hw) htail v hvt

/-- Named fields preserve their names through the `memoryAccess`-parameterized
    evaluator. -/
theorem evalPanValueFields_names (structs : StructContext)
    (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (baseAddress topAddress bytesInWord : RiscV.Word 64)
    (access : Option (PanValueMemoryAccess (RiscV.Word 64)))
    (fields : List (FieldName × Exp (RiscV.Word 64)))
    (values : List (FieldName × PanValue (RiscV.Word 64)))
    (h : evalPanValueExp.evalPanValueFields structs locals globals memory baseAddress
        topAddress bytesInWord fields (memoryAccess := access) = some values) :
    values.map Prod.fst = fields.map Prod.fst := by
  induction fields generalizing values with
  | nil => simp [evalPanValueExp.evalPanValueFields] at h; subst h; simp
  | cons f fs ih =>
      obtain ⟨fname, fexp⟩ := f
      cases hhead : evalPanValueExp structs locals globals memory baseAddress topAddress
          bytesInWord fexp (memoryAccess := access) with
      | none => simp [evalPanValueExp.evalPanValueFields, hhead] at h
      | some head =>
          cases htail : evalPanValueExp.evalPanValueFields structs locals globals memory
              baseAddress topAddress bytesInWord fs (memoryAccess := access) with
          | none => simp [evalPanValueExp.evalPanValueFields, hhead, htail] at h
          | some tail =>
              simp [evalPanValueExp.evalPanValueFields, hhead, htail] at h
              subst h
              simp [ih tail htail]

/-- The production named-struct field-name check is the exact `ofString`-image
    name-list equality. -/
theorem panValueFieldNameCheck_iff (info : StructInfo)
    (fields : List (FieldName × Exp (RiscV.Word 64)))
    (values : List (FieldName × PanValue (RiscV.Word 64)))
    (hinfoNames : ∀ f ∈ info.fields, NameRanged f.1)
    (hfieldNames : ∀ p ∈ fields, NameRanged p.1)
    (hproj : values.map Prod.fst = fields.map Prod.fst) :
    (info.fields.map Prod.fst == values.map Prod.fst) = true ↔
      ((structInfoCacheToHOL info).fields.map Prod.fst =
        (fields.map (fun p => (ofString p.1, expToHOL p.2))).map Prod.fst) := by
  rw [hproj]
  have hfold1 : (structInfoCacheToHOL info).fields.map Prod.fst =
      (info.fields.map Prod.fst).map ofString := by
    simp only [structInfoCacheToHOL, List.map_map]
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp_apply]
  have hfold2 : ((fields.map (fun p => (ofString p.1, expToHOL p.2))).map Prod.fst) =
      (fields.map Prod.fst).map ofString := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp_apply]
  rw [hfold1, hfold2]
  exact list_beq_ofString_map_true (a := info.fields.map Prod.fst) (b := fields.map Prod.fst)
    (fun x hx => by rcases List.mem_map.mp hx with ⟨f, hf, rfl⟩; exact hinfoNames f hf)
    (fun x hx => by rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩; exact hfieldNames p hp)

/-- Final `if` normalization for the `.nStruct` clause, given the name-check
    equivalence. -/
theorem if_and_eq_if {β : Type} (nameBeq : Bool) (nameEq : Prop) [Decidable nameEq]
    (shapeCheck : Bool) (X : Option β) (h : nameBeq = true ↔ nameEq) :
    (if (nameBeq && shapeCheck) = true then X else none) =
      (if nameEq then (if shapeCheck = true then X else none) else none) := by
  by_cases hb : nameBeq = true
  · have hn : nameEq := h.mp hb
    by_cases hs : shapeCheck = true
    · simp_all
    · have hs' : shapeCheck = false := by cases hsc : shapeCheck <;> simp_all
      simp_all
  · have hn : ¬ nameEq := fun hn => hb (h.mpr hn)
    have hb' : nameBeq = false := by cases hbeq : nameBeq <;> simp_all
    simp_all

/-- Production/exact agreement for the `.nStruct` clause. -/
theorem evalPanValueExp_nStruct_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (access : Option (PanValueMemoryAccess (RiscV.Word 64)))
    (name : String) (fields : List (FieldName × Exp (RiscV.Word 64)))
    (hname : NameRanged name)
    (hfieldNames : ∀ p ∈ fields, NameRanged p.1)
    (hctxNames : ∀ p ∈ state.structs, NameRanged p.1)
    (hinfo : ∀ (info : StructInfo), lookupInfo name state.structs = some info →
        (∀ f ∈ info.fields, NameRanged f.1) ∧ (∀ f ∈ info.fields, ShapeByteRanged f.2))
    (hfields : ∀ p ∈ fields, Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord p.2 (memoryAccess := access))
      = exact.evalHOLFinite (expToHOL p.2))
    (hresRanged : ∀ p ∈ fields, ∀ v,
        evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord p.2 (memoryAccess := access) = some v →
        PanValueByteRanged v) :
    Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord (.nStruct name fields)
          (memoryAccess := access))
      = exact.evalHOLFinite
          (.nstruct (ofString name) (fields.map (fun p => (ofString p.1, expToHOL p.2)))) := by
  obtain ⟨_, _, hstructs, _, _, _, _, _, _, _, _, _, _⟩ := hrel
  simp only [evalPanValueExp, PanSemStateFiniteExact.evalHOLFinite_nstruct]
  rw [show exact.structs = panStructContextToHOL state.structs from hstructs.symm,
    lookupInfo_panStructContextToHOL' name state.structs hname hctxNames]
  cases hlook : lookupInfo name state.structs with
  | none => simp only [Option.map_none] <;> rfl
  | some info =>
      simp only [Option.map_some]
      have hvalEq := evalPanValueFields_eq_evalListFieldsHOLExact_of state.structs state.locals
        state.globals state.memory state.baseAddress state.topAddress panSemBitVec64BytesInWord
        access exact fields hfields
      cases hvals : evalPanValueExp.evalPanValueFields state.structs state.locals state.globals
          state.memory state.baseAddress state.topAddress panSemBitVec64BytesInWord fields
          (memoryAccess := access) with
      | none =>
          rw [hvals] at hvalEq
          simp only [Option.map_none] at hvalEq
          rw [← hvalEq]
          simp
      | some values =>
          rw [hvals] at hvalEq
          simp only [Option.map_some] at hvalEq
          rw [← hvalEq]
          simp
          have hproj := evalPanValueFields_names state.structs state.locals state.globals
            state.memory state.baseAddress state.topAddress panSemBitVec64BytesInWord access
            fields values hvals
          have hvalsRanged : ∀ v ∈ values, PanValueByteRanged v.2 :=
            evalPanValueFields_byteRanged state.structs state.locals state.globals state.memory
              state.baseAddress state.topAddress panSemBitVec64BytesInWord access fields values
              hresRanged hvals
          obtain ⟨hinfoNames, hinfoShapes⟩ := hinfo info hlook
          have hnameIff := panValueFieldNameCheck_iff info fields values hinfoNames hfieldNames hproj
          have hscEq : (((structInfoCacheToHOL info).fields.map Prod.snd).zip
                ((values.map (fun p => (ofString p.1, panValueToHOL p.2))).map
                  (fun p => shapeOfHOLExact p.2))).all (fun p => shapeEqHOL p.1 p.2) =
              ((info.fields.map (fun f => shapeToHOL f.2)).zip
                (values.map (fun v => shapeOfHOLExact (panValueToHOL v.2)))).all
                (fun p => shapeEqHOL p.1 p.2) := by
            simp [structInfoCacheToHOL, List.map_map, Function.comp_def]
          rw [panValueFieldsExactHOL_eq_shapeEqCheck state.structs info.fields values
            hinfoShapes hvalsRanged]
          rw [hscEq]
          apply if_and_eq_if
          simpa only [List.map_map, Function.comp_apply] using hnameIff

/-- Named-field lookup commutes with the value codec under ranged names. -/
theorem lookupPanValueField_map (name : String)
    (fields : List (FieldName × PanValue (RiscV.Word 64)))
    (hname : NameRanged name) (hfields : ∀ p ∈ fields, NameRanged p.1) :
    Option.map panValueToHOL (lookupPanValueField name fields) =
      lookupFieldHOL (ofString name)
        (fields.map (fun p => (ofString p.1, panValueToHOL p.2))) := by
  induction fields with
  | nil => simp [lookupPanValueField, lookupFieldHOL]
  | cons f fs ih =>
      obtain ⟨candidate, value⟩ := f
      have hcand : NameRanged candidate := hfields (candidate, value) (by simp)
      have htail : ∀ p ∈ fs, NameRanged p.1 := fun p hp => hfields p (by simp [hp])
      simp only [lookupPanValueField, lookupFieldHOL, List.map_cons]
      by_cases hc : candidate == name
      · have heq : candidate = name := beq_iff_eq.mp hc
        subst heq
        simp only [beq_self_eq_true, if_pos, Option.map_some]
      · have hne : candidate ≠ name := fun h => hc (beq_iff_eq.mpr h)
        have hofne : ofString candidate ≠ ofString name :=
          fun h => hne (ofString_injective_of_ranged hcand hname h)
        rw [if_neg hc, if_neg hofne]
        exact ih htail

/-- Production/exact agreement for the `.nField` clause. -/
theorem evalPanValueExp_nField_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (access : Option (PanValueMemoryAccess (RiscV.Word 64)))
    (name : String) (expression : Exp (RiscV.Word 64))
    (hname : NameRanged name)
    (hctxNames : ∀ p ∈ state.structs, NameRanged p.1)
    (hexpr : Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord expression
          (memoryAccess := access))
      = exact.evalHOLFinite (expToHOL expression))
    (hresRanged : ∀ v,
        evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord expression
          (memoryAccess := access) = some v → PanValueByteRanged v) :
    Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord (.nField name expression)
          (memoryAccess := access))
      = exact.evalHOLFinite (.nfield (ofString name) (expToHOL expression)) := by
  obtain ⟨_, _, hstructs, _, _, _, _, _, _, _, _, _, _⟩ := hrel
  simp only [evalPanValueExp, PanSemStateFiniteExact.evalHOLFinite_nfield]
  rw [show exact.structs = panStructContextToHOL state.structs from hstructs.symm]
  cases hv : evalPanValueExp state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress panSemBitVec64BytesInWord expression
      (memoryAccess := access) with
  | none =>
      rw [hv] at hexpr
      simp only [Option.map_none] at hexpr
      rw [← hexpr]
      simp
  | some pv =>
      rw [hv] at hexpr
      simp only [Option.map_some] at hexpr
      rw [← hexpr]
      cases pv with
      | word bits => simp
      | rStruct fs => simp
      | nStruct structName fields =>
          have hvr := hresRanged (.nStruct structName fields) hv
          simp only [PanValueByteRanged] at hvr
          obtain ⟨hstructName, hfieldsRanged⟩ := hvr
          have hfieldsNames : ∀ p ∈ fields, NameRanged p.1 :=
            fun p hp => (hfieldsRanged p hp).1
          have hlookEq : (structContextLookupHOL (ofString structName)
                (panStructContextToHOL state.structs)).isSome =
              (lookupInfo structName state.structs).isSome := by
            rw [lookupInfo_panStructContextToHOL' structName state.structs hstructName hctxNames,
              Option.isSome_map]
          simp [hlookEq]
          by_cases hc : (lookupInfo structName state.structs).isSome = true
          · simp only [hc, if_true]
            rw [lookupPanValueField_map name fields hname hfieldsNames]
          · have hc' : (lookupInfo structName state.structs).isSome = false := by
              cases h : (lookupInfo structName state.structs).isSome <;> simp_all
            simp [hc']

/-- Production/exact agreement for the `.load` clause. -/
theorem evalPanValueExp_load_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (hranged : PanSemStateRelExecRanged state)
    (shape : Shape) (address : Exp (RiscV.Word 64))
    (hshape : ShapeByteRanged shape)
    (haddress : Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord address
          (memoryAccess := some (panSemBitVec64MemoryAccess state)))
      = exact.evalHOLFinite (expToHOL address)) :
    Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord (.load shape address)
          (memoryAccess := some (panSemBitVec64MemoryAccess state)))
      = exact.evalHOLFinite (.load (shapeToHOL shape) (expToHOL address)) := by
  obtain ⟨_, _, hstructs, _, _, hm, hmd, _, _, _, _, _, _⟩ := hrel
  have hr : ∀ p ∈ state.structs.toHOL, NameRanged p.1 :=
    fun p hp => (hranged.2.2 p hp).1
  have hi : ∀ p ∈ state.structs.toHOL, StructInfoByteRanged p.2 :=
    fun p hp => (hranged.2.2 p hp).2
  simp only [evalPanValueExp, PanSemStateFiniteExact.evalHOLFinite_load]
  rw [show exact.structs = panStructContextToHOL state.structs from hstructs.symm]
  have hwfEq : isWfShape state.structs shape =
      isWfShapeExactHOL (panStructContextToHOL state.structs) (shapeToHOL shape) := by
    rw [← isWfShapeHOL_toHOL state.structs shape]
    exact isWfShapeHOL_eq_isWfShapeExactHOL state.structs.toHOL hr shape hshape
  cases haddr : evalPanValueExp state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress panSemBitVec64BytesInWord address
      (memoryAccess := some (panSemBitVec64MemoryAccess state)) with
  | none =>
      rw [haddr] at haddress
      simp only [Option.map_none] at haddress
      rw [← haddress]
      simp
  | some pv =>
      rw [haddr] at haddress
      simp only [Option.map_some] at haddress
      rw [← haddress]
      cases pv with
      | word bits =>
          simp
          by_cases hwf : isWfShape state.structs shape = true
          · have hwfE : isWfShapeExactHOL (panStructContextToHOL state.structs)
                (shapeToHOL shape) = true := by rw [← hwfEq]; exact hwf
            simp only [hwfE, if_true]
            rw [panValueFlatLoad_eq_panMemLoadHOL state state.memory state.structs shape bits hwf]
            rw [Option.map_map]
            have hcomp : ((panValueToHOL (width := 64)) ∘ (HolValue.toPanValue (width := 64))) =
                holValueToHOL := by
              funext v
              exact panValueToHOL_toPanValue v
            rw [hcomp]
            have hdom : ∀ a, panValueFlatMachineDomain state state.memory a ↔
                exact.toExact.memaddrs a :=
              fun a => panValueFlatMachineDomain_iff state exact hm hmd a
            have hmem : ∀ a, exact.toExact.memaddrs a →
                panValueWordHOL state.memory a = exact.toExact.memory a :=
              fun a ha => panValueWordHOL_eq_of_memRel state exact hm hmd a ha
            exact panMemLoadHOL_map_holValueToHOL
              (domain := panValueFlatMachineDomain state state.memory)
              (memory := panValueWordHOL state.memory)
              (domainE := exact.toExact.memaddrs) (memoryE := exact.toExact.memory)
              hdom hmem shape bits state.structs.toHOL hr hi hshape
          · have hwfE : ¬ isWfShapeExactHOL (panStructContextToHOL state.structs)
                (shapeToHOL shape) = true := by rw [← hwfEq]; exact hwf
            unfold panValueFlatLoad
            rw [if_neg hwf, if_neg hwfE]
            rfl
      | rStruct fs => simp
      | nStruct nm fs => simp

/-! ## Rangedness of production expression evaluation

`PanValueByteRanged` restricts only the identifier payloads of a production
value; word payloads are always representable.  The companion theorem
`evalPanValueExp_byteRanged` shows that every value returned by the production
expression evaluator under `PanSemStateRelExecRanged` and `ExpByteRanged` inputs
is `PanValueByteRanged`.  The `.load` obligation is discharged by an induction
over the fuel-indexed flat-load family.  Everything here is untagged
Flapjack-specific bridge infrastructure. -/

/-- Projecting a byte-ranged production context through `StructContext.toHOL`
    preserves the range invariant used by the flat-load induction. -/
theorem ctxBR_of_structContextByteRanged (c : StructContext)
    (h : StructContextByteRanged c.toHOL) : CtxBR c := by
  intro p hp
  have hmem : (p.1, { fields := p.2.fields, size := p.2.size }) ∈ c.toHOL := by
    simp only [StructContext.toHOL, List.mem_map]
    exact ⟨p, hp, rfl⟩
  have hrange := h _ hmem
  exact ⟨hrange.1, hrange.2⟩

/-- Every entry name of a production context whose projection is byte-ranged is
    itself byte-ranged. -/
theorem structContextByteRanged_names (c : StructContext)
    (h : StructContextByteRanged c.toHOL) : ∀ p ∈ c, NameRanged p.1 := by
  intro p hp
  have hmem : (p.1, { fields := p.2.fields, size := p.2.size }) ∈ c.toHOL := by
    simp only [StructContext.toHOL, List.mem_map]
    exact ⟨p, hp, rfl⟩
  exact (h _ hmem).1

/-- A looked-up production `struct_info` has ranged field names and shapes when
    the projected context is byte-ranged. -/
theorem lookupInfo_byteRanged {name : String} {context : StructContext}
    {info : StructInfo} (h : lookupInfo name context = some info)
    (hrange : StructContextByteRanged context.toHOL) :
    (∀ f ∈ info.fields, NameRanged f.1) ∧ (∀ f ∈ info.fields, ShapeByteRanged f.2) := by
  induction context with
  | nil => simp [lookupInfo] at h
  | cons entry rest ih =>
      obtain ⟨candidate, info'⟩ := entry
      have hhead : (candidate, { fields := info'.fields, size := info'.size }) ∈
          StructContext.toHOL ((candidate, info') :: rest) := by
        simp [StructContext.toHOL]
      have hheadRange := hrange _ hhead
      simp only [lookupInfo] at h
      by_cases hc : candidate == name
      · rw [if_pos hc] at h
        have hinj : info' = info := by simpa using h
        subst hinj
        exact ⟨fun f hf => (hheadRange.2 f hf).1, fun f hf => (hheadRange.2 f hf).2⟩
      · rw [if_neg hc] at h
        refine ih h ?_
        intro p hp
        apply hrange p
        simp only [StructContext.toHOL, List.map_cons, List.mem_cons]
        exact Or.inr (by simpa only [StructContext.toHOL] using hp)

/-- The produced field names of a flat field load are byte-ranged when the input
    field names are. -/
theorem names_ranged_of_map_fst_eq {α β : Type}
    {values : List (FieldName × PanValue α)} {fields : List (FieldName × β)}
    (hnames : ∀ p ∈ fields, NameRanged p.1)
    (heq : values.map Prod.fst = fields.map Prod.fst) :
    ∀ p ∈ values, NameRanged p.1 := by
  intro p hp
  have hmem : p.1 ∈ values.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
  rw [heq] at hmem
  obtain ⟨q, hq, hqeq⟩ := List.mem_map.mp hmem
  rw [← hqeq]
  exact hnames q hq

/-- A byte-ranged `rStruct` field selected by index is byte-ranged. -/
theorem getElem?_byteRanged {width : Nat} {l : List (PanValue (BitVec width))} {index : Nat}
    {value : PanValue (BitVec width)} (h : ∀ x ∈ l, PanValueByteRanged x)
    (hget : l[index]? = some value) : PanValueByteRanged value := by
  induction l generalizing index with
  | nil => simp at hget
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst hget
          exact h head (by simp)
      | succ index =>
          simp only [List.getElem?_cons_succ] at hget
          exact ih (fun x hx => h x (by simp [hx])) hget

/-- A byte-ranged named field selected by name is byte-ranged. -/
theorem lookupPanValueField_byteRanged {width : Nat}
    {fields : List (FieldName × PanValue (BitVec width))} {name : FieldName}
    {value : PanValue (BitVec width)}
    (hranged : ∀ p ∈ fields, PanValueByteRanged p.2)
    (h : lookupPanValueField name fields = some value) : PanValueByteRanged value := by
  induction fields with
  | nil => simp [lookupPanValueField] at h
  | cons pair rest ih =>
      obtain ⟨candidate, fieldValue⟩ := pair
      simp only [lookupPanValueField] at h
      by_cases hc : candidate == name
      · rw [if_pos hc] at h
        have heq : fieldValue = value := by simpa using h
        subst heq
        exact hranged (candidate, fieldValue) (by simp)
      · rw [if_neg hc] at h
        exact ih (fun p hp => hranged p (by simp [hp])) h

/-- Flat-load fuel rangedness: every value returned by the fuel-indexed flat load
    (and its list/field helpers) is `PanValueByteRanged`, provided the context
    and the loaded shapes are byte-ranged.  The recursive named-structure clause
    follows the remaining context, so the range invariant is threaded through the
    mutual induction. -/
theorem panValueFlatLoadFuel_byteRanged {width : Nat}
    (structs : StructContext) (readWord : BitVec width → Option (BitVec width))
    (bytesInWord : BitVec width)
    (hctx : CtxBR structs) :
    ∀ (fuel : Nat) (shape : Shape) (address : BitVec width) (value : PanValue (BitVec width)),
      ShapeByteRanged shape →
      panValueFlatLoadFuel structs readWord bytesInWord fuel shape address = some value →
        PanValueByteRanged value := by
  have hmain := panValueFlatLoadFuel.induct (α := BitVec width) bytesInWord
    (motive1 := fun structs fuel shape address =>
      CtxBR structs → ShapeByteRanged shape →
      ∀ value, panValueFlatLoadFuel structs readWord bytesInWord fuel shape address = some value →
        PanValueByteRanged value)
    (motive2 := fun structs fuel fields address =>
      CtxBR structs → (∀ f ∈ fields, NameRanged f.1) →
      (∀ f ∈ fields, ShapeByteRanged f.2) →
      ∀ values, panValueFlatLoadFieldsFuel structs readWord bytesInWord fuel fields address = some values →
        (∀ p ∈ values, NameRanged p.1) ∧ (∀ p ∈ values, PanValueByteRanged p.2))
    (motive3 := fun structs fuel shapes address =>
      CtxBR structs → (∀ s ∈ shapes, ShapeByteRanged s) →
      ∀ values, panValueFlatLoadListFuel structs readWord bytesInWord fuel shapes address = some values →
        ∀ v ∈ values, PanValueByteRanged v)
    (by
      intro structs x x_1 hctx hshape value h
      simp [panValueFlatLoadFuel] at h)
    (by
      intro structs fuel address hctx hshape value h
      obtain ⟨word, -, rfl⟩ := by simpa [panValueFlatLoadFuel] using h
      simp only [PanValueByteRanged])
    (by
      intro structs fuel shapes address ih hctx hshape value h
      obtain ⟨values, hvalues, rfl⟩ := by simpa [panValueFlatLoadFuel] using h
      have hshapes : ∀ s ∈ shapes, ShapeByteRanged s := by
        simpa only [ShapeByteRanged] using hshape
      simpa only [PanValueByteRanged] using ih hctx hshapes values hvalues)
    (by
      intro structs fuel name address ih hctx hshape value h
      cases hlookup : lookupInfoWithRest name structs with
      | none => simp [panValueFlatLoadFuel, hlookup] at h
      | some pair =>
          obtain ⟨info, rest⟩ := pair
          cases hfields : panValueFlatLoadFieldsFuel rest readWord bytesInWord fuel
              info.fields address with
          | none => simp [panValueFlatLoadFuel, hlookup, hfields] at h
          | some values =>
              simp [panValueFlatLoadFuel, hlookup, hfields] at h
              have hname : NameRanged name := by simpa only [ShapeByteRanged] using hshape
              obtain ⟨k, hk⟩ := lookupInfoWithRest_exists_mem hlookup
              have hinfoFields : ∀ f ∈ info.fields, NameRanged f.1 ∧ ShapeByteRanged f.2 :=
                hctx (k, info) hk |>.2
              have hvals := ih info rest (lookupInfoWithRest_ctxBR hlookup hctx)
                (fun f hf => (hinfoFields f hf).1)
                (fun f hf => (hinfoFields f hf).2) values hfields
              subst h
              simp only [PanValueByteRanged]
              exact ⟨hname, fun p hp => ⟨hvals.1 p hp, hvals.2 p hp⟩⟩)
    (by
      intro structs x x_1 hctx hnames hshapes values h
      simp [panValueFlatLoadFieldsFuel] at h
      subst h
      exact ⟨by simp, by simp⟩)
    (by
      intro structs head tail x hctx hnames hshapes values h
      simp [panValueFlatLoadFieldsFuel] at h)
    (by
      intro structs fuel field shape fields address ihHead ihTail hctx hnames hshapes values h
      have hname : NameRanged field := hnames (field, shape) (by simp)
      have hshape : ShapeByteRanged shape := hshapes (field, shape) (by simp)
      have htailNames : ∀ f ∈ fields, NameRanged f.1 :=
        fun f hf => hnames f (by simp [hf])
      have htailShapes : ∀ f ∈ fields, ShapeByteRanged f.2 :=
        fun f hf => hshapes f (by simp [hf])
      cases hvalue : panValueFlatLoadFuel structs readWord bytesInWord fuel shape address with
      | none => simp [panValueFlatLoadFieldsFuel, hvalue] at h
      | some value =>
          cases hvalues : panValueFlatLoadFieldsFuel structs readWord bytesInWord fuel fields
              (panValueFlatOffset bytesInWord address (shapeSizeWithContext structs shape)) with
          | none => simp [panValueFlatLoadFieldsFuel, hvalue, hvalues] at h
          | some rest =>
              simp [panValueFlatLoadFieldsFuel, hvalue, hvalues] at h
              subst h
              refine ⟨?_, ?_⟩
              · intro p hp
                rcases List.mem_cons.mp hp with rfl | hp
                · exact hname
                · exact (ihTail hctx htailNames htailShapes rest hvalues).1 p hp
              · intro p hp
                rcases List.mem_cons.mp hp with rfl | hp
                · exact ihHead hctx hshape value hvalue
                · exact (ihTail hctx htailNames htailShapes rest hvalues).2 p hp)
    (by
      intro structs x x_1 hctx hshapes values h
      simp [panValueFlatLoadListFuel] at h
      subst h
      intro v hv
      simp at hv)
    (by
      intro structs head tail x hctx hshapes values h
      simp [panValueFlatLoadListFuel] at h)
    (by
      intro structs fuel shape shapes address ihHead ihTail hctx hshapes values h
      have hshape : ShapeByteRanged shape := hshapes shape (by simp)
      have htailShapes : ∀ s ∈ shapes, ShapeByteRanged s :=
        fun s hs => hshapes s (by simp [hs])
      cases hvalue : panValueFlatLoadFuel structs readWord bytesInWord fuel shape address with
      | none => simp [panValueFlatLoadListFuel, hvalue] at h
      | some loaded =>
          cases hvalues : panValueFlatLoadListFuel structs readWord bytesInWord fuel shapes
              (panValueFlatOffset bytesInWord address (shapeSizeWithContext structs shape)) with
          | none => simp [panValueFlatLoadListFuel, hvalue, hvalues] at h
          | some rest =>
              simp [panValueFlatLoadListFuel, hvalue, hvalues] at h
              subst h
              intro v hv
              rcases List.mem_cons.mp hv with rfl | hv
              · exact ihHead hctx hshape v hvalue
              · exact ihTail hctx htailShapes rest hvalues v hv)
  intro fuel shape address value hshape h
  exact hmain structs fuel shape address hctx hshape value h

/-- Every value returned by a flat load of a byte-ranged shape from a byte-ranged
    context is `PanValueByteRanged`. -/
theorem panValueFlatLoad_byteRanged (structs : StructContext)
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (bytesInWord address : RiscV.Word 64) (shape : Shape)
    (memoryAccess : Option (PanValueMemoryAccess (RiscV.Word 64)))
    (value : PanValue (RiscV.Word 64))
    (hctx : CtxBR structs) (hshape : ShapeByteRanged shape)
    (h : panValueFlatLoad structs memory bytesInWord address shape memoryAccess = some value) :
    PanValueByteRanged value := by
  rw [panValueFlatLoad] at h
  by_cases hwf : isWfShape structs shape = true
  · rw [if_pos hwf] at h
    exact panValueFlatLoadFuel_byteRanged structs
      (panValueFlatReadWord memory bytesInWord memoryAccess) bytesInWord hctx
      _ shape address value hshape h
  · rw [if_neg hwf] at h
    simp at h

/-! ## Rangedness of production expression evaluation -/

/-- Every value returned by the production expression evaluator under a
    byte-ranged state and a byte-ranged expression is `PanValueByteRanged`.  The
    `.load` obligation is discharged by `panValueFlatLoad_byteRanged`, and the
    `.nStruct`/`.nField` obligations use the field-name range predicates. -/
theorem evalPanValueExp_byteRanged {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hranged : PanSemStateRelExecRanged state)
    (access : Option (PanValueMemoryAccess (RiscV.Word 64)))
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e)
    (v : PanValue (RiscV.Word 64))
    (h : evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord e
          (memoryAccess := access) = some v) :
    PanValueByteRanged v := by
  have hmain := evalPanValueExp.induct
    (motive1 := fun expressions memoryAccess =>
      ListExpByteRanged expressions →
      ∀ values, evalPanValueExp.evalPanValueExps state.structs state.locals state.globals
          state.memory state.baseAddress state.topAddress panSemBitVec64BytesInWord
          expressions (memoryAccess := memoryAccess) = some values →
        ∀ v ∈ values, PanValueByteRanged v)
    (motive2 := fun expression memoryAccess =>
      ExpByteRanged expression →
      ∀ v, evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord expression
          (memoryAccess := memoryAccess) = some v → PanValueByteRanged v)
    (motive3 := fun fields memoryAccess =>
      ListFieldByteRanged fields →
      ∀ values, evalPanValueExp.evalPanValueFields state.structs state.locals state.globals
          state.memory state.baseAddress state.topAddress panSemBitVec64BytesInWord
          fields (memoryAccess := memoryAccess) = some values →
        ∀ p ∈ values, PanValueByteRanged p.2)
    (by
      intro memoryAccess he values h
      simp only [evalPanValueExp.evalPanValueExps, Option.some.injEq] at h
      subst h
      intro v hv
      simp at hv)
    (by
      intro expression expressions memoryAccess ihHead ihTail he values h
      simp only [ListExpByteRanged] at he
      obtain ⟨heHead, heTail⟩ := he
      simp only [evalPanValueExp.evalPanValueExps] at h
      cases hvalue : evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord expression
          (memoryAccess := memoryAccess) with
      | none => simp [hvalue] at h
      | some head =>
          cases hvalues : evalPanValueExp.evalPanValueExps state.structs state.locals
              state.globals state.memory state.baseAddress state.topAddress
              panSemBitVec64BytesInWord expressions (memoryAccess := memoryAccess) with
          | none => simp [hvalue, hvalues] at h
          | some tail =>
              simp [hvalue, hvalues, Option.some.injEq] at h
              subst h
              intro v hv
              rcases List.mem_cons.mp hv with rfl | hv
              · exact ihHead heHead v hvalue
              · exact ihTail heTail tail hvalues v hv)
    (by
      intro memoryAccess value he v h
      simp only [evalPanValueExp, Option.some.injEq] at h
      subst h
      simp only [PanValueByteRanged])
    (by
      intro memoryAccess name he v h
      simp only [evalPanValueExp] at h
      exact hranged.1 name v h)
    (by
      intro memoryAccess name he v h
      simp only [evalPanValueExp] at h
      exact hranged.2.1 name v h)
    (by
      intro fields memoryAccess ih he v h
      simp only [evalPanValueExp] at h
      cases hfields : evalPanValueExp.evalPanValueExps state.structs state.locals
          state.globals state.memory state.baseAddress state.topAddress
          panSemBitVec64BytesInWord fields (memoryAccess := memoryAccess) with
      | none => simp [hfields] at h
      | some values =>
          simp [hfields, Option.some.injEq] at h
          subst h
          simpa only [PanValueByteRanged] using ih he values hfields)
    (by
      intro index expression memoryAccess ih he v h
      cases hexpr : evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord expression
          (memoryAccess := memoryAccess) with
      | none => simp [evalPanValueExp, hexpr] at h
      | some inner =>
          cases inner with
          | word w => simp [evalPanValueExp, hexpr] at h
          | rStruct fs =>
              cases hget : fs[index]? with
              | none => simp [evalPanValueExp, hexpr, hget] at h
              | some w =>
                  simp [evalPanValueExp, hexpr, hget, Option.some.injEq] at h
                  subst h
                  have hfs : ∀ x ∈ fs, PanValueByteRanged x := by
                    simpa only [PanValueByteRanged] using ih he (.rStruct fs) hexpr
                  exact getElem?_byteRanged hfs hget
          | nStruct nm fs => simp [evalPanValueExp, hexpr] at h)
    (by
      intro name fields memoryAccess ih he v h
      simp only [ExpByteRanged] at he
      obtain ⟨hname, hfieldsRanged⟩ := he
      cases hinfo : lookupInfo name state.structs with
      | none => simp [evalPanValueExp, hinfo] at h
      | some info =>
          cases hvals : evalPanValueExp.evalPanValueFields state.structs state.locals
              state.globals state.memory state.baseAddress state.topAddress
              panSemBitVec64BytesInWord fields (memoryAccess := memoryAccess) with
          | none => simp [evalPanValueExp, hinfo, hvals] at h
          | some values =>
              by_cases hcheck : panValueFieldsExactHOL state.structs info.fields values = true
              · simp [evalPanValueExp, hinfo, hvals, hcheck, Option.some.injEq] at h
                subst h
                simp only [PanValueByteRanged]
                refine ⟨hname, ?_⟩
                have hnames := evalPanValueFields_names state.structs state.locals
                  state.globals state.memory state.baseAddress state.topAddress
                  panSemBitVec64BytesInWord memoryAccess fields values hvals
                have hfieldNames : ∀ p ∈ fields, NameRanged p.1 :=
                  listFieldByteRanged_names hfieldsRanged
                have hvalsNames := names_ranged_of_map_fst_eq hfieldNames hnames
                intro p hp
                exact ⟨hvalsNames p hp, ih hfieldsRanged values hvals p hp⟩
              · simp [evalPanValueExp, hinfo, hvals, hcheck] at h)
    (by
      intro name expression memoryAccess ih he v h
      simp only [ExpByteRanged] at he
      obtain ⟨_, hexpRanged⟩ := he
      cases hexpr : evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord expression
          (memoryAccess := memoryAccess) with
      | none => simp [evalPanValueExp, hexpr] at h
      | some inner =>
          cases inner with
          | word w => simp [evalPanValueExp, hexpr] at h
          | rStruct fs => simp [evalPanValueExp, hexpr] at h
          | nStruct structName fs =>
              by_cases hsome : (lookupInfo structName state.structs).isSome = true
              · cases hlook : lookupPanValueField name fs with
                | none => simp [evalPanValueExp, hexpr, hsome, hlook] at h
                | some w =>
                    simp [evalPanValueExp, hexpr, hsome, hlook, Option.some.injEq] at h
                    subst h
                    have hinner : PanValueByteRanged (.nStruct structName fs) :=
                      ih hexpRanged (.nStruct structName fs) hexpr
                    have hfs : ∀ p : FieldName × PanValue (BitVec 64),
                        p ∈ fs → PanValueByteRanged p.2 := by
                      have h' := hinner
                      simp only [PanValueByteRanged] at h'
                      exact fun p hp => (h'.2 p hp).2
                    exact lookupPanValueField_byteRanged hfs hlook
              · simp [evalPanValueExp, hexpr, hsome] at h)
    (by
      intro shape address memoryAccess ih he v h
      simp only [ExpByteRanged] at he
      obtain ⟨hshape, _⟩ := he
      cases haddr : evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord address
          (memoryAccess := memoryAccess) with
      | none => simp [evalPanValueExp, haddr] at h
      | some addrValue =>
          cases addrValue with
          | word addr =>
              simp only [evalPanValueExp, haddr] at h
              exact panValueFlatLoad_byteRanged state.structs state.memory
                panSemBitVec64BytesInWord addr shape memoryAccess v
                (ctxBR_of_structContextByteRanged state.structs hranged.2.2) hshape h
          | rStruct fs => simp [evalPanValueExp, haddr] at h
          | nStruct nm fs => simp [evalPanValueExp, haddr] at h)
    (by
      intro address memoryAccess ih he v h
      cases haddr : evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord address
          (memoryAccess := memoryAccess) with
      | none => simp [evalPanValueExp, haddr] at h
      | some addrValue =>
          cases addrValue with
          | word addr =>
              cases memoryAccess with
              | none =>
                  cases hread : state.memory addr with
                  | none => simp [evalPanValueExp, haddr, hread] at h
                  | some mv =>
                      cases mv with
                      | word w =>
                          simp [evalPanValueExp, haddr, hread, Option.some.injEq] at h
                          subst h
                          simp only [PanValueByteRanged]
                      | rStruct fs => simp [evalPanValueExp, haddr, hread] at h
                      | nStruct nm fs => simp [evalPanValueExp, haddr, hread] at h
              | some access =>
                  cases hread : access.read32 access.domain state.memory
                      panSemBitVec64BytesInWord addr with
                  | none => simp [evalPanValueExp, haddr, hread] at h
                  | some w =>
                      simp [evalPanValueExp, haddr, hread, Option.some.injEq] at h
                      subst h
                      simp only [PanValueByteRanged]
          | rStruct fs => simp [evalPanValueExp, haddr] at h
          | nStruct nm fs => simp [evalPanValueExp, haddr] at h)
    (by
      intro address memoryAccess ih he v h
      cases haddr : evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord address
          (memoryAccess := memoryAccess) with
      | none => simp [evalPanValueExp, haddr] at h
      | some addrValue =>
          cases addrValue with
          | word addr =>
              cases memoryAccess with
              | none =>
                  cases hread : state.memory addr with
                  | none => simp [evalPanValueExp, haddr, hread] at h
                  | some mv =>
                      cases mv with
                      | word w =>
                          simp [evalPanValueExp, haddr, hread, Option.some.injEq] at h
                          subst h
                          simp only [PanValueByteRanged]
                      | rStruct fs => simp [evalPanValueExp, haddr, hread] at h
                      | nStruct nm fs => simp [evalPanValueExp, haddr, hread] at h
              | some access =>
                  cases hread : access.readByte access.domain state.memory
                      panSemBitVec64BytesInWord addr with
                  | none => simp [evalPanValueExp, haddr, hread] at h
                  | some w =>
                      simp [evalPanValueExp, haddr, hread, Option.some.injEq] at h
                      subst h
                      simp only [PanValueByteRanged]
          | rStruct fs => simp [evalPanValueExp, haddr] at h
          | nStruct nm fs => simp [evalPanValueExp, haddr] at h)
    (by
      intro operator arguments memoryAccess ih he v h
      cases hargs : evalPanValueExp.evalPanValueExps state.structs state.locals
          state.globals state.memory state.baseAddress state.topAddress
          panSemBitVec64BytesInWord arguments (memoryAccess := memoryAccess) with
      | none => simp [evalPanValueExp, hargs] at h
      | some values =>
          cases memoryAccess with
          | none =>
              cases hmap : values.mapM panValueWordProjection with
              | none => simp [evalPanValueExp, hargs, hmap] at h
              | some words =>
                  cases words with
                  | nil => simp [evalPanValueExp, hargs, hmap] at h
                  | cons a rest =>
                      cases rest with
                      | nil => simp [evalPanValueExp, hargs, hmap] at h
                      | cons b rest2 =>
                          cases rest2 with
                          | nil =>
                              simp [evalPanValueExp, hargs, hmap, Option.some.injEq] at h
                              subst h
                              simp only [PanValueByteRanged]
                          | cons c rest3 => simp [evalPanValueExp, hargs, hmap] at h
          | some access =>
              cases hmap : values.mapM panValueWordProjection with
              | none => simp [evalPanValueExp, hargs, hmap] at h
              | some words =>
                  cases hword : access.wordOp operator words with
                  | none => simp [evalPanValueExp, hargs, hmap, hword] at h
                  | some w =>
                      simp [evalPanValueExp, hargs, hmap, hword, Option.some.injEq] at h
                      subst h
                      simp only [PanValueByteRanged])
    (by
      intro operator arguments memoryAccess ih he v h
      cases hargs : evalPanValueExp.evalPanValueExps state.structs state.locals
          state.globals state.memory state.baseAddress state.topAddress
          panSemBitVec64BytesInWord arguments (memoryAccess := memoryAccess) with
      | none => simp [evalPanValueExp, hargs] at h
      | some values =>
          cases values with
          | nil => simp [evalPanValueExp, hargs] at h
          | cons first rest =>
              cases rest with
              | nil => simp [evalPanValueExp, hargs] at h
              | cons second rest2 =>
                  cases rest2 with
                  | nil =>
                      cases first with
                      | word left =>
                          cases second with
                          | word right =>
                              cases hpan : evalPanOp operator [left, right] with
                              | none => simp [evalPanValueExp, hargs, hpan] at h
                              | some w =>
                                  simp [evalPanValueExp, hargs, hpan, Option.some.injEq] at h
                                  subst h
                                  simp only [PanValueByteRanged]
                          | rStruct fs => simp [evalPanValueExp, hargs] at h
                          | nStruct nm fs => simp [evalPanValueExp, hargs] at h
                      | rStruct fs => simp [evalPanValueExp, hargs] at h
                      | nStruct nm fs => simp [evalPanValueExp, hargs] at h
                  | cons third rest3 => simp [evalPanValueExp, hargs] at h)
    (by
      intro operator left right memoryAccess ihLeft ihRight he v h
      simp only [ExpByteRanged] at he
      obtain ⟨heLeft, heRight⟩ := he
      cases memoryAccess with
      | none =>
          cases hleft : evalPanValueExp state.structs state.locals state.globals state.memory
              state.baseAddress state.topAddress panSemBitVec64BytesInWord left
              (memoryAccess := none) with
          | none => simp [evalPanValueExp, hleft] at h
          | some leftValue =>
              cases hright : evalPanValueExp state.structs state.locals state.globals
                  state.memory state.baseAddress state.topAddress
                  panSemBitVec64BytesInWord right (memoryAccess := none) with
              | none => simp [evalPanValueExp, hleft, hright] at h
              | some rightValue =>
                  cases leftValue with
                  | word l =>
                      cases rightValue with
                      | word r =>
                          simp [evalPanValueExp, hleft, hright, Option.some.injEq] at h
                          subst h
                          simp only [PanValueByteRanged]
                      | rStruct fs => simp [evalPanValueExp, hleft, hright] at h
                      | nStruct nm fs => simp [evalPanValueExp, hleft, hright] at h
                  | rStruct fs => simp [evalPanValueExp, hleft, hright] at h
                  | nStruct nm fs => simp [evalPanValueExp, hleft, hright] at h
      | some access =>
          cases hleft : evalPanValueExp state.structs state.locals state.globals state.memory
              state.baseAddress state.topAddress panSemBitVec64BytesInWord left
              (memoryAccess := some access) with
          | none => simp [evalPanValueExp, hleft] at h
          | some leftValue =>
              cases hright : evalPanValueExp state.structs state.locals state.globals
                  state.memory state.baseAddress state.topAddress
                  panSemBitVec64BytesInWord right (memoryAccess := some access) with
              | none => simp [evalPanValueExp, hleft, hright] at h
              | some rightValue =>
                  cases leftValue with
                  | word l =>
                      cases rightValue with
                      | word r =>
                          simp [evalPanValueExp, hleft, hright, Option.some.injEq] at h
                          subst h
                          simp only [PanValueByteRanged]
                      | rStruct fs => simp [evalPanValueExp, hleft, hright] at h
                      | nStruct nm fs => simp [evalPanValueExp, hleft, hright] at h
                  | rStruct fs => simp [evalPanValueExp, hleft, hright] at h
                  | nStruct nm fs => simp [evalPanValueExp, hleft, hright] at h)
    (by
      intro operator left right memoryAccess ihLeft ihRight he v h
      simp only [ExpByteRanged] at he
      obtain ⟨heLeft, heRight⟩ := he
      cases memoryAccess with
      | none =>
          cases hleft : evalPanValueExp state.structs state.locals state.globals state.memory
              state.baseAddress state.topAddress panSemBitVec64BytesInWord left
              (memoryAccess := none) with
          | none => simp [evalPanValueExp, hleft] at h
          | some leftValue =>
              cases hright : evalPanValueExp state.structs state.locals state.globals
                  state.memory state.baseAddress state.topAddress
                  panSemBitVec64BytesInWord right (memoryAccess := none) with
              | none => simp [evalPanValueExp, hleft, hright] at h
              | some rightValue =>
                  cases leftValue with
                  | word l =>
                      cases rightValue with
                      | word r =>
                          cases hshift : evalPanShift operator l r with
                          | none => simp [evalPanValueExp, hleft, hright, hshift] at h
                          | some w =>
                              simp [evalPanValueExp, hleft, hright, hshift,
                                Option.some.injEq] at h
                              subst h
                              simp only [PanValueByteRanged]
                      | rStruct fs => simp [evalPanValueExp, hleft, hright] at h
                      | nStruct nm fs => simp [evalPanValueExp, hleft, hright] at h
                  | rStruct fs => simp [evalPanValueExp, hleft, hright] at h
                  | nStruct nm fs => simp [evalPanValueExp, hleft, hright] at h
      | some access =>
          cases hleft : evalPanValueExp state.structs state.locals state.globals state.memory
              state.baseAddress state.topAddress panSemBitVec64BytesInWord left
              (memoryAccess := some access) with
          | none => simp [evalPanValueExp, hleft] at h
          | some leftValue =>
              cases hright : evalPanValueExp state.structs state.locals state.globals
                  state.memory state.baseAddress state.topAddress
                  panSemBitVec64BytesInWord right (memoryAccess := some access) with
              | none => simp [evalPanValueExp, hleft, hright] at h
              | some rightValue =>
                  cases leftValue with
                  | word l =>
                      cases rightValue with
                      | word r =>
                          cases hshift : access.shift operator l r with
                          | none => simp [evalPanValueExp, hleft, hright, hshift] at h
                          | some w =>
                              simp [evalPanValueExp, hleft, hright, hshift,
                                Option.some.injEq] at h
                              subst h
                              simp only [PanValueByteRanged]
                      | rStruct fs => simp [evalPanValueExp, hleft, hright] at h
                      | nStruct nm fs => simp [evalPanValueExp, hleft, hright] at h
                  | rStruct fs => simp [evalPanValueExp, hleft, hright] at h
                  | nStruct nm fs => simp [evalPanValueExp, hleft, hright] at h)
    (by
      intro memoryAccess he v h
      simp only [evalPanValueExp, Option.some.injEq] at h
      subst h
      simp only [PanValueByteRanged])
    (by
      intro memoryAccess he v h
      simp only [evalPanValueExp, Option.some.injEq] at h
      subst h
      simp only [PanValueByteRanged])
    (by
      intro memoryAccess he v h
      simp only [evalPanValueExp, Option.some.injEq] at h
      subst h
      simp only [PanValueByteRanged])
    (by
      intro memoryAccess he values h
      simp only [evalPanValueExp.evalPanValueFields, Option.some.injEq] at h
      subst h
      intro p hp
      simp at hp)
    (by
      intro name expression fields memoryAccess ihHead ihTail he values h
      simp only [ListFieldByteRanged] at he
      obtain ⟨_, heHead, heTail⟩ := he
      simp only [evalPanValueExp.evalPanValueFields] at h
      cases hvalue : evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord expression
          (memoryAccess := memoryAccess) with
      | none => simp [hvalue] at h
      | some head =>
          cases hvalues : evalPanValueExp.evalPanValueFields state.structs state.locals
              state.globals state.memory state.baseAddress state.topAddress
              panSemBitVec64BytesInWord fields (memoryAccess := memoryAccess) with
          | none => simp [hvalue, hvalues] at h
          | some tail =>
              simp [hvalue, hvalues, Option.some.injEq] at h
              subst h
              intro p hp
              rcases List.mem_cons.mp hp with rfl | hp
              · exact ihHead heHead head hvalue
              · exact ihTail heTail tail hvalues p hp)
  exact hmain e access he v h

/-! ## Unconditional all-constructor agreement -/

/-- Byte-ranged field lists have byte-ranged field expressions. -/
theorem listFieldByteRanged_exp {width : Nat} :
    ∀ {fields : List (FieldName × Exp (BitVec width))}, ListFieldByteRanged fields →
      ∀ p ∈ fields, ExpByteRanged p.2 := by
  intro fields
  induction fields with
  | nil => intro _ p hp; simp at hp
  | cons f fs ih =>
      intro h p hp
      simp only [ListFieldByteRanged] at h
      obtain ⟨_, hhead, htail⟩ := h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hhead
      · exact ih htail p hp

/-- Unconditional production/exact expression-evaluation agreement for all
    sixteen `Exp` constructors.  Under `PanSemStateRelExec`, the byte-ranged
    state premise `PanSemStateRelExecRanged`, and a byte-ranged expression, the
    production evaluator run with the state-owned memory access encodes to the
    exact `evalHOLFinite` result.  The `hresRanged` premises of the structured
    `nStruct`/`nField` clauses are discharged by `evalPanValueExp_byteRanged`. -/
theorem evalPanValueExp_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (hranged : PanSemStateRelExecRanged state)
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e) :
    Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord e
          (memoryAccess := some (panSemBitVec64MemoryAccess state)))
      = exact.evalHOLFinite (expToHOL e) := by
  have hctxNames : ∀ p ∈ state.structs, NameRanged p.1 :=
    structContextByteRanged_names state.structs hranged.2.2
  have hmain := evalPanValueExp.induct
    (motive1 := fun expressions memoryAccess =>
      memoryAccess = some (panSemBitVec64MemoryAccess state) →
      ListExpByteRanged expressions →
      ∀ e ∈ expressions,
        Option.map panValueToHOL
            (evalPanValueExp state.structs state.locals state.globals state.memory
              state.baseAddress state.topAddress panSemBitVec64BytesInWord e
              (memoryAccess := memoryAccess))
          = exact.evalHOLFinite (expToHOL e))
    (motive2 := fun expression memoryAccess =>
      memoryAccess = some (panSemBitVec64MemoryAccess state) →
      ExpByteRanged expression →
      Option.map panValueToHOL
          (evalPanValueExp state.structs state.locals state.globals state.memory
            state.baseAddress state.topAddress panSemBitVec64BytesInWord expression
            (memoryAccess := memoryAccess))
        = exact.evalHOLFinite (expToHOL expression))
    (motive3 := fun fields memoryAccess =>
      memoryAccess = some (panSemBitVec64MemoryAccess state) →
      ListFieldByteRanged fields →
      ∀ p ∈ fields,
        Option.map panValueToHOL
            (evalPanValueExp state.structs state.locals state.globals state.memory
              state.baseAddress state.topAddress panSemBitVec64BytesInWord p.2
              (memoryAccess := memoryAccess))
          = exact.evalHOLFinite (expToHOL p.2))
    (by
      intro memoryAccess hmem he e heMem
      simp at heMem)
    (by
      intro expression expressions memoryAccess ihHead ihTail hmem he e heMem
      subst hmem
      simp only [ListExpByteRanged] at he
      obtain ⟨heHead, heTail⟩ := he
      rcases List.mem_cons.mp heMem with rfl | heMem
      · exact ihHead rfl heHead
      · exact ihTail rfl heTail e heMem)
    (by
      intro memoryAccess value hmem he
      subst hmem
      simpa only [expToHOL] using evalPanValueExp_const_agree state exact
        (some (panSemBitVec64MemoryAccess state)) value)
    (by
      intro memoryAccess name hmem he
      subst hmem
      simpa only [expToHOL] using evalPanValueExp_var_local_agree state exact hrel
        (some (panSemBitVec64MemoryAccess state)) name he)
    (by
      intro memoryAccess name hmem he
      subst hmem
      simpa only [expToHOL] using evalPanValueExp_var_global_agree state exact hrel
        (some (panSemBitVec64MemoryAccess state)) name he)
    (by
      intro fields memoryAccess ih hmem he
      subst hmem
      simp only [ExpByteRanged] at he
      simpa only [expToHOL] using evalPanValueExp_rStruct_agree state exact
        (some (panSemBitVec64MemoryAccess state)) fields (ih rfl he))
    (by
      intro index expression memoryAccess ih hmem he
      subst hmem
      simpa only [expToHOL] using evalPanValueExp_rField_agree state exact
        (some (panSemBitVec64MemoryAccess state)) index expression (ih rfl he))
    (by
      intro name fields memoryAccess ih hmem he
      subst hmem
      simp only [ExpByteRanged] at he
      obtain ⟨hname, hfieldsRanged⟩ := he
      have hinfo : ∀ (info : StructInfo), lookupInfo name state.structs = some info →
          (∀ f ∈ info.fields, NameRanged f.1) ∧ (∀ f ∈ info.fields, ShapeByteRanged f.2) :=
        fun info h => lookupInfo_byteRanged h hranged.2.2
      have hres : ∀ p ∈ fields, ∀ v,
          evalPanValueExp state.structs state.locals state.globals state.memory
            state.baseAddress state.topAddress panSemBitVec64BytesInWord p.2
            (memoryAccess := some (panSemBitVec64MemoryAccess state)) = some v →
          PanValueByteRanged v :=
        fun p hp v hv => evalPanValueExp_byteRanged state hranged
          (some (panSemBitVec64MemoryAccess state)) p.2
          (listFieldByteRanged_exp hfieldsRanged p hp) v hv
      simpa only [expToHOL] using evalPanValueExp_nStruct_agree state exact hrel
        (some (panSemBitVec64MemoryAccess state)) name fields hname
        (listFieldByteRanged_names hfieldsRanged) hctxNames hinfo (ih rfl hfieldsRanged) hres)
    (by
      intro name expression memoryAccess ih hmem he
      subst hmem
      simp only [ExpByteRanged] at he
      obtain ⟨hname, hexpRanged⟩ := he
      simpa only [expToHOL] using evalPanValueExp_nField_agree state exact hrel
        (some (panSemBitVec64MemoryAccess state)) name expression hname hctxNames
        (ih rfl hexpRanged)
        (fun v hv => evalPanValueExp_byteRanged state hranged
          (some (panSemBitVec64MemoryAccess state)) expression hexpRanged v hv))
    (by
      intro shape address memoryAccess ih hmem he
      subst hmem
      simp only [ExpByteRanged] at he
      obtain ⟨hshape, haddrRanged⟩ := he
      simpa only [expToHOL] using evalPanValueExp_load_agree state exact hrel hranged shape address hshape
        (ih rfl haddrRanged))
    (by
      intro address memoryAccess ih hmem he
      subst hmem
      simpa only [expToHOL] using evalPanValueExp_load32_agree state exact hrel address (ih rfl he))
    (by
      intro address memoryAccess ih hmem he
      subst hmem
      simpa only [expToHOL] using evalPanValueExp_loadByte_agree state exact hrel address (ih rfl he))
    (by
      intro operator arguments memoryAccess ih hmem he
      subst hmem
      simpa only [expToHOL] using evalPanValueExp_op_agree state exact (panSemBitVec64MemoryAccess state)
        operator arguments (ih rfl he) (panSemBitVec64MemoryAccess_wordOp state))
    (by
      intro operator arguments memoryAccess ih hmem he
      subst hmem
      simpa only [expToHOL] using evalPanValueExp_panOp_agree state exact
        (some (panSemBitVec64MemoryAccess state)) operator arguments (ih rfl he))
    (by
      intro operator left right memoryAccess ihLeft ihRight hmem he
      subst hmem
      simp only [ExpByteRanged] at he
      obtain ⟨heLeft, heRight⟩ := he
      simpa only [expToHOL] using evalPanValueExp_cmp_agree state exact (panSemBitVec64MemoryAccess state)
        operator left right (ihLeft rfl heLeft) (ihRight rfl heRight)
        (fun op l r => panSemBitVec64MemoryAccess_compare state op l r))
    (by
      intro operator left right memoryAccess ihLeft ihRight hmem he
      subst hmem
      simp only [ExpByteRanged] at he
      obtain ⟨heLeft, heRight⟩ := he
      simpa only [expToHOL] using evalPanValueExp_shift_agree state exact (panSemBitVec64MemoryAccess state)
        operator left right (ihLeft rfl heLeft) (ihRight rfl heRight)
        (fun op l r => panSemBitVec64MemoryAccess_shift state op l r))
    (by
      intro memoryAccess hmem he
      subst hmem
      simpa only [expToHOL] using evalPanValueExp_baseAddr_agree state exact hrel
        (some (panSemBitVec64MemoryAccess state)))
    (by
      intro memoryAccess hmem he
      subst hmem
      simpa only [expToHOL] using evalPanValueExp_topAddr_agree state exact hrel
        (some (panSemBitVec64MemoryAccess state)))
    (by
      intro memoryAccess hmem he
      subst hmem
      simpa only [expToHOL] using evalPanValueExp_bytesInWord_agree state exact
        (some (panSemBitVec64MemoryAccess state)))
    (by
      intro memoryAccess hmem he p hp
      simp at hp)
    (by
      intro name expression fields memoryAccess ihHead ihTail hmem he p hp
      subst hmem
      simp only [ListFieldByteRanged] at he
      obtain ⟨_, heHead, heTail⟩ := he
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ihHead rfl heHead
      · exact ihTail rfl heTail p hp)
  exact hmain e (some (panSemBitVec64MemoryAccess state)) rfl he

/-- State-owned expression-evaluation agreement wrapper: the same result through
    `evalPanSemStateExp`. -/
theorem evalPanSemStateExp_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (hranged : PanSemStateRelExecRanged state)
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e) :
    Option.map panValueToHOL (evalPanSemStateExp state e) =
      exact.evalHOLFinite (expToHOL e) := by
  rw [evalPanSemStateExp_64_eq_previous]
  exact evalPanValueExp_agree state exact hrel hranged e he

/-- A byte-ranged expression evaluated under a ranged state yields a
    byte-ranged value. -/
theorem evalPanSemStateExp_byteRanged {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hranged : PanSemStateRelExecRanged state)
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e) (value : PanValue (RiscV.Word 64))
    (hvalue : evalPanSemStateExp state e = some value) : PanValueByteRanged value := by
  rw [evalPanSemStateExp_64_eq_previous] at hvalue
  exact evalPanValueExp_byteRanged state hranged
    (some (panSemBitVec64MemoryAccess state)) e he value hvalue

/-! ## Discharging the expression byte-range premise from the executed program

The all-16 agreement `evalPanValueExp_agree` (`:2494`) and its state wrapper
`evalPanSemStateExp_agree` (`:2671`) take the encoded expression's identifier
bytes as an explicit `ExpByteRanged` premise.  That premise is **not** an extra
assumption beyond the executed compiler path: the parser-backed entrypoints
(`Pipeline.lean:634-671`, e.g. `compileFlapjackEntryCake`'s
`some (.isTrue targetByteRanged)` branch) thread `DeclByteRanged` for their
declarations, and `expsOf_byteRanged`
(`Flapjack/Pancake/PanLang/Prog.lean`) proves the program-level predicate
`ProgByteRanged` already implies `ExpByteRanged` for every expression occurring
directly in the program (`Flapjack.expsOf`).  The wrappers below therefore
discharge the expression premise from that executed byte-range hypothesis.

The **state** premise `PanSemStateRelExecRanged` remains explicit: as recorded
below and in `flapjack-pxn.18.4.3.77.2.15`, parser origin constrains program
syntax but not runtime FFI values, initial/stored globals, or stored record
structures, so it cannot be discharged here. -/

/-- The all-16 expression agreement with its `ExpByteRanged` premise discharged
    from a `ProgByteRanged` program: any expression occurring directly in a
    byte-ranged program is byte-ranged (`expsOf_byteRanged`).  Only the state
    rangedness premise remains explicit. -/
theorem evalPanValueExp_agree_of_mem_expsOf {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (hranged : PanSemStateRelExecRanged state)
    (program : Prog (RiscV.Word 64)) (hprogram : ProgByteRanged program)
    (e : Exp (RiscV.Word 64)) (he : e ∈ expsOf program) :
    Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord e
          (memoryAccess := some (panSemBitVec64MemoryAccess state)))
      = exact.evalHOLFinite (expToHOL e) :=
  evalPanValueExp_agree state exact hrel hranged e
    (expsOf_byteRanged program hprogram e he)

/-- State-owned wrapper of `evalPanValueExp_agree_of_mem_expsOf`, through
    `evalPanSemStateExp`. -/
theorem evalPanSemStateExp_agree_of_mem_expsOf {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (hranged : PanSemStateRelExecRanged state)
    (program : Prog (RiscV.Word 64)) (hprogram : ProgByteRanged program)
    (e : Exp (RiscV.Word 64)) (he : e ∈ expsOf program) :
    Option.map panValueToHOL (evalPanSemStateExp state e) =
      exact.evalHOLFinite (expToHOL e) :=
  evalPanSemStateExp_agree state exact hrel hranged e
    (expsOf_byteRanged program hprogram e he)

/-- `FunDeclByteRanged`-level form: the parser/pass `DeclByteRanged` hypothesis
    reaches a function body as `FunDeclByteRanged`, whose `ProgByteRanged`
    conjunct (`hd.2.2.1`) discharges the expression premise for any expression
    in the body. -/
theorem evalPanValueExp_agree_of_funDeclByteRanged {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (hranged : PanSemStateRelExecRanged state)
    (d : FunDeclOf 64) (hd : FunDeclByteRanged d)
    (e : Exp (RiscV.Word 64)) (he : e ∈ expsOf d.body) :
    Option.map panValueToHOL
        (evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord e
          (memoryAccess := some (panSemBitVec64MemoryAccess state)))
      = exact.evalHOLFinite (expToHOL e) :=
  evalPanValueExp_agree_of_mem_expsOf state exact hrel hranged d.body hd.2.2.1 e he

/-- The production assignment-validity test agrees with the exact
    `is_valid_value` test on encoded values under `PanSemStateRelExec` and the
    byte-range premise.  This is the validity half of the `Assign` clause
    agreement: both sides look up the destination and compare the shape of the
    incoming value with the stored one. -/
theorem panValueAssignmentValid_eq_isValidValueHOLFinite {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (kind : VarKind) (name : VarName) (hname : NameRanged name)
    (value : PanValue (RiscV.Word 64)) (hvalue : PanValueByteRanged value) :
    panValueAssignmentValid production.structs production.locals production.globals
        kind name value
      = isValidValueHOLFinite exact kind (ofString name) (panValueToHOL value) := by
  cases kind
  · have hold := hrel.1 name hname
    simp only [panValueAssignmentValid, isValidValueHOLFinite, lookupKvarHOLFinite]
    rw [show exact.locals.lookup (ofString name) =
        Option.map panValueToHOL (production.locals name) from hold.symm]
    cases hl : production.locals name with
    | none => rfl
    | some old =>
        have hbv : PanValueByteRanged old := hranged.1 name old hl
        show panShapeMatches (panValueShape production.structs value)
              (panValueShape production.structs old)
          = shapeEqHOL (shapeOfHOLExact (panValueToHOL value))
              (shapeOfHOLExact (panValueToHOL old))
        rw [shapeOfHOLExact_panValueToHOL, shapeOfHOLExact_panValueToHOL]
        exact panShapeMatches_eq_shapeEqHOL _ _
          (panValueShape_byteRanged _ _ hvalue) (panValueShape_byteRanged _ _ hbv)
  · have hold := hrel.2.1 name hname
    simp only [panValueAssignmentValid, isValidValueHOLFinite, lookupKvarHOLFinite]
    rw [show exact.globals.lookup (ofString name) =
        Option.map panValueToHOL (production.globals name) from hold.symm]
    cases hl : production.globals name with
    | none => rfl
    | some old =>
        have hbv : PanValueByteRanged old := hranged.2.1 name old hl
        show panShapeMatches (panValueShape production.structs value)
              (panValueShape production.structs old)
          = shapeEqHOL (shapeOfHOLExact (panValueToHOL value))
              (shapeOfHOLExact (panValueToHOL old))
        rw [shapeOfHOLExact_panValueToHOL, shapeOfHOLExact_panValueToHOL]
        exact panShapeMatches_eq_shapeEqHOL _ _
          (panValueShape_byteRanged _ _ hvalue) (panValueShape_byteRanged _ _ hbv)

/-- The finite-support `evalHOLFinite` agrees with the `Classical`-instance
    `evalHOLExact` call used by the clause reduction lemmas. -/
theorem evalHOLFinite_eq_classical {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [DecidablePred state.memaddrs]
    (e : ExpHOL width) :
    @evalHOLExact width σ _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) e
      = state.evalHOLFinite e := by
  unfold evalHOLFinite
  rw [Subsingleton.elim (fun address => Classical.propDecidable (state.memaddrs address))
    (inferInstance : DecidablePred state.memaddrs)]

/-- Production/exact agreement for the `Assign` constructor, assembled from the
    all-constructor expression agreement
    (`evalPanSemStateExp_agree`/`evalPanSemStateExp_byteRanged`), the
    assignment-validity parity, and the `TotalEvalBridge` preservation slice
    `panSemTotalAssignClause_agree`. -/
theorem panSemTotalEvaluate_assign_agree {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (kind : VarKind) (name : VarName) (hname : NameRanged name)
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e) :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive (.assign kind name e) production).1
        (evaluateHOLFiniteState exact (.assign kind (ofString name) (expToHOL e))).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive (.assign kind name e) production).2
        (evaluateHOLFiniteState exact (.assign kind (ofString name) (expToHOL e))).2.toExact := by
  rw [panSemTotalEvaluate]
  have hval := evalPanSemStateExp_agree production exact hrel hranged e he
  have hclass := evalHOLFinite_eq_classical exact (expToHOL e)
  cases hest : evalPanSemStateExp production e with
  | none =>
      have hexactEval : @evalHOLExact 64 σ _ exact.toExact
          (fun address => Classical.propDecidable (exact.memaddrs address)) (expToHOL e)
          = none := by
        rw [hclass, ← hval, hest]
        rfl
      rw [panSemTotalAssignClause_none production kind name e hest]
      rw [evaluateHOLFiniteState_assign, hexactEval]
      exact ⟨trivial, hrel⟩
  | some value =>
      have hvalue : exact.evalHOLFinite (expToHOL e) = some (panValueToHOL value) := by
        rw [← hval, hest]
        rfl
      have hexactEval : @evalHOLExact 64 σ _ exact.toExact
          (fun address => Classical.propDecidable (exact.memaddrs address)) (expToHOL e)
          = some (panValueToHOL value) := by
        rw [hclass]
        exact hvalue
      have hbv := evalPanSemStateExp_byteRanged production hranged e he value hest
      by_cases hprod : panValueAssignmentValid production.structs production.locals
          production.globals kind name value = true
      · have hparity := panValueAssignmentValid_eq_isValidValueHOLFinite production exact
          hrel hranged kind name hname value hbv
        have hexactValid : isValidValueHOLFinite exact kind (ofString name)
            (panValueToHOL value) = true := by
          rw [← hparity]
          exact hprod
        exact panSemTotalAssignClause_agree production exact hrel kind name hname e value
          hest hexactEval hprod hexactValid
      · have hprod' : panValueAssignmentValid production.structs production.locals
            production.globals kind name value = false := Bool.eq_false_iff.mpr hprod
        have hparity := panValueAssignmentValid_eq_isValidValueHOLFinite production exact
          hrel hranged kind name hname value hbv
        have hexactInvalid : isValidValueHOLFinite exact kind (ofString name)
            (panValueToHOL value) = false := by
          rw [← hparity]
          exact hprod'
        rw [panSemTotalAssignClause_invalid production kind name e value hest hprod']
        rw [evaluateHOLFiniteState_assign, hexactEval]
        simp only [hexactInvalid]
        exact ⟨trivial, hrel⟩

/-- The fully assembled production/exact `Assign`-clause agreement with both
    expression premises (`NameRanged name`, `ExpByteRanged e`) discharged from
    the executed program node's `ProgByteRanged` hypothesis.  This is the
    non-trivial connection of a parity slice to the parser/pass byte-range
    evidence: the assignment node that the executed evaluator sees is exactly
    the node whose rangedness the parser path supplies. -/
theorem panSemTotalEvaluate_assign_agree_of_progByteRanged {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (kind : VarKind) (name : VarName) (e : Exp (RiscV.Word 64))
    (hprogram : ProgByteRanged (.assign kind name e)) :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive (.assign kind name e) production).1
        (evaluateHOLFiniteState exact (.assign kind (ofString name) (expToHOL e))).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive (.assign kind name e) production).2
        (evaluateHOLFiniteState exact (.assign kind (ofString name) (expToHOL e))).2.toExact := by
  obtain ⟨hname, he⟩ := hprogram
  exact panSemTotalEvaluate_assign_agree primitive production exact hrel hranged
    kind name hname e he

/-- Production/exact agreement for the `Store` constructor, assembled from the
    all-constructor expression agreement
    (`evalPanSemStateExp_agree`/`evalHOLFinite_eq_classical`) and the
    `TotalEvalBridge` clause slice `panSemTotalStoreClause_agree`.  Both the
    destination and the source evaluation agreement are discharged from their
    `ExpByteRanged` hypotheses; the success, invalid-address (non-word
    destination), and failed-expression branches are all covered without any
    target run, result, or post-state premise. -/
theorem panSemTotalEvaluate_store_agree {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (address value : Exp (RiscV.Word 64))
    (haddress : ExpByteRanged address) (hvalue : ExpByteRanged value) :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive (.store address value) production).1
        (evaluateHOLFiniteState exact (.store (expToHOL address) (expToHOL value))).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive (.store address value) production).2
        (evaluateHOLFiniteState exact (.store (expToHOL address) (expToHOL value))).2.toExact := by
  rw [panSemTotalEvaluate]
  have haddr := evalPanSemStateExp_agree production exact hrel hranged address haddress
  have hclassAddr := evalHOLFinite_eq_classical exact (expToHOL address)
  cases hAddr : evalPanSemStateExp production address with
  | none =>
      have hexactAddr : @evalHOLExact 64 σ _ exact.toExact
          (fun a => Classical.propDecidable (exact.memaddrs a)) (expToHOL address) = none := by
        rw [hclassAddr, ← haddr, hAddr]
        rfl
      rw [panSemTotalStoreClause_none production address value hAddr]
      simp only [evaluateHOLFiniteState_store, hexactAddr]
      exact ⟨trivial, hrel⟩
  | some addrValue =>
      have hexactAddr : @evalHOLExact 64 σ _ exact.toExact
          (fun a => Classical.propDecidable (exact.memaddrs a)) (expToHOL address)
          = some (panValueToHOL addrValue) := by
        rw [hclassAddr, ← haddr, hAddr]
        rfl
      cases addrValue with
      | word addr =>
          have hval := evalPanSemStateExp_agree production exact hrel hranged value hvalue
          have hclassVal := evalHOLFinite_eq_classical exact (expToHOL value)
          cases hValue : evalPanSemStateExp production value with
          | none =>
              have hexactValue : @evalHOLExact 64 σ _ exact.toExact
                  (fun a => Classical.propDecidable (exact.memaddrs a)) (expToHOL value) = none := by
                rw [hclassVal, ← hval, hValue]
                rfl
              have hclause : panSemTotalStoreClause production address value = (some .error, production) := by
                simp [panSemTotalStoreClause, panSemTotalExprStep, hAddr, hValue]
              rw [hclause]
              simp only [evaluateHOLFiniteState_store, hexactAddr, panValueToHOL_word, hexactValue]
              exact ⟨trivial, hrel⟩
          | some storedValue =>
              have hexactAddr' : @evalHOLExact 64 σ _ exact.toExact
                  (fun a => Classical.propDecidable (exact.memaddrs a)) (expToHOL address)
                  = some (.val (.word addr)) := by
                simpa only [panValueToHOL_word] using hexactAddr
              have hexactValue : @evalHOLExact 64 σ _ exact.toExact
                  (fun a => Classical.propDecidable (exact.memaddrs a)) (expToHOL value)
                  = some (panValueToHOL storedValue) := by
                rw [hclassVal, ← hval, hValue]
                rfl
              exact panSemTotalStoreClause_agree production exact hrel address value addr storedValue
                hAddr hValue hexactAddr' hexactValue
      | rStruct fields =>
          have hclause : panSemTotalStoreClause production address value = (some .error, production) := by
            simp [panSemTotalStoreClause, panSemTotalExprStep, hAddr]
          rw [hclause]
          simp only [evaluateHOLFiniteState_store, hexactAddr, panValueToHOL]
          exact ⟨trivial, hrel⟩
      | nStruct name fields =>
          have hclause : panSemTotalStoreClause production address value = (some .error, production) := by
            simp [panSemTotalStoreClause, panSemTotalExprStep, hAddr]
          rw [hclause]
          simp only [evaluateHOLFiniteState_store, hexactAddr, panValueToHOL]
          exact ⟨trivial, hrel⟩

/-- The fully assembled production/exact `Store`-clause agreement with both
    expression premises (`ExpByteRanged address`, `ExpByteRanged value`)
    discharged from the executed program node's `ProgByteRanged` hypothesis
    (mirroring `panSemTotalEvaluate_assign_agree_of_progByteRanged`). -/
theorem panSemTotalEvaluate_store_agree_of_progByteRanged {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (address value : Exp (RiscV.Word 64))
    (hprogram : ProgByteRanged (.store address value)) :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive (.store address value) production).1
        (evaluateHOLFiniteState exact (.store (expToHOL address) (expToHOL value))).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive (.store address value) production).2
        (evaluateHOLFiniteState exact (.store (expToHOL address) (expToHOL value))).2.toExact := by
  obtain ⟨haddress, hvalue⟩ := hprogram
  exact panSemTotalEvaluate_store_agree primitive production exact hrel hranged
    address value haddress hvalue

/-! ## Production/exact agreement for the `Return` and `Raise` constructors

`panSemTotalReturnClause` (`TotalSteps.lean:177`) and `panSemTotalRaiseClause`
(`TotalSteps.lean:236`) are the production leaf clauses, and their exact
counterparts are the tagged `evaluateHOLFiniteState_return`/`_raise`
(`StateExactFiniteMap.lean:2318`/`:2353`).  The agreement below is assembled
from the all-constructor expression agreement (`evalPanSemStateExp_agree`), the
shape/size parity bridges (`shapeOfHOLExact_panValueToHOL`,
`panValueShape_eq_panSemShapeOf_tagged`,
`sizeOfShWithCtxt_eq_sizeOfShapeWithContextHOL`, `panShapeMatches_eq_shapeEqHOL`)
and the `empty_locals`/state relation preservation.  Every branch is
represented: a failed expression evaluation, an oversized value, an absent
exception shape, and a mismatched exception shape all return `SOME Error` with
the state unchanged, while a byte-ranged value within the size bound (and with
the declared exception shape for `Raise`) returns the corresponding result and
clears the locals.  No target result and no post-state relation are assumed.
Untagged Flapjack-specific bridge infrastructure; no `@[hol]` tag. -/

/-- The `toStringOfBytes` image of an `MlString` is `NameRanged`: decoding bytes
    to characters yields codes below 256. -/
theorem nameRanged_toStringOfBytes_bridge (m : MlS) :
    NameRanged (toStringOfBytes m) := by
  intro character hmem
  simp only [toStringOfBytes, String.toList_ofList, List.mem_map] at hmem
  obtain ⟨byte, _hbyte, rfl⟩ := hmem
  have hb : byte.toNat < 256 := by simpa using byte.isLt
  rw [ofNat_toNat_char byte]
  exact hb

/-- Decoding a `ShapeHOL` to a production shape is byte-ranged. -/
theorem shapeOfHOL_byteRanged_bridge :
    (shape : ShapeHOL) → ShapeByteRanged (shapeOfHOL shape)
  | .one => by simp [ShapeByteRanged, shapeOfHOL]
  | .named name => by
      simpa [ShapeByteRanged, shapeOfHOL] using nameRanged_toStringOfBytes_bridge name
  | .comb fields => by
      simp only [shapeOfHOL, ShapeByteRanged]
      intro shape hshape
      obtain ⟨source, _hsource, rfl⟩ := List.mem_map.mp hshape
      exact shapeOfHOL_byteRanged_bridge source

/-- A decoded exact expression is byte-ranged, so the production
    `ExpByteRanged` premise of the expression agreement is always available for
    `expOfHOL`. -/
theorem expOfHOL_byteRanged_bridge {width : Nat} [NeZero width] :
    (expression : ExpHOL width) → ExpByteRanged (expOfHOL expression) :=
  ExpHOL.rec
    (motive_1 := fun expression => ExpByteRanged (expOfHOL expression))
    (motive_2 := fun expressions =>
      ListExpByteRanged (expressions.map expOfHOL))
    (motive_3 := fun fields =>
      ListFieldByteRanged (fields.map
        (fun p => (toStringOfBytes p.1, expOfHOL p.2))))
    (motive_4 := fun field =>
      (∀ c ∈ toStringOfBytes field.1 |>.toList, c.toNat < 256) ∧
        ExpByteRanged (expOfHOL field.2))
    (by simp [expOfHOL, ExpByteRanged])
    (fun _kind name => by
      simpa [expOfHOL, ExpByteRanged] using nameRanged_toStringOfBytes_bridge name)
    (fun _fields ih => by simpa [expOfHOL, ExpByteRanged, ListExpByteRanged] using ih)
    (fun _index _value ih => by simpa [expOfHOL, ExpByteRanged] using ih)
    (fun name _fields ih => by
      simpa [expOfHOL, ExpByteRanged, ListFieldByteRanged] using
        And.intro (nameRanged_toStringOfBytes_bridge name) ih)
    (fun name _value ih => by
      simpa [expOfHOL, ExpByteRanged] using
        And.intro (nameRanged_toStringOfBytes_bridge name) ih)
    (fun shape _address ih => by
      simpa [expOfHOL, ExpByteRanged] using
        And.intro (shapeOfHOL_byteRanged_bridge shape) ih)
    (fun _address ih => by simpa [expOfHOL, ExpByteRanged] using ih)
    (fun _address ih => by simpa [expOfHOL, ExpByteRanged] using ih)
    (fun _operator _args ih => by simpa [expOfHOL, ExpByteRanged] using ih)
    (fun _operator _args ih => by simpa [expOfHOL, ExpByteRanged] using ih)
    (fun _operator _left _right ihl ihr => by
      simpa [expOfHOL, ExpByteRanged] using And.intro ihl ihr)
    (fun _operator _left _right ihl ihr => by
      simpa [expOfHOL, ExpByteRanged] using And.intro ihl ihr)
    (by simp [expOfHOL, ExpByteRanged])
    (by simp [expOfHOL, ExpByteRanged])
    (by simp [expOfHOL, ExpByteRanged])
    (by simp [ListExpByteRanged])
    (fun _head _tail ihHead ihTail => by
      simpa [ListExpByteRanged, List.map] using And.intro ihHead ihTail)
    (by simp [ListFieldByteRanged])
    (fun _head _tail ihHead ihTail => by
      simpa [ListFieldByteRanged, List.map] using
        And.intro ihHead.1 (And.intro ihHead.2 ihTail))
    (fun fst snd ih => by
      exact ⟨nameRanged_toStringOfBytes_bridge fst, ih⟩)

/-- Production/exact agreement for the `Return` constructor. -/
theorem panSemTotalEvaluate_return_agree {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (expression : ExpHOL 64) :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive
          (.return (expOfHOL expression) : Prog (RiscV.Word 64)) production).1
        (evaluateHOLFiniteState exact (.return expression : ProgHOL 64)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive
          (.return (expOfHOL expression) : Prog (RiscV.Word 64)) production).2
        (evaluateHOLFiniteState exact (.return expression : ProgHOL 64)).2.toExact := by
  have hexp := expOfHOL_byteRanged_bridge expression
  have hval := evalPanSemStateExp_agree production exact hrel hranged
    (expOfHOL expression) hexp
  simp only [expToHOL_expOfHOL] at hval
  have hclass := evalHOLFinite_eq_classical exact expression
  rw [panSemTotalEvaluate]
  cases hest : evalPanSemStateExp production (expOfHOL expression) with
  | none =>
      have hexactEval : @evalHOLExact 64 σ _ exact.toExact
          (fun address => Classical.propDecidable (exact.memaddrs address)) expression
          = none := by
        rw [hclass, ← hval, hest]
        rfl
      rw [panSemTotalReturnClause_none production (expOfHOL expression) hest]
      rw [evaluateHOLFiniteState_return, hexactEval]
      exact ⟨trivial, hrel⟩
  | some value =>
      have hvalue : exact.evalHOLFinite expression = some (panValueToHOL value) := by
        rw [← hval, hest]
        rfl
      have hexactEval : @evalHOLExact 64 σ _ exact.toExact
          (fun address => Classical.propDecidable (exact.memaddrs address)) expression
          = some (panValueToHOL value) := by
        rw [hclass]
        exact hvalue
      have hbv := evalPanSemStateExp_byteRanged production hranged
        (expOfHOL expression) hexp value hest
      have hshapeRanged : ShapeByteRanged (panSemShapeOf value) := by
        have h := panValueShape_byteRanged production.structs value hbv
        rwa [panValueShape_eq_panSemShapeOf_tagged production.structs value] at h
      have hshapeExact : shapeOfHOLExact (panValueToHOL value) =
          shapeToHOL (panSemShapeOf value) := by
        rw [shapeOfHOLExact_panValueToHOL production.structs value,
          panValueShape_eq_panSemShapeOf_tagged production.structs value]
      have hstructs : structContextToHOL production.structs.toHOL = exact.structs :=
        hrel.2.2.1
      have hsizeEq : sizeOfShWithCtxt production.structs.toHOL (panSemShapeOf value) =
          sizeOfShapeWithContextHOL exact.structs
            (shapeOfHOLExact (panValueToHOL value)) := by
        rw [hshapeExact, ← hstructs]
        exact sizeOfShWithCtxt_eq_sizeOfShapeWithContextHOL production.structs.toHOL
          (fun p hp => (hranged.2.2 p hp).1) (panSemShapeOf value) hshapeRanged
      by_cases hsize : sizeOfShWithCtxt production.structs.toHOL (panSemShapeOf value) ≤ 32
      · have hsizeExact : sizeOfShapeWithContextHOL exact.structs
            (shapeOfHOLExact (panValueToHOL value)) ≤ 32 := by
          rw [← hsizeEq]
          exact hsize
        rw [panSemTotalReturnClause_some production (expOfHOL expression) value hest hsize]
        rw [evaluateHOLFiniteState_return, hexactEval]
        simp only [hsizeExact, if_true]
        exact ⟨rfl, by
          simpa only [panEmptyLocals, toExact_emptyLocalsHOLFinite] using
            PanSemStateRelExec.emptyLocals hrel⟩
      · have hsizeExact : ¬ sizeOfShapeWithContextHOL exact.structs
            (shapeOfHOLExact (panValueToHOL value)) ≤ 32 := by
          rw [← hsizeEq]
          exact hsize
        rw [show panSemTotalReturnClause production (expOfHOL expression) =
            (some .error, production) from by
          simp [panSemTotalReturnClause, panSemTotalExprStep, hest, hsize]]
        rw [evaluateHOLFiniteState_return, hexactEval]
        simp only [hsizeExact, if_false]
        exact ⟨trivial, hrel⟩

/-- Production/exact agreement for the `Raise` constructor.  The extra premise
    `hexnRanged` records that the production exception shapes are byte-ranged:
    `PanSemStateRelExec` compares exception shapes only through the lossy
    `shapeToHOL`, so without it a decoded exact shape could match while the
    production `panShapeMatches` test fails on an out-of-range exception name. -/
theorem panSemTotalEvaluate_raise_agree {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (hexnRanged : ∀ eid shape, production.exceptionShapes eid = some shape →
      ShapeByteRanged shape)
    (exceptionId : MlS) (expression : ExpHOL 64) :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive
          (.raise (toStringOfBytes exceptionId) (expOfHOL expression) :
            Prog (RiscV.Word 64)) production).1
        (evaluateHOLFiniteState exact (.raise exceptionId expression : ProgHOL 64)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive
          (.raise (toStringOfBytes exceptionId) (expOfHOL expression) :
            Prog (RiscV.Word 64)) production).2
        (evaluateHOLFiniteState exact (.raise exceptionId expression : ProgHOL 64)).2.toExact := by
  have hexp := expOfHOL_byteRanged_bridge expression
  have hval := evalPanSemStateExp_agree production exact hrel hranged
    (expOfHOL expression) hexp
  simp only [expToHOL_expOfHOL] at hval
  have hclass := evalHOLFinite_eq_classical exact expression
  have heid : NameRanged (toStringOfBytes exceptionId) :=
    nameRanged_toStringOfBytes_bridge exceptionId
  have hshapeRel := hrel.2.2.2.2.1 (toStringOfBytes exceptionId) heid
  rw [ofString_toStringOfBytes] at hshapeRel
  rw [panSemTotalEvaluate]
  cases hest : evalPanSemStateExp production (expOfHOL expression) with
  | none =>
      have hexactEval : @evalHOLExact 64 σ _ exact.toExact
          (fun address => Classical.propDecidable (exact.memaddrs address)) expression
          = none := by
        rw [hclass, ← hval, hest]
        rfl
      have hexactRaise : evaluateHOLFiniteState exact
          (.raise exceptionId expression : ProgHOL 64) = (some .error, exact) := by
        rw [evaluateHOLFiniteState_raise, hexactEval]
        cases h : exact.eshapes.lookup exceptionId <;> rfl
      rw [panSemTotalRaiseClause_none production (toStringOfBytes exceptionId)
        (expOfHOL expression) hest, hexactRaise]
      exact ⟨trivial, hrel⟩
  | some value =>
      have hvalue : exact.evalHOLFinite expression = some (panValueToHOL value) := by
        rw [← hval, hest]
        rfl
      have hexactEval : @evalHOLExact 64 σ _ exact.toExact
          (fun address => Classical.propDecidable (exact.memaddrs address)) expression
          = some (panValueToHOL value) := by
        rw [hclass]
        exact hvalue
      have hbv := evalPanSemStateExp_byteRanged production hranged
        (expOfHOL expression) hexp value hest
      have hshapeRanged : ShapeByteRanged (panSemShapeOf value) := by
        have h := panValueShape_byteRanged production.structs value hbv
        rwa [panValueShape_eq_panSemShapeOf_tagged production.structs value] at h
      have hshapeExact : shapeOfHOLExact (panValueToHOL value) =
          shapeToHOL (panSemShapeOf value) := by
        rw [shapeOfHOLExact_panValueToHOL production.structs value,
          panValueShape_eq_panSemShapeOf_tagged production.structs value]
      have hstructs : structContextToHOL production.structs.toHOL = exact.structs :=
        hrel.2.2.1
      have hsizeEq : sizeOfShWithCtxt production.structs.toHOL (panSemShapeOf value) =
          sizeOfShapeWithContextHOL exact.structs
            (shapeOfHOLExact (panValueToHOL value)) := by
        rw [hshapeExact, ← hstructs]
        exact sizeOfShWithCtxt_eq_sizeOfShapeWithContextHOL production.structs.toHOL
          (fun p hp => (hranged.2.2 p hp).1) (panSemShapeOf value) hshapeRanged
      cases hsh : production.exceptionShapes (toStringOfBytes exceptionId) with
      | none =>
          have hlookup : exact.eshapes.lookup exceptionId = none := by
            change exact.toExact.eshapes exceptionId = none
            rw [← hshapeRel, hsh]
            rfl
          have hexactRaise : evaluateHOLFiniteState exact
              (.raise exceptionId expression : ProgHOL 64) = (some .error, exact) := by
            rw [evaluateHOLFiniteState_raise, hlookup, hexactEval]
          rw [show panSemTotalRaiseClause production (toStringOfBytes exceptionId)
              (expOfHOL expression) = (some .error, production) from by
            simp [panSemTotalRaiseClause, panSemTotalExprStep, hest, hsh], hexactRaise]
          exact ⟨trivial, hrel⟩
      | some shape =>
          have hshapeLookup : exact.eshapes.lookup exceptionId =
              some (shapeToHOL shape) := by
            change exact.toExact.eshapes exceptionId = some (shapeToHOL shape)
            rw [← hshapeRel, hsh]
            rfl
          have hshapeByte : ShapeByteRanged shape :=
            hexnRanged (toStringOfBytes exceptionId) shape hsh
          have hmatch : panShapeMatches shape (panSemShapeOf value) =
              shapeEqHOL (shapeToHOL shape) (shapeOfHOLExact (panValueToHOL value)) := by
            rw [panShapeMatches_eq_shapeEqHOL shape (panSemShapeOf value)
              hshapeByte hshapeRanged, ← hshapeExact]
          have hcondBool :
              (shapeOfHOLExact (panValueToHOL value) = shapeToHOL shape ∧
                sizeOfShapeWithContextHOL exact.structs
                  (shapeOfHOLExact (panValueToHOL value)) ≤ 32)
              ↔ (panShapeMatches shape (panSemShapeOf value) &&
                  decide (sizeOfShWithCtxt production.structs.toHOL
                    (panSemShapeOf value) ≤ 32)) = true := by
            rw [Bool.and_eq_true, decide_eq_true_iff, ← hsizeEq]
            constructor
            · rintro ⟨heq, hsz⟩
              refine ⟨?_, hsz⟩
              rw [hmatch]
              exact (shapeEqHOL_eq_true _ _).mpr heq.symm
            · rintro ⟨hm, hsz⟩
              refine ⟨?_, hsz⟩
              have hse : shapeEqHOL (shapeToHOL shape)
                  (shapeOfHOLExact (panValueToHOL value)) = true := by
                rw [← hmatch]
                exact hm
              exact ((shapeEqHOL_eq_true _ _).mp hse).symm
          by_cases hcond : (panShapeMatches shape (panSemShapeOf value) &&
              decide (sizeOfShWithCtxt production.structs.toHOL
                (panSemShapeOf value) ≤ 32)) = true
          · have hcond' : panShapeMatches shape (panSemShapeOf value) = true ∧
                decide (sizeOfShWithCtxt production.structs.toHOL
                  (panSemShapeOf value) ≤ 32) = true := by
              simpa only [Bool.and_eq_true] using hcond
            obtain ⟨hmatchTrue, hsizeDecide⟩ := hcond'
            have hsizeTrue : sizeOfShWithCtxt production.structs.toHOL
                (panSemShapeOf value) ≤ 32 := decide_eq_true_iff.mp hsizeDecide
            rw [panSemTotalRaiseClause_some production (toStringOfBytes exceptionId)
              (expOfHOL expression) value shape hest hsh hmatchTrue hsizeTrue]
            rw [evaluateHOLFiniteState_raise, hshapeLookup, hexactEval]
            dsimp only
            rw [if_pos (hcondBool.mpr hcond)]
            exact ⟨⟨ofString_toStringOfBytes exceptionId, rfl⟩, by
              simpa only [panEmptyLocals, toExact_emptyLocalsHOLFinite] using
                PanSemStateRelExec.emptyLocals hrel⟩
          · have hcondFalse : (panShapeMatches shape (panSemShapeOf value) &&
                decide (sizeOfShWithCtxt production.structs.toHOL
                  (panSemShapeOf value) ≤ 32)) = false := Bool.eq_false_iff.mpr hcond
            rw [show panSemTotalRaiseClause production (toStringOfBytes exceptionId)
                (expOfHOL expression) = (some .error, production) from by
              simp [panSemTotalRaiseClause, panSemTotalExprStep, hest, hsh, hcondFalse]]
            rw [evaluateHOLFiniteState_raise, hshapeLookup, hexactEval]
            dsimp only
            rw [if_neg (fun h => hcond (hcondBool.mp h))]
            exact ⟨trivial, hrel⟩

/-- Production/exact agreement for the `StoreByte` constructor: both evaluators
    evaluate the destination and the source to words, then store the low byte;
    evaluation failure, a non-word operand, or a failed store yields `Error` with
    the state unchanged.  The memory step is `panSemStateRelExec_storeByte`. -/
theorem panSemTotalEvaluate_storeByte_agree {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (destination source : ExpHOL 64) :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive
          (.storeByte (expOfHOL destination) (expOfHOL source) : Prog (RiscV.Word 64))
          production).1
        (evaluateHOLFiniteState exact (.storeByte destination source : ProgHOL 64)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive
          (.storeByte (expOfHOL destination) (expOfHOL source) : Prog (RiscV.Word 64))
          production).2
        (evaluateHOLFiniteState exact (.storeByte destination source : ProgHOL 64)).2.toExact := by
  have hd := evalPanSemStateExp_agree production exact hrel hranged
    (expOfHOL destination) (expOfHOL_byteRanged_bridge destination)
  have hs := evalPanSemStateExp_agree production exact hrel hranged
    (expOfHOL source) (expOfHOL_byteRanged_bridge source)
  simp only [expToHOL_expOfHOL, ← evalHOLFinite_eq_classical] at hd hs
  rw [panSemTotalEvaluate, evaluateHOLFiniteState_storeByte, ← hd]
  unfold panSemTotalStoreByteClause panSemTotalExprStep
  cases hed : evalPanSemStateExp production (expOfHOL destination) with
  | none => exact ⟨trivial, hrel⟩
  | some dv =>
    cases dv with
    | rStruct _ => simp only [Option.map_some, panValueToHOL.eq_2]; exact ⟨trivial, hrel⟩
    | nStruct _ _ => simp only [Option.map_some, panValueToHOL.eq_3]; exact ⟨trivial, hrel⟩
    | word a =>
      simp only [Option.map_some, panValueToHOL_word]
      rw [← hs]
      cases hes : evalPanSemStateExp production (expOfHOL source) with
      | none => exact ⟨trivial, hrel⟩
      | some sv =>
        cases sv with
        | rStruct _ => simp only [Option.map_some, panValueToHOL.eq_2]; exact ⟨trivial, hrel⟩
        | nStruct _ _ => simp only [Option.map_some, panValueToHOL.eq_3]; exact ⟨trivial, hrel⟩
        | word w =>
          simp only [Option.map_some, panValueToHOL_word]
          have hb := panSemStateRelExec_storeByte production exact.toExact hrel a w
          revert hb
          cases (panSemBitVec64MemoryAccess production).storeByte
              (panSemBitVec64MemoryAccess production).domain
              production.memory panSemBitVec64BytesInWord a w <;>
            cases @panMemStoreByteWord8HOL 64 _ exact.memory exact.memaddrs
              (fun a => Classical.propDecidable (exact.memaddrs a)) exact.be a
              (BitVec.ofNat 8 w.toNat) <;>
            intro hb <;> first | exact hb.elim | exact ⟨trivial, hrel⟩ | exact ⟨trivial, hb⟩

/-- Production/exact agreement for the `Store32` constructor, analogous to
    `panSemTotalEvaluate_storeByte_agree`; the memory step (alignment, domain,
    and the big/little-endian byte order) is `panSemStateRelExec_store32`. -/
theorem panSemTotalEvaluate_store32_agree {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (destination source : ExpHOL 64) :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive
          (.store32 (expOfHOL destination) (expOfHOL source) : Prog (RiscV.Word 64))
          production).1
        (evaluateHOLFiniteState exact (.store32 destination source : ProgHOL 64)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive
          (.store32 (expOfHOL destination) (expOfHOL source) : Prog (RiscV.Word 64))
          production).2
        (evaluateHOLFiniteState exact (.store32 destination source : ProgHOL 64)).2.toExact := by
  have hd := evalPanSemStateExp_agree production exact hrel hranged
    (expOfHOL destination) (expOfHOL_byteRanged_bridge destination)
  have hs := evalPanSemStateExp_agree production exact hrel hranged
    (expOfHOL source) (expOfHOL_byteRanged_bridge source)
  simp only [expToHOL_expOfHOL, ← evalHOLFinite_eq_classical] at hd hs
  rw [panSemTotalEvaluate, evaluateHOLFiniteState_store32, ← hd]
  unfold panSemTotalStore32Clause panSemTotalExprStep
  cases hed : evalPanSemStateExp production (expOfHOL destination) with
  | none => exact ⟨trivial, hrel⟩
  | some dv =>
    cases dv with
    | rStruct _ => simp only [Option.map_some, panValueToHOL.eq_2]; exact ⟨trivial, hrel⟩
    | nStruct _ _ => simp only [Option.map_some, panValueToHOL.eq_3]; exact ⟨trivial, hrel⟩
    | word a =>
      simp only [Option.map_some, panValueToHOL_word]
      rw [← hs]
      cases hes : evalPanSemStateExp production (expOfHOL source) with
      | none => exact ⟨trivial, hrel⟩
      | some sv =>
        cases sv with
        | rStruct _ => simp only [Option.map_some, panValueToHOL.eq_2]; exact ⟨trivial, hrel⟩
        | nStruct _ _ => simp only [Option.map_some, panValueToHOL.eq_3]; exact ⟨trivial, hrel⟩
        | word w =>
          simp only [Option.map_some, panValueToHOL_word]
          have hb := panSemStateRelExec_store32 production exact.toExact hrel a w
          revert hb
          cases (panSemBitVec64MemoryAccess production).store32
              (panSemBitVec64MemoryAccess production).domain
              production.memory panSemBitVec64BytesInWord a w <;>
            cases @panMemStore32HOL 64 _ exact.memory exact.memaddrs
              (fun a => Classical.propDecidable (exact.memaddrs a)) exact.be a
              (BitVec.ofNat 32 w.toNat) <;>
            intro hb <;> first | exact hb.elim | exact ⟨trivial, hrel⟩ | exact ⟨trivial, hb⟩

/-! ## Rangedness preservation and the `PanSemStateRelExec`/rangedness boundary

`PanSemStateRelExecRanged` (`:94`) is the byte-range premise of the all-16
expression agreement.  This section records which production state updates
preserve it and, equally important, the precise boundary where it can fail.

The premise constrains only the three identifier-carrying components of the
production state: the stored local values, the stored global values, and the
structure context.  Consequently

* a local/global assignment whose new value is `PanValueByteRanged` preserves the
  premise, and by `evalPanValueExp_byteRanged` so does assigning the result of a
  byte-ranged expression evaluated under an already-ranged state;
* every update that leaves those three fields untouched (clock, FFI, memory,
  memory domains, code, exception shapes, base/top address, endianness)
  preserves the premise definitionally, and replacing `structs` by a
  `StructContextByteRanged` context does too;
* the premise is **not** implied by `PanSemStateRelExec`: the state relation maps
  production values through the total `panValueToHOL`, which encodes
  out-of-range identifiers through `ofString`, so a production local/global can
  hold a non-byte-ranged `nStruct` while the relation still holds.  The
  kernel-checked witness below (`nonByteRangedValue`, `not_ranged_of_local_nonRanged`)
  exhibits exactly that gap, and the registered regression
  `Flapjack.Test.PanSemStateBridgeParity` builds a state pair that is related by
  `PanSemStateRelExec` but fails `PanSemStateRelExecRanged`.

That gap is the reason the runtime FFI/global values need a separate range
obligation: parser origin constrains program syntax and identifier bytes but says
nothing about values returned by `extCall` or loaded from globals, so the byte
range cannot be discharged from the parser alone.  Everything here is untagged
Flapjack-specific bridge infrastructure; no `@[hol]` tag is attached. -/

/-- `PanValueByteRanged` is closed under `updatePanValueMap` with a byte-ranged
    value: the updated function is pointwise byte-ranged whenever the original
    is.  This is the value-map update class used by local/global assignment. -/
theorem updatePanValueMap_byteRanged {width : Nat} {γ : Type} [BEq γ]
    (values : γ → Option (PanValue (BitVec width)))
    (name : γ) (value : PanValue (BitVec width))
    (hvalues : ∀ key v, values key = some v → PanValueByteRanged v)
    (hvalue : PanValueByteRanged value) :
    ∀ key v, updatePanValueMap values name value key = some v → PanValueByteRanged v := by
  intro key v h
  unfold updatePanValueMap at h
  by_cases hc : key == name
  · rw [if_pos hc] at h
    rw [Option.some.injEq] at h
    exact h ▸ hvalue
  · rw [if_neg hc] at h
    exact hvalues key v h

/-- A local assignment of a byte-ranged value preserves
    `PanSemStateRelExecRanged`.  The assigned key need not be byte-ranged: the
    premise constrains the stored values, not the map keys. -/
theorem PanSemStateRelExecRanged.updateLocals {σ : Type}
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state) (name : VarName)
    (value : PanValue (RiscV.Word 64)) (hvalue : PanValueByteRanged value) :
    PanSemStateRelExecRanged
      { state with locals := updatePanValueMap state.locals name value } := by
  refine ⟨?_, h.2.1, h.2.2⟩
  intro key v hkey
  exact updatePanValueMap_byteRanged state.locals name value h.1 hvalue key v hkey

/-- A global assignment of a byte-ranged value preserves
    `PanSemStateRelExecRanged`. -/
theorem PanSemStateRelExecRanged.updateGlobals {σ : Type}
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state) (name : VarName)
    (value : PanValue (RiscV.Word 64)) (hvalue : PanValueByteRanged value) :
    PanSemStateRelExecRanged
      { state with globals := updatePanValueMap state.globals name value } := by
  refine ⟨h.1, ?_, h.2.2⟩
  intro key v hkey
  exact updatePanValueMap_byteRanged state.globals name value h.2.1 hvalue key v hkey

/-- Any production state update that leaves `locals`, `globals`, and `structs`
    unchanged preserves `PanSemStateRelExecRanged`. -/
theorem PanSemStateRelExecRanged.of_fields {σ : Type}
    {state other : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state)
    (hlocals : other.locals = state.locals) (hglobals : other.globals = state.globals)
    (hstructs : other.structs = state.structs) :
    PanSemStateRelExecRanged other := by
  refine ⟨?_, ?_, ?_⟩
  · intro name value hv
    rw [hlocals] at hv
    exact h.1 name value hv
  · intro name value hv
    rw [hglobals] at hv
    exact h.2.1 name value hv
  · rw [hstructs]
    exact h.2.2

/-- The clock update preserves `PanSemStateRelExecRanged`. -/
theorem PanSemStateRelExecRanged.setClock {σ : Type}
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state) (clock : Nat) :
    PanSemStateRelExecRanged { state with clock := clock } :=
  h.of_fields rfl rfl rfl

/-- The FFI update preserves `PanSemStateRelExecRanged` (the premise constrains no
    FFI field). -/
theorem PanSemStateRelExecRanged.setFfi {σ : Type}
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state) (ffi : FfiState σ) :
    PanSemStateRelExecRanged { state with ffi := ffi } :=
  h.of_fields rfl rfl rfl

/-- The memory update preserves `PanSemStateRelExecRanged` because the premise
    does not constrain the memory map. This does not establish rangedness of
    values read from memory. -/
theorem PanSemStateRelExecRanged.setMemory {σ : Type}
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state)
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64))) :
    PanSemStateRelExecRanged { state with memory := memory } :=
  h.of_fields rfl rfl rfl

/-- The `memaddrs` update preserves `PanSemStateRelExecRanged`. -/
theorem PanSemStateRelExecRanged.setMemaddrs {σ : Type}
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state) (memaddrs : RiscV.Word 64 → Bool) :
    PanSemStateRelExecRanged { state with memaddrs := memaddrs } :=
  h.of_fields rfl rfl rfl

/-- The `sharedMemaddrs` update preserves `PanSemStateRelExecRanged`. -/
theorem PanSemStateRelExecRanged.setSharedMemaddrs {σ : Type}
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state) (sharedMemaddrs : RiscV.Word 64 → Bool) :
    PanSemStateRelExecRanged { state with sharedMemaddrs := sharedMemaddrs } :=
  h.of_fields rfl rfl rfl

/-- The code-map update preserves `PanSemStateRelExecRanged`. -/
theorem PanSemStateRelExecRanged.setCode {σ : Type}
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state) (code : PanSemCodeMap (RiscV.Word 64)) :
    PanSemStateRelExecRanged { state with code := code } :=
  h.of_fields rfl rfl rfl

/-- The exception-shape update preserves `PanSemStateRelExecRanged`. -/
theorem PanSemStateRelExecRanged.setExceptionShapes {σ : Type}
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state)
    (exceptionShapes : ExceptionId → Option Shape) :
    PanSemStateRelExecRanged { state with exceptionShapes := exceptionShapes } :=
  h.of_fields rfl rfl rfl

/-- The base-address update preserves `PanSemStateRelExecRanged`. -/
theorem PanSemStateRelExecRanged.setBaseAddress {σ : Type}
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state) (baseAddress : RiscV.Word 64) :
    PanSemStateRelExecRanged { state with baseAddress := baseAddress } :=
  h.of_fields rfl rfl rfl

/-- The top-address update preserves `PanSemStateRelExecRanged`. -/
theorem PanSemStateRelExecRanged.setTopAddress {σ : Type}
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state) (topAddress : RiscV.Word 64) :
    PanSemStateRelExecRanged { state with topAddress := topAddress } :=
  h.of_fields rfl rfl rfl

/-- The endianness update preserves `PanSemStateRelExecRanged`. -/
theorem PanSemStateRelExecRanged.setBe {σ : Type}
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state) (be : Bool) :
    PanSemStateRelExecRanged { state with be := be } :=
  h.of_fields rfl rfl rfl

/-- Replacing the structure context by a byte-ranged context preserves
    `PanSemStateRelExecRanged`. -/
theorem PanSemStateRelExecRanged.setStructs {σ : Type}
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state) (structs : StructContext)
    (hstructs : StructContextByteRanged structs.toHOL) :
    PanSemStateRelExecRanged { state with structs := structs } := by
  refine ⟨h.1, h.2.1, ?_⟩
  exact hstructs

/-- The expression-driven local assignment class: assigning the byte-ranged result
    of a byte-ranged expression evaluated under a ranged state preserves
    `PanSemStateRelExecRanged`.  The value's rangedness is supplied by
    `evalPanValueExp_byteRanged`; no separate rangedness assumption on the value
    is needed. -/
theorem PanSemStateRelExecRanged.evalLocalUpdate {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hranged : PanSemStateRelExecRanged state)
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e)
    (name : VarName) (value : PanValue (RiscV.Word 64))
    (hvalue : evalPanValueExp state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress panSemBitVec64BytesInWord e
        (memoryAccess := some (panSemBitVec64MemoryAccess state)) = some value) :
    PanSemStateRelExecRanged
      { state with locals := updatePanValueMap state.locals name value } := by
  have hv := evalPanValueExp_byteRanged state hranged
    (some (panSemBitVec64MemoryAccess state)) e he value hvalue
  exact PanSemStateRelExecRanged.updateLocals hranged name value hv

/-- The expression-driven global assignment class, mirroring
    `PanSemStateRelExecRanged.evalLocalUpdate`. -/
theorem PanSemStateRelExecRanged.evalGlobalUpdate {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hranged : PanSemStateRelExecRanged state)
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e)
    (name : VarName) (value : PanValue (RiscV.Word 64))
    (hvalue : evalPanValueExp state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress panSemBitVec64BytesInWord e
        (memoryAccess := some (panSemBitVec64MemoryAccess state)) = some value) :
    PanSemStateRelExecRanged
      { state with globals := updatePanValueMap state.globals name value } := by
  have hv := evalPanValueExp_byteRanged state hranged
    (some (panSemBitVec64MemoryAccess state)) e he value hvalue
  exact PanSemStateRelExecRanged.updateGlobals hranged name value hv

/-! ### The boundary where rangedness can fail

A production value whose `nStruct` identifier has a character code at least 256
is not `PanValueByteRanged`, because it is not exactly representable as a HOL
`mlstring`.  Such a value can still sit in a production local or global, and the
executed state relation `PanSemStateRelExec` does not exclude it: `panValueToHOL`
totalizes the offending identifier through `ofString`.  This is the precise gap
the range premise must close; runtime FFI/global values are exactly where such a
value can enter. -/

/-- A concrete production value with an out-of-range identifier (`€`, code
    point 8364). -/
def nonByteRangedValue : PanValue (RiscV.Word 64) :=
  .nStruct "\u20ac" []

/-- The concrete out-of-range value is not `PanValueByteRanged`. -/
theorem nonByteRangedValue_not_ranged : ¬ PanValueByteRanged nonByteRangedValue := by
  intro h
  simp only [nonByteRangedValue, PanValueByteRanged, NameRanged, String.toList] at h
  exact absurd h.1 (by decide)

/-- A state whose local map holds a non-byte-ranged value fails
    `PanSemStateRelExecRanged`. -/
theorem not_ranged_of_local_nonRanged {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (name : VarName)
    (value : PanValue (RiscV.Word 64)) (h : state.locals name = some value)
    (hv : ¬ PanValueByteRanged value) : ¬ PanSemStateRelExecRanged state := by
  intro hr
  exact hv (hr.1 name value h)

/-- A state whose global map holds a non-byte-ranged value fails
    `PanSemStateRelExecRanged`. -/
theorem not_ranged_of_global_nonRanged {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (name : VarName)
    (value : PanValue (RiscV.Word 64)) (h : state.globals name = some value)
    (hv : ¬ PanValueByteRanged value) : ¬ PanSemStateRelExecRanged state := by
  intro hr
  exact hv (hr.2.1 name value h)

/-! ## Runtime FFI/primitive value-range boundary for `PanSemStateRelExecRanged`

`flapjack-pxn.18.4.3.77.2.15.1` recorded which identifier-preserving production
state updates preserve the byte-range premise `PanSemStateRelExecRanged` (`:94`),
and exhibited the `PanSemStateRelExec`/rangedness gap (`nonByteRangedValue`,
`not_ranged_of_local_nonRanged`, `not_ranged_of_global_nonRanged`).  The remaining
question is where a non-byte-ranged value can *enter* the executable state at
runtime, since parsing constrains neither FFI results nor primitive-handler
results.

This section resolves that boundary and narrows it precisely:

* the production `ExtCall` clause (`panSemTotalExtCallClause`) writes the FFI's
  returned *bytes* through `panSemTotalMachineWriteBytes` and installs the new
  `FfiState`; it never installs a `PanValue` into `locals` or `globals`.  Hence
  the value-map conjuncts of `PanSemStateRelExecRanged` are preserved
  **unconditionally** by the production `ExtCall` constructor: the FFI cannot
  introduce a non-byte-ranged local/global value at all.  The only
  identifier-carrying FFI payload is the event name, whose range obligation is
  the explicit runtime predicate `FfiResultByteRanged` below;
* the production `Primitive` clause (`panSemTotalPrimitiveClause`) *does* install
  the handler's `PanValue` result into `locals`, so its rangedness is conditional
  on the runtime predicate `PanPrimitiveHandlerByteRanged` (every value returned
  by the handler is `PanValueByteRanged`);
* a negative witness (`primitiveClause_not_ranged_of_nonRanged`) shows how an
  out-of-range primitive result crosses the boundary; a second witness
  (`extCallClause_not_ranged_of_global_nonRanged`) shows that `ExtCall` cannot
  repair a pre-existing out-of-range global.

The remaining runtime source outside these two clauses is the *initial* global
map (or any other direct global installation), which no evaluator clause
constrains; it is documented as the residual obligation rather than discharged
here.  Everything in this section is untagged Flapjack-specific bridge
infrastructure; no `@[hol]` tag is attached. -/

/-- Every production `UInt8` is `< 256`, so an FFI byte payload is always
    byte-ranged. -/
def BytesByteRanged (bytes : List UInt8) : Prop :=
  ∀ b ∈ bytes, b.toNat < 256

theorem bytesByteRanged (bytes : List UInt8) : BytesByteRanged bytes :=
  fun b _ => b.toNat_lt

/-- Explicit runtime FFI value-range predicate.  The production FFI returns only
    byte payloads (`List UInt8`, always `< 256`) plus one identifier-carrying
    event name; the host-state component is abstract (`σ`) and carries no
    `PanValue`.  So the predicate is exactly the byte-range obligation on the
    event name, reusing `FfiNameByteRanged` (`FfiBridge.lean:573`). -/
def FfiResultByteRanged {σ : Type} : FfiResult σ → Prop
  | .returned _ bytes => BytesByteRanged bytes
  | .final event => FfiNameByteRanged event.name

/-- A returned FFI result is always byte-ranged: its payload is `UInt8`. -/
theorem ffiResultByteRanged_returned {σ : Type} (state : FfiState σ) (bytes : List UInt8) :
    FfiResultByteRanged (.returned state bytes) :=
  bytesByteRanged bytes

/-- A final FFI result is byte-ranged exactly when its event name is. -/
theorem ffiResultByteRanged_final_iff (σ : Type) (event : FfiFinalEvent) :
    FfiResultByteRanged (σ := σ) (.final event) ↔ FfiNameByteRanged event.name :=
  Iff.rfl

/-- The FFI's observable payload is byte-ranged on the successful-return path
    regardless of the call name; only the `.final` event name carries an
    identifier whose range is not automatic. -/
theorem ffiResultByteRanged_of_callFfi_returned {σ : Type} (state : FfiState σ)
    (name : FfiName) (configuration bytes : List UInt8) (nextFfi : FfiState σ)
    (nextBytes : List UInt8)
    (_h : callFfi state name configuration bytes = .returned nextFfi nextBytes) :
    FfiResultByteRanged (.returned nextFfi nextBytes) :=
  bytesByteRanged nextBytes

/-- Runtime predicate on a primitive handler: every value it returns is
    byte-ranged.  Unlike the FFI, the production `Primitive` clause installs this
    value directly into `locals`, so this is the exact premise needed to preserve
    `PanSemStateRelExecRanged` across the constructor. -/
def PanPrimitiveHandlerByteRanged (primitive : PanPrimitiveHandler (RiscV.Word 64)) : Prop :=
  ∀ (operator : PrimOp) (values : List (PanValue (RiscV.Word 64)))
    (value : PanValue (RiscV.Word 64)),
    primitive operator values = some value → PanValueByteRanged value

/-- `panEmptyLocals` preserves `PanSemStateRelExecRanged`: only the local map is
    replaced, by the everywhere-`none` map. -/
theorem PanSemStateRelExecRanged.panEmptyLocals {σ : Type}
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state) :
    PanSemStateRelExecRanged (Flapjack.panEmptyLocals state) := by
  refine ⟨?_, h.2.1, h.2.2⟩
  intro name value hv
  rw [show (Flapjack.panEmptyLocals state).locals name = none from rfl] at hv
  exact absurd hv (by simp)

/-- `panSemTotalMachineWriteBytes` changes only the memory map, so it preserves
    `PanSemStateRelExecRanged` definitionally. -/
theorem PanSemStateRelExecRanged.machineWriteBytes {σ : Type}
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state) (address : RiscV.Word 64) (bytes : List UInt8) :
    PanSemStateRelExecRanged (panSemTotalMachineWriteBytes state address bytes) :=
  h.of_fields rfl rfl rfl

/-- A single evaluated-expression step preserves `PanSemStateRelExecRanged` when
    the continuation does.  On evaluation failure the step returns the entry
    state unchanged. -/
theorem PanSemStateRelExecRanged.exprStep {σ : Type}
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state) (expression : Exp (RiscV.Word 64))
    (onValue : PanValue (RiscV.Word 64) →
      Option (PanSemHOLResult (RiscV.Word 64)) ×
        PanSemState (RiscV.Word 64) (FfiState σ))
    (honValue : ∀ value, PanSemStateRelExecRanged (onValue value).2) :
    PanSemStateRelExecRanged (panSemTotalExprStep state expression onValue).2 := by
  unfold panSemTotalExprStep
  split
  · exact honValue _
  · exact h

/-- A single evaluated-expression-list step preserves `PanSemStateRelExecRanged`
    when the continuation does. -/
theorem PanSemStateRelExecRanged.exprListStep {σ : Type}
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state) (expressions : List (Exp (RiscV.Word 64)))
    (onValues : List (PanValue (RiscV.Word 64)) →
      Option (PanSemHOLResult (RiscV.Word 64)) ×
        PanSemState (RiscV.Word 64) (FfiState σ))
    (honValues : ∀ values, PanSemStateRelExecRanged (onValues values).2) :
    PanSemStateRelExecRanged (panSemTotalExprListStep state expressions onValues).2 := by
  unfold panSemTotalExprListStep
  split
  · exact honValues _
  · exact h

/-- The production `ExtCall` composition step preserves `PanSemStateRelExecRanged`
    unconditionally.  Its value-map conjuncts are untouched: the final-event
    branch clears only `locals`, and the returned branch rewrites only `memory`
    and `ffi`.  The FFI's returned bytes are always byte-ranged and no `PanValue`
    is installed, so no FFI range premise is needed. -/
theorem PanSemStateRelExecRanged.extCallStep {σ : Type}
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state)
    (evaluatedPtr1 evaluatedLen1 evaluatedPtr2 evaluatedLen2 : Option (PanValue (RiscV.Word 64)))
    (function : FunName) :
    PanSemStateRelExecRanged
      (panSemTotalExtCallStep state evaluatedPtr1 evaluatedLen1 evaluatedPtr2 evaluatedLen2
        (panSemTotalMachineReadBytes state)
        (fun ffi name configurationBytes arrayBytes => callFfi ffi name configurationBytes arrayBytes)
        (panSemTotalMachineWriteBytes) function).2 := by
  unfold panSemTotalExtCallStep
  split
  · split
    · split
      · exact h.panEmptyLocals
      · refine h.of_fields ?_ ?_ ?_ <;> simp [panSemTotalMachineWriteBytes]
    · exact h
  · exact h

/-- The production `ExtCall` clause preserves `PanSemStateRelExecRanged`
    unconditionally: the four argument evaluations leave the value maps and
    structure context untouched, and the FFI step only writes memory / installs
    the new `FfiState`. -/
theorem PanSemStateRelExecRanged.extCallClause {σ : Type}
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state) (function : FunName)
    (configuration configurationLength array arrayLength : Exp (RiscV.Word 64)) :
    PanSemStateRelExecRanged
      (panSemTotalExtCallClause state function configuration configurationLength
        array arrayLength).2 := by
  unfold panSemTotalExtCallClause
  apply PanSemStateRelExecRanged.exprStep h
  intro configurationValue
  apply PanSemStateRelExecRanged.exprStep h
  intro configurationLengthValue
  apply PanSemStateRelExecRanged.exprStep h
  intro arrayValue
  apply PanSemStateRelExecRanged.exprStep h
  intro arrayLengthValue
  exact PanSemStateRelExecRanged.extCallStep h _ _ _ _ function

/-- The production `Primitive` clause preserves `PanSemStateRelExecRanged`
    provided the runtime predicate `PanPrimitiveHandlerByteRanged` holds: only the
    successful, valid-assignment branch installs the handler's value into
    `locals`, by `PanSemStateRelExecRanged.updateLocals`. -/
theorem PanSemStateRelExecRanged.primitiveClause {σ : Type}
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state) (name : VarName) (operator : PrimOp)
    (arguments : List (Exp (RiscV.Word 64))) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (hprim : PanPrimitiveHandlerByteRanged primitive) :
    PanSemStateRelExecRanged
      (panSemTotalPrimitiveClause state name operator arguments primitive).2 := by
  unfold panSemTotalPrimitiveClause
  apply PanSemStateRelExecRanged.exprListStep h
  intro values
  split
  · rename_i value hvalue
    split
    · rename_i hvalid
      exact h.updateLocals name value (hprim operator values value hvalue)
    · exact h
  · exact h

/-- **Negative witness (primitive boundary).** If the primitive handler returns a
    non-byte-ranged value on a successful, valid-assignment path, the resulting
    state fails `PanSemStateRelExecRanged`.  This is the exact runtime boundary
    where the premise can be crossed. -/
theorem primitiveClause_not_ranged_of_nonRanged {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (name : VarName) (operator : PrimOp)
    (arguments : List (Exp (RiscV.Word 64))) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (values : List (PanValue (RiscV.Word 64))) (value : PanValue (RiscV.Word 64))
    (heval : evalPanSemStateExps state arguments = some values)
    (hprim : primitive operator values = some value)
    (hvalid : panValueAssignmentValid state.structs state.locals state.globals
      .local name value = true)
    (hv : ¬ PanValueByteRanged value) :
    ¬ PanSemStateRelExecRanged
        (panSemTotalPrimitiveClause state name operator arguments primitive).2 := by
  rw [panSemTotalPrimitiveClause_ok state name operator arguments primitive values value
    heval hprim hvalid]
  exact not_ranged_of_local_nonRanged
    { state with locals := updatePanValueMap state.locals name value } name value
    (by simp [updatePanValueMap]) hv

/-- The production `ExtCall` clause never changes the global map: it only clears
    `locals` (final event) or rewrites `memory`/`ffi` (returned). -/
theorem panSemTotalExtCallClause_globals {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (function : FunName)
    (configuration configurationLength array arrayLength : Exp (RiscV.Word 64)) :
    (panSemTotalExtCallClause state function configuration configurationLength
        array arrayLength).2.globals = state.globals := by
  simp only [panSemTotalExtCallClause, panSemTotalExprStep, panSemTotalExtCallStep,
    panSemTotalMachineReadBytes, panSemTotalMachineWriteBytes, panEmptyLocals]
  repeat' (first | rfl | split)

/-- **Negative witness (residual global boundary).** `ExtCall` does not repair a
    pre-existing non-byte-ranged global: the production clause leaves `globals`
    unchanged, so if the entry state already holds an out-of-range global (the
    initial/stored-global boundary) the resulting state still fails
    `PanSemStateRelExecRanged`. -/
theorem extCallClause_not_ranged_of_global_nonRanged {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (function : FunName)
    (configuration configurationLength array arrayLength : Exp (RiscV.Word 64))
    (name : VarName) (value : PanValue (RiscV.Word 64))
    (h : state.globals name = some value) (hv : ¬ PanValueByteRanged value) :
    ¬ PanSemStateRelExecRanged
        (panSemTotalExtCallClause state function configuration configurationLength
          array arrayLength).2 := by
  intro hr
  exact not_ranged_of_global_nonRanged
    (panSemTotalExtCallClause state function configuration configurationLength
      array arrayLength).2 name value
    (by rw [panSemTotalExtCallClause_globals]; exact h) hv hr

/-! ## Exception-shape rangedness: frame and preservation

`PanSemStateRelExec` compares exception shapes only through the lossy
`shapeToHOL`, so the production/exact `Raise` agreement
(`panSemTotalEvaluate_raise_agree`) needs the intrinsic premise
`PanSemExceptionShapesRanged` (`:116`).  This section discharges that premise:
every state-update helper of the total evaluator leaves `exceptionShapes`
unchanged, and the total evaluator's `exceptionShapes` frame lemma below makes
the predicate invariant under all reachable production execution.  The
initial-state obligation is covered by the `panPropsALookupEq` / declaration
`exceptionEntries` rangedness lemmas.  Everything here is untagged
Flapjack-specific bridge infrastructure; no `@[hol]` tag is attached. -/

/-- The clock-leaf clauses leave `exceptionShapes` unchanged. -/
theorem panSemEvaluateClockLeaf_exceptionShapes
    (leaf : PanSemClockLeaf) (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    (panSemEvaluateClockLeaf leaf state).2.exceptionShapes = state.exceptionShapes := by
  cases leaf <;> simp only [panSemEvaluateClockLeaf] <;> repeat' (first | rfl | split)

/-- The `Assign` clause leaves `exceptionShapes` unchanged. -/
theorem panSemTotalAssignClause_exceptionShapes
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (kind : VarKind) (name : VarName) (value : Exp (RiscV.Word 64)) :
    (panSemTotalAssignClause state kind name value).2.exceptionShapes = state.exceptionShapes := by
  simp only [panSemTotalAssignClause, panSemTotalExprStep]
  repeat' (first | rfl | split)

/-- The `Raise` clause leaves `exceptionShapes` unchanged (it only reads them). -/
theorem panSemTotalRaiseClause_exceptionShapes
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exceptionId : ExceptionId) (expression : Exp (RiscV.Word 64)) :
    (panSemTotalRaiseClause state exceptionId expression).2.exceptionShapes = state.exceptionShapes := by
  simp only [panSemTotalRaiseClause, panSemTotalExprStep, panEmptyLocals]
  repeat' (first | rfl | split)

/-- The `Return` clause leaves `exceptionShapes` unchanged. -/
theorem panSemTotalReturnClause_exceptionShapes
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (expression : Exp (RiscV.Word 64)) :
    (panSemTotalReturnClause state expression).2.exceptionShapes = state.exceptionShapes := by
  simp only [panSemTotalReturnClause, panSemTotalExprStep, panEmptyLocals]
  repeat' (first | rfl | split)

/-- The `Primitive` clause leaves `exceptionShapes` unchanged. -/
theorem panSemTotalPrimitiveClause_exceptionShapes
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (name : VarName) (operator : PrimOp) (arguments : List (Exp (RiscV.Word 64)))
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) :
    (panSemTotalPrimitiveClause state name operator arguments primitive).2.exceptionShapes = state.exceptionShapes := by
  simp only [panSemTotalPrimitiveClause, panSemTotalExprListStep]
  repeat' (first | rfl | split)

/-- The `Store` clause leaves `exceptionShapes` unchanged. -/
theorem panSemTotalStoreClause_exceptionShapes
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) :
    (panSemTotalStoreClause state address value).2.exceptionShapes = state.exceptionShapes := by
  simp only [panSemTotalStoreClause, panSemTotalExprStep]
  repeat' (first | rfl | split)

/-- The `Store32` clause leaves `exceptionShapes` unchanged. -/
theorem panSemTotalStore32Clause_exceptionShapes
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) :
    (panSemTotalStore32Clause state address value).2.exceptionShapes = state.exceptionShapes := by
  simp only [panSemTotalStore32Clause, panSemTotalExprStep]
  repeat' (first | rfl | split)

/-- The `StoreByte` clause leaves `exceptionShapes` unchanged. -/
theorem panSemTotalStoreByteClause_exceptionShapes
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) :
    (panSemTotalStoreByteClause state address value).2.exceptionShapes = state.exceptionShapes := by
  simp only [panSemTotalStoreByteClause, panSemTotalExprStep]
  repeat' (first | rfl | split)

/-- The `ExtCall` clause leaves `exceptionShapes` unchanged. -/
theorem panSemTotalExtCallClause_exceptionShapes
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (function : FunName) (configuration configurationLength array arrayLength : Exp (RiscV.Word 64)) :
    (panSemTotalExtCallClause state function configuration configurationLength array arrayLength).2.exceptionShapes = state.exceptionShapes := by
  simp only [panSemTotalExtCallClause, panSemTotalExprStep, panSemTotalExtCallStep,
    panSemTotalMachineReadBytes, panSemTotalMachineWriteBytes, panEmptyLocals]
  repeat' (first | rfl | split)

/-- The `ShMemLoad` clause leaves `exceptionShapes` unchanged. -/
theorem panSemTotalShMemLoadClause_exceptionShapes
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (size : OpSize) (kind : VarKind) (name : VarName) (address : Exp (RiscV.Word 64)) :
    (panSemTotalShMemLoadClause state size kind name address).2.exceptionShapes = state.exceptionShapes := by
  simp only [panSemTotalShMemLoadClause, panSemTotalExprStep, panSemTotalShMemState,
    panSemTotalShMemStateBack, panSemTotalShMemLoadResult]
  repeat' (first | rfl | split)

/-- The `ShMemStore` clause leaves `exceptionShapes` unchanged. -/
theorem panSemTotalShMemStoreClause_exceptionShapes
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (size : OpSize) (address value : Exp (RiscV.Word 64)) :
    (panSemTotalShMemStoreClause state size address value).2.exceptionShapes = state.exceptionShapes := by
  simp only [panSemTotalShMemStoreClause, panSemTotalExprStep, panSemTotalShMemState,
    panSemTotalShMemStateBack, panSemTotalShMemStoreResult]
  repeat' (first | rfl | split)

theorem panSemTotalDecBind_exceptionShapes [BEq String]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (name : VarName) (value : PanValue (RiscV.Word 64)) :
    (panSemTotalDecBind state name value).exceptionShapes = state.exceptionShapes := by
  simp [panSemTotalDecBind]

theorem panSemFixClock_exceptionShapes (entryClock : Nat)
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    (panSemFixClock entryClock state).exceptionShapes = state.exceptionShapes := rfl

/-- `panEmptyLocals` only clears locals, so it leaves `exceptionShapes` unchanged. -/
theorem panEmptyLocals_exceptionShapes
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    (panEmptyLocals state).exceptionShapes = state.exceptionShapes := rfl

/-- **Frame lemma.** The production total evaluator never writes
    `exceptionShapes`: its result state stores exactly the entry state's
    exception map.  Proved by well-founded induction over `panSemEvalMeasure`,
    using the per-clause frame lemmas above for the non-recursive clauses and
    the induction hypothesis for the recursive `Dec`/`Seq`/`If`/`While`/`Call`/
    `DecCall` clauses. -/
theorem panSemTotalEvaluate_exceptionShapes {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) :
    ∀ (prog : Prog (RiscV.Word 64)) (state : PanSemState (RiscV.Word 64) (FfiState σ)),
      (panSemTotalEvaluate primitive prog state).2.exceptionShapes = state.exceptionShapes := by
  intro prog state
  have hwf : WellFounded (@panSemEvalMeasureRel (RiscV.Word 64) (FfiState σ)) :=
    panSemEvalMeasureRel_wf
  let motive : PanSemState (RiscV.Word 64) (FfiState σ) × Prog (RiscV.Word 64) → Prop :=
    fun p => (panSemTotalEvaluate primitive p.2 p.1).2.exceptionShapes = p.1.exceptionShapes
  have hmain : ∀ p, motive p := by
    intro p
    refine WellFounded.induction hwf p ?_
    intro p ih
    obtain ⟨state, prog⟩ := p
    change (panSemTotalEvaluate primitive prog state).2.exceptionShapes = state.exceptionShapes
    cases prog with
    | skip => rw [panSemTotalEvaluate]; exact panSemEvaluateClockLeaf_exceptionShapes .skip state
    | «break» => rw [panSemTotalEvaluate]; exact panSemEvaluateClockLeaf_exceptionShapes .break state
    | «continue» => rw [panSemTotalEvaluate]; exact panSemEvaluateClockLeaf_exceptionShapes .continue state
    | tick => rw [panSemTotalEvaluate]; exact panSemEvaluateClockLeaf_exceptionShapes .tick state
    | assign kind name value => rw [panSemTotalEvaluate]; exact panSemTotalAssignClause_exceptionShapes state kind name value
    | primitive name operator arguments => rw [panSemTotalEvaluate]; exact panSemTotalPrimitiveClause_exceptionShapes state name operator arguments primitive
    | store address value => rw [panSemTotalEvaluate]; exact panSemTotalStoreClause_exceptionShapes state address value
    | store32 address value => rw [panSemTotalEvaluate]; exact panSemTotalStore32Clause_exceptionShapes state address value
    | storeByte address value => rw [panSemTotalEvaluate]; exact panSemTotalStoreByteClause_exceptionShapes state address value
    | raise exceptionId expression => rw [panSemTotalEvaluate]; exact panSemTotalRaiseClause_exceptionShapes state exceptionId expression
    | «return» expression => rw [panSemTotalEvaluate]; exact panSemTotalReturnClause_exceptionShapes state expression
    | annot tag text => rw [panSemTotalEvaluate]
    | dec name shape value body =>
        rw [panSemTotalEvaluate]
        try dsimp only
        cases heval : evalPanSemStateExp state value with
        | none => rfl
        | some evaluated =>
            simp only []
            cases hmatch : panShapeMatches shape (panSemShapeOf evaluated) with
            | false => rfl
            | true =>
                simp only [if_true]
                try dsimp only
                rw [ih (panSemTotalDecBind state name evaluated, body)
                  (panSemEvalMeasureRel_decBody state name shape value body)]
                rw [panSemTotalDecBind_exceptionShapes]
    | seq first second =>
        rw [panSemTotalEvaluate]
        try dsimp only
        cases hres : (panSemTotalEvaluate primitive first state).1 with
        | none =>
            have ih1 := ih (state, first)
              (panSemEvalMeasureRel_seq_branch state state first second first (Nat.le_refl _) (Or.inl rfl))
            have hclk : (panSemFixClock state.clock (panSemTotalEvaluate primitive first state).2).clock ≤ state.clock :=
              panSemFixClock_clock_le _ _
            have ih2 := ih (panSemFixClock state.clock (panSemTotalEvaluate primitive first state).2, second)
              (panSemEvalMeasureRel_seq_branch _ state first second second hclk (Or.inr rfl))
            rw [ih2, panSemFixClock_exceptionShapes, ih1]
        | some result =>
            have ih1 := ih (state, first)
              (panSemEvalMeasureRel_seq_branch state state first second first (Nat.le_refl _) (Or.inl rfl))
            rw [panSemFixClock_exceptionShapes, ih1]
    | ite condition thenBranch elseBranch =>
        rw [panSemTotalEvaluate]
        try dsimp only
        cases hcond : evalPanSemStateExp state condition with
        | none => rfl
        | some v =>
            cases v with
            | word w =>
                try dsimp only
                split
                · exact ih (state, elseBranch)
                    (panSemEvalMeasureRel_ite_branch state condition thenBranch elseBranch elseBranch (Or.inr rfl))
                · exact ih (state, thenBranch)
                    (panSemEvalMeasureRel_ite_branch state condition thenBranch elseBranch thenBranch (Or.inl rfl))
            | rStruct fs => rfl
            | nStruct nm flds => rfl
    | «while» condition body =>
        rw [panSemTotalEvaluate]
        try dsimp only
        cases hcond : evalPanSemStateExp state condition with
        | none => rfl
        | some v =>
            cases v with
            | word w =>
                try dsimp only
                split
                · rfl
                · split
                  · exact panEmptyLocals_exceptionShapes state
                  · rename_i hw hclk
                    try dsimp only
                    have hdecClock : state.clock - 1 < state.clock := by omega
                    have ihBody := ih ({ state with clock := state.clock - 1 }, body)
                      (panSemEvalMeasureRel_of_clock_lt hdecClock)
                    have hfixLt : (panSemFixClock (state.clock - 1)
                        (panSemTotalEvaluate primitive body { state with clock := state.clock - 1 }).2).clock < state.clock := by
                      have := panSemFixClock_clock_le (state.clock - 1)
                        (panSemTotalEvaluate primitive body { state with clock := state.clock - 1 }).2
                      omega
                    have ihLoop := ih ((panSemFixClock (state.clock - 1)
                        (panSemTotalEvaluate primitive body { state with clock := state.clock - 1 }).2),
                        .while condition body)
                      (panSemEvalMeasureRel_of_clock_lt hfixLt)
                    cases hbody : (panSemTotalEvaluate primitive body { state with clock := state.clock - 1 }).1 with
                    | none => rw [ihLoop, panSemFixClock_exceptionShapes, ihBody]
                    | some r =>
                        cases r with
                        | «continue» => rw [ihLoop, panSemFixClock_exceptionShapes, ihBody]
                        | «break» => rw [panSemFixClock_exceptionShapes, ihBody]
                        | error => rw [panSemFixClock_exceptionShapes, ihBody]
                        | timeOut => rw [panSemFixClock_exceptionShapes, ihBody]
                        | returned val => rw [panSemFixClock_exceptionShapes, ihBody]
                        | exception eid val => rw [panSemFixClock_exceptionShapes, ihBody]
                        | finalFfi ev => rw [panSemFixClock_exceptionShapes, ihBody]
            | rStruct fs => rfl
            | nStruct nm flds => rfl
    | call info function arguments =>
        rw [panSemTotalEvaluate]
        try dsimp only
        cases hexps : evalPanSemStateExps state arguments with
        | none => rfl
        | some values =>
            simp only []
            cases hlookup : panSemTotalCodeLookup state function values with
            | none => rfl
            | some triple =>
                obtain ⟨callee, newLocals, returnShape⟩ := triple
                simp only []
                split
                · exact panEmptyLocals_exceptionShapes state
                · rename_i hclk
                  have hdecClock : state.clock - 1 < state.clock := by omega
                  have ihBody := ih ({ state with clock := state.clock - 1, locals := newLocals }, callee)
                    (panSemEvalMeasureRel_of_clock_lt hdecClock)
                  have hbodyExc : (panSemTotalEvaluate primitive callee
                      ({ state with clock := state.clock - 1, locals := newLocals })).2.exceptionShapes =
                      state.exceptionShapes := by
                    rw [ihBody]
                  have hfixedExc : (panSemFixClock (state.clock - 1)
                      (panSemTotalEvaluate primitive callee
                        ({ state with clock := state.clock - 1, locals := newLocals })).2).exceptionShapes =
                      state.exceptionShapes := by
                    rw [panSemFixClock_exceptionShapes, hbodyExc]
                  have hfixedClock : (panSemFixClock (state.clock - 1)
                      (panSemTotalEvaluate primitive callee
                        ({ state with clock := state.clock - 1, locals := newLocals })).2).clock <
                      state.clock := by
                    have hle := panSemFixClock_clock_le (state.clock - 1)
                      (panSemTotalEvaluate primitive callee
                        ({ state with clock := state.clock - 1, locals := newLocals })).2
                    omega
                  cases hcall : (panSemTotalEvaluate primitive callee
                      ({ state with clock := state.clock - 1, locals := newLocals })).1 with
                  | none => try dsimp only; exact hfixedExc
                  | some r =>
                      cases r with
                      | error => try dsimp only; rw [panEmptyLocals_exceptionShapes]; exact hfixedExc
                      | timeOut => try dsimp only; rw [panEmptyLocals_exceptionShapes]; exact hfixedExc
                      | finalFfi ev => try dsimp only; rw [panEmptyLocals_exceptionShapes]; exact hfixedExc
                      | «break» => try dsimp only; exact hfixedExc
                      | «continue» => try dsimp only; exact hfixedExc
                      | returned value =>
                          try dsimp only
                          split
                          · try dsimp only
                            split
                            · rw [panEmptyLocals_exceptionShapes]; exact hfixedExc
                            · try dsimp only; exact hfixedExc
                            · try dsimp only
                              split
                              · split
                                · try dsimp only; exact hfixedExc
                                · try dsimp only; exact hfixedExc
                              · try dsimp only; exact hfixedExc
                          · try dsimp only; exact hfixedExc
                      | exception exceptionId value =>
                          try dsimp only
                          split
                          · rw [panEmptyLocals_exceptionShapes]; exact hfixedExc
                          · try dsimp only; exact hfixedExc
                          · try dsimp only
                            rename_i handlerId handlerVar handlerProg
                            split
                            · split
                              · split
                                · try dsimp only
                                  have ihHandler := ih
                                    ({ panSemFixClock (state.clock - 1)
                                        (panSemTotalEvaluate primitive callee
                                          ({ state with clock := state.clock - 1, locals := newLocals })).2 with
                                      locals := updatePanValueMap state.locals handlerVar value }, handlerProg)
                                    (panSemEvalMeasureRel_of_clock_lt (by
                                      have hle := panSemFixClock_clock_le (state.clock - 1)
                                        (panSemTotalEvaluate primitive callee
                                          ({ state with clock := state.clock - 1, locals := newLocals })).2
                                      omega))
                                  rw [ihHandler, hfixedExc]
                                · try dsimp only; exact hfixedExc
                              · try dsimp only; exact hfixedExc
                            · rw [panEmptyLocals_exceptionShapes]; exact hfixedExc
    | decCall name shape function arguments continuation =>
        rw [panSemTotalEvaluate]
        try dsimp only
        cases hexps : evalPanSemStateExps state arguments with
        | none => rfl
        | some values =>
            simp only []
            cases hlookup : panSemTotalCodeLookup state function values with
            | none => rfl
            | some triple =>
                obtain ⟨callee, newLocals, returnShape⟩ := triple
                simp only []
                split
                · exact panEmptyLocals_exceptionShapes state
                · rename_i hclk
                  have hdecClock : state.clock - 1 < state.clock := by omega
                  have ihBody := ih ({ state with clock := state.clock - 1, locals := newLocals }, callee)
                    (panSemEvalMeasureRel_of_clock_lt hdecClock)
                  have hbodyExc : (panSemTotalEvaluate primitive callee
                      ({ state with clock := state.clock - 1, locals := newLocals })).2.exceptionShapes =
                      state.exceptionShapes := by
                    rw [ihBody]
                  have hfixedExc : (panSemFixClock (state.clock - 1)
                      (panSemTotalEvaluate primitive callee
                        ({ state with clock := state.clock - 1, locals := newLocals })).2).exceptionShapes =
                      state.exceptionShapes := by
                    rw [panSemFixClock_exceptionShapes, hbodyExc]
                  have hfixedClock : (panSemFixClock (state.clock - 1)
                      (panSemTotalEvaluate primitive callee
                        ({ state with clock := state.clock - 1, locals := newLocals })).2).clock <
                      state.clock := by
                    have hle := panSemFixClock_clock_le (state.clock - 1)
                      (panSemTotalEvaluate primitive callee
                        ({ state with clock := state.clock - 1, locals := newLocals })).2
                    omega
                  cases hcall : (panSemTotalEvaluate primitive callee
                      ({ state with clock := state.clock - 1, locals := newLocals })).1 with
                  | none => try dsimp only; exact hfixedExc
                  | some r =>
                      cases r with
                      | error => try dsimp only; rw [panEmptyLocals_exceptionShapes]; exact hfixedExc
                      | timeOut => try dsimp only; rw [panEmptyLocals_exceptionShapes]; exact hfixedExc
                      | finalFfi ev => try dsimp only; rw [panEmptyLocals_exceptionShapes]; exact hfixedExc
                      | «break» => try dsimp only; exact hfixedExc
                      | «continue» => try dsimp only; exact hfixedExc
                      | returned value =>
                          try dsimp only
                          split
                          · try dsimp only
                            have ihCont := ih
                              ({ panSemFixClock (state.clock - 1)
                                  (panSemTotalEvaluate primitive callee
                                    ({ state with clock := state.clock - 1, locals := newLocals })).2 with
                                locals := updatePanValueMap state.locals name value }, continuation)
                              (panSemEvalMeasureRel_of_clock_lt (by
                                have hle := panSemFixClock_clock_le (state.clock - 1)
                                  (panSemTotalEvaluate primitive callee
                                    ({ state with clock := state.clock - 1, locals := newLocals })).2
                                omega))
                            have hcontExc : (panSemTotalEvaluate primitive continuation
                                ({ panSemFixClock (state.clock - 1)
                                    (panSemTotalEvaluate primitive callee
                                      ({ state with clock := state.clock - 1, locals := newLocals })).2 with
                                  locals := updatePanValueMap state.locals name value })).2.exceptionShapes =
                                state.exceptionShapes := by
                              rw [ihCont]
                              exact hfixedExc
                            try dsimp only
                            rw [hcontExc]
                          · try dsimp only; exact hfixedExc
                      | exception eid val =>
                          try dsimp only; rw [panEmptyLocals_exceptionShapes]; exact hfixedExc
    | extCall function configuration configurationLength array arrayLength =>
        rw [panSemTotalEvaluate]
        exact panSemTotalExtCallClause_exceptionShapes state function configuration configurationLength array arrayLength
    | shMemLoad size kind name address =>
        rw [panSemTotalEvaluate]
        exact panSemTotalShMemLoadClause_exceptionShapes state size kind name address
    | shMemStore size address value =>
        rw [panSemTotalEvaluate]
        exact panSemTotalShMemStoreClause_exceptionShapes state size address value
  exact hmain (state, prog)

/-- The declaration-derived exception table (`exceptionEntries`, HOL
    `panLang$exceptions`) stores only byte-ranged shapes when every declaration
    is `DeclByteRanged`; an `exnDecl` contributes its `ShapeByteRanged` conjunct. -/
theorem exceptionEntries_shapeByteRanged {width : Nat}
    (declarations : List (Decl (BitVec width)))
    (hranged : ∀ d ∈ declarations, DeclByteRanged d) :
    ∀ p ∈ exceptionEntries declarations, ShapeByteRanged p.2 := by
  induction declarations with
  | nil => intro p hp; simp [exceptionEntries] at hp
  | cons declaration declarations ih =>
      cases declaration with
      | function fd =>
          simp only [exceptionEntries]
          exact ih (fun d hd => hranged d (by simp [hd]))
      | decl shp name value =>
          simp only [exceptionEntries]
          exact ih (fun d hd => hranged d (by simp [hd]))
      | exnDecl eid shp =>
          simp only [exceptionEntries]
          intro p hp
          rcases List.mem_cons.mp hp with hhead | htail
          · subst hhead
            exact (hranged (.exnDecl eid shp) (by simp)).2
          · exact ih (fun d hd => hranged d (by simp [hd])) p htail
      | name struct fields =>
          simp only [exceptionEntries]
          exact ih (fun d hd => hranged d (by simp [hd]))

/-- A production state whose `exceptionShapes` is the equality-based `panPropsALookupEq`
    of a byte-ranged association list satisfies `PanSemExceptionShapesRanged`:
    the lookup returns only values stored in the list. -/
theorem panSemExceptionShapesRanged_of_ALookupEq [DecidableEq String]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (entries : List (String × Shape))
    (hranged : ∀ entry ∈ entries, ShapeByteRanged entry.2) :
    PanSemExceptionShapesRanged
      { state with exceptionShapes := fun name => panPropsALookupEq name entries } := by
  intro exceptionId shape hlookup
  induction entries with
  | nil => simp [panPropsALookupEq] at hlookup
  | cons entry entries ih =>
      rcases entry with ⟨candidate, value⟩
      by_cases hc : candidate = exceptionId
      · subst hc
        simp only [panPropsALookupEq, decide_true, if_true] at hlookup
        rw [Option.some.injEq] at hlookup
        subst hlookup
        exact hranged (candidate, value) (by simp)
      · simp only [panPropsALookupEq, decide_eq_false_iff_not.mpr hc] at hlookup
        exact ih (fun e he => hranged e (by simp [he])) hlookup

/-- Variant of `panSemExceptionShapesRanged_of_ALookupEq` for an association list whose
    values are transformed by a `ShapeByteRanged`-preserving `convert` (the
    `structCompileShape` shape of the `pan_structs` pass). -/
theorem panSemExceptionShapesRanged_of_ALookupEq_map [DecidableEq String]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (entries : List (String × Shape)) (convert : Shape → Shape)
    (hconvert : ∀ shape, ShapeByteRanged shape → ShapeByteRanged (convert shape))
    (hranged : ∀ entry ∈ entries, ShapeByteRanged entry.2) :
    PanSemExceptionShapesRanged
      { state with exceptionShapes := fun name =>
          panPropsALookupEq name (entries.map fun p => (p.1, convert p.2)) } := by
  apply panSemExceptionShapesRanged_of_ALookupEq state
    (entries.map fun p => (p.1, convert p.2))
  intro entry hentry
  rcases List.mem_map.mp hentry with ⟨original, horiginal, rfl⟩
  exact hconvert original.2 (hranged original horiginal)

/-- `PanSemExceptionShapesRanged` is preserved by the `pan_structs` pass, which maps
    each stored shape through `structCompileShape context`: the existing
    `structCompileShape_byteRanged` carries byte-rangedness across the rewrite. -/
theorem PanSemExceptionShapesRanged.map_structCompileShape
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemExceptionShapesRanged state) (context : StructContext)
    (hc : CtxBR context) :
    PanSemExceptionShapesRanged
      { state with exceptionShapes := fun name =>
          Option.map (structCompileShape context) (state.exceptionShapes name) } := by
  intro exceptionId shape hlookup
  cases hstate : state.exceptionShapes exceptionId with
  | none => simp only [hstate, Option.map_none] at hlookup; exact absurd hlookup (by simp)
  | some stored =>
      simp only [hstate, Option.map_some] at hlookup
      rw [Option.some.injEq] at hlookup
      rw [← hlookup]
      exact structCompileShape_byteRanged context stored hc (h exceptionId stored hstate)

/-- The compiled initial exception map (a total `panPropsALookupEq` lookup of
    `exceptionEntries declarations`) satisfies `PanSemExceptionShapesRanged`
    whenever `declarations` is `DeclByteRanged`. -/
theorem panSemExceptionShapesRanged_of_exceptionEntries
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (declarations : List (Decl (RiscV.Word 64)))
    (hranged : ∀ d ∈ declarations, DeclByteRanged d) :
    PanSemExceptionShapesRanged
      { state with exceptionShapes :=
          fun name => panPropsALookupEq name (exceptionEntries declarations) } :=
  panSemExceptionShapesRanged_of_ALookupEq state (exceptionEntries declarations)
    (exceptionEntries_shapeByteRanged declarations hranged)

/-- **Update preservation.** `PanSemExceptionShapesRanged` is invariant under every
    production execution step: `panSemTotalEvaluate` never writes
    `exceptionShapes`, so the `Raise` premise holds for all reachable states. -/
theorem panSemTotalEvaluate_exceptionShapesRanged {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (prog : Prog (RiscV.Word 64))
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (h : PanSemExceptionShapesRanged state) :
    PanSemExceptionShapesRanged (panSemTotalEvaluate primitive prog state).2 := by
  intro exceptionId shape hlookup
  rw [panSemTotalEvaluate_exceptionShapes primitive prog state] at hlookup
  exact h exceptionId shape hlookup

/-- **Connection to the `Raise` agreement.** `panSemTotalEvaluate_raise_agree` with
    the free `hexnRanged` premise discharged from the intrinsic
    `PanSemExceptionShapesRanged production`. -/
theorem panSemTotalEvaluate_raise_agree_of_exceptionShapesRanged {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (hexn : PanSemExceptionShapesRanged production)
    (exceptionId : MlS) (expression : ExpHOL 64) :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive
          (.raise (toStringOfBytes exceptionId) (expOfHOL expression) :
            Prog (RiscV.Word 64)) production).1
        (evaluateHOLFiniteState exact (.raise exceptionId expression : ProgHOL 64)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive
          (.raise (toStringOfBytes exceptionId) (expOfHOL expression) :
            Prog (RiscV.Word 64)) production).2
        (evaluateHOLFiniteState exact (.raise exceptionId expression : ProgHOL 64)).2.toExact :=
  panSemTotalEvaluate_raise_agree primitive production exact hrel hranged hexn exceptionId expression

/-- Production/exact agreement for the `If` constructor, given the agreement
    of each branch at the same related state: both evaluators branch on a
    zero/non-zero word condition, and a failed or non-word condition yields
    `Error` with the state unchanged.  The branch hypotheses are the structural
    induction hypotheses of the eventual total agreement. -/
theorem panSemTotalEvaluate_ite_agree {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (condition : ExpHOL 64) (thenBranch elseBranch : ProgHOL 64)
    (ihThen : PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive (progOfHOL thenBranch) production).1
        (evaluateHOLFiniteState exact thenBranch).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive (progOfHOL thenBranch) production).2
        (evaluateHOLFiniteState exact thenBranch).2.toExact)
    (ihElse : PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive (progOfHOL elseBranch) production).1
        (evaluateHOLFiniteState exact elseBranch).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive (progOfHOL elseBranch) production).2
        (evaluateHOLFiniteState exact elseBranch).2.toExact) :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive
          (progOfHOL (.ite condition thenBranch elseBranch)) production).1
        (evaluateHOLFiniteState exact (.ite condition thenBranch elseBranch)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive
          (progOfHOL (.ite condition thenBranch elseBranch)) production).2
        (evaluateHOLFiniteState exact
          (.ite condition thenBranch elseBranch)).2.toExact := by
  have hc := evalPanSemStateExp_agree production exact hrel hranged
    (expOfHOL condition) (expOfHOL_byteRanged_bridge condition)
  simp only [expToHOL_expOfHOL, ← evalHOLFinite_eq_classical] at hc
  rw [progOfHOL, panSemTotalEvaluate, evaluateHOLFiniteState_ite, ← hc]
  cases hec : evalPanSemStateExp production (expOfHOL condition) with
  | none => exact ⟨trivial, hrel⟩
  | some cv =>
    cases cv with
    | rStruct _ => simp only [Option.map_some, panValueToHOL.eq_2]; exact ⟨trivial, hrel⟩
    | nStruct _ _ => simp only [Option.map_some, panValueToHOL.eq_3]; exact ⟨trivial, hrel⟩
    | word a =>
      simp only [Option.map_some, panValueToHOL_word]
      by_cases ha : a = 0
      · simp only [ha, if_true]; exact ihElse
      · simp only [ha, if_false]; exact ihThen

/-- `PanSemStateRelExec` carries over the production `panSemFixClock` and the
    exact `fixClockHOLFinite` (HOL `fix_clock`, whose `if … < …` clamp equals
    `min`). -/
theorem PanSemStateRelExec.fixClockHOLFinite {σ : Type} {β : Type}
    {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    (oldState : PanSemStateFiniteExact 64 σ)
    (step : β × PanSemStateFiniteExact 64 σ)
    (h : PanSemStateRelExec production step.2.toExact) :
    PanSemStateRelExec (panSemFixClock oldState.clock production)
      (PanSemStateFiniteExact.fixClockHOLFinite oldState step).2.toExact := by
  have hfix := PanSemStateRelExec.fixClock oldState.clock h
  have hclock : (if oldState.clock < step.2.clock then oldState.clock else step.2.clock) =
      min oldState.clock step.2.clock := by
    rw [Nat.min_def]
    by_cases hlt : oldState.clock < step.2.clock
    · simp [hlt, Nat.le_of_lt hlt]
    · by_cases hle : oldState.clock ≤ step.2.clock
      · simp [hlt, hle]; omega
      · simp [hlt, hle]
  simp only [PanSemStateFiniteExact.fixClockHOLFinite, hclock]
  exact hfix

/-- Production/exact agreement for the `Seq` constructor from the first
    sub-program's agreement and the second's agreement at every related, ranged
    state (it runs after `fix_clock`).  `hfirstRanged` is an explicit open gap:
    `PanSemStateRelExecRanged` is not preserved by every production step (see
    `extCallClause_not_ranged_of_global_nonRanged`), and discharging it is
    tracked by the rangedness bead `flapjack-pxn.18.4.3.77.2.15`. -/
theorem panSemTotalEvaluate_seq_agree {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact)
    (first second : ProgHOL 64)
    (ihFirst : PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive (progOfHOL first) production).1
        (evaluateHOLFiniteState exact first).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive (progOfHOL first) production).2
        (evaluateHOLFiniteState exact first).2.toExact)
    (hfirstRanged : PanSemStateRelExecRanged
        (panSemTotalEvaluate primitive (progOfHOL first) production).2)
    (ihSecond : ∀ (production' : PanSemState (RiscV.Word 64) (FfiState σ))
        (exact' : PanSemStateFiniteExact 64 σ),
        PanSemStateRelExec production' exact'.toExact →
        PanSemStateRelExecRanged production' →
        PanSemHOLResultOptionRel
            (panSemTotalEvaluate primitive (progOfHOL second) production').1
            (evaluateHOLFiniteState exact' second).1 ∧
          PanSemStateRelExec
            (panSemTotalEvaluate primitive (progOfHOL second) production').2
            (evaluateHOLFiniteState exact' second).2.toExact) :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive (progOfHOL (.seq first second)) production).1
        (evaluateHOLFiniteState exact (.seq first second)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive (progOfHOL (.seq first second)) production).2
        (evaluateHOLFiniteState exact (.seq first second)).2.toExact := by
  obtain ⟨hres, hstate⟩ := ihFirst
  have hfix := PanSemStateRelExec.fixClockHOLFinite exact
    (evaluateHOLFiniteState exact first) hstate
  have hclock : exact.clock = production.clock :=
    hrel.2.2.2.2.2.2.2.2.1
  rw [progOfHOL, panSemTotalEvaluate, evaluateHOLFiniteState_seq]
  simp only
  revert hres hfix hfirstRanged
  rw [← hclock]
  generalize panSemTotalEvaluate primitive (progOfHOL first) production = P
  generalize evaluateHOLFiniteState exact first = E
  intro hranged hres hfix
  rcases P with ⟨_ | r, p⟩ <;> rcases E with ⟨_ | e, q⟩
  · exact ihSecond _ _ hfix (hranged.setClock _)
  · exact hres.elim
  · exact hres.elim
  · exact ⟨hres, hfix⟩

/-- Production/exact agreement for the `Dec` constructor from the body's
    agreement at every related, ranged state: the initializer agreement, the
    shape-match correspondence `panShapeMatches_eq_shapeEqHOL`, the local bind
    (`PanSemStateRelExec.updateLocals`), and the `res_var` restore of the old
    binding (`PanSemStateRelExec.resVarLocals`). -/
theorem panSemTotalEvaluate_dec_agree {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) (body : ProgHOL 64)
    (ihBody : ∀ (production' : PanSemState (RiscV.Word 64) (FfiState σ))
        (exact' : PanSemStateFiniteExact 64 σ),
        PanSemStateRelExec production' exact'.toExact →
        PanSemStateRelExecRanged production' →
        PanSemHOLResultOptionRel
            (panSemTotalEvaluate primitive (progOfHOL body) production').1
            (evaluateHOLFiniteState exact' body).1 ∧
          PanSemStateRelExec
            (panSemTotalEvaluate primitive (progOfHOL body) production').2
            (evaluateHOLFiniteState exact' body).2.toExact) :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive
          (progOfHOL (.dec name shape initializer body)) production).1
        (evaluateHOLFiniteState exact (.dec name shape initializer body)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive
          (progOfHOL (.dec name shape initializer body)) production).2
        (evaluateHOLFiniteState exact (.dec name shape initializer body)).2.toExact := by
  have hi := evalPanSemStateExp_agree production exact hrel hranged
    (expOfHOL initializer) (expOfHOL_byteRanged_bridge initializer)
  simp only [expToHOL_expOfHOL, ← evalHOLFinite_eq_classical] at hi
  have hn := nameRanged_toStringOfBytes_bridge name
  rw [progOfHOL, panSemTotalEvaluate, evaluateHOLFiniteState_dec_total]
  simp only
  rw [← hi]
  cases hev : evalPanSemStateExp production (expOfHOL initializer) with
  | none => exact ⟨trivial, hrel⟩
  | some v =>
    simp only [Option.map_some]
    have hbv := evalPanSemStateExp_byteRanged production hranged
      (expOfHOL initializer) (expOfHOL_byteRanged_bridge initializer) v hev
    have hshapeRanged : ShapeByteRanged (panSemShapeOf v) := by
      have h := panValueShape_byteRanged production.structs v hbv
      rwa [panValueShape_eq_panSemShapeOf_tagged production.structs v] at h
    have hshapeExact : shapeOfHOLExact (panValueToHOL v) =
        shapeToHOL (panSemShapeOf v) := by
      rw [shapeOfHOLExact_panValueToHOL production.structs v,
        panValueShape_eq_panSemShapeOf_tagged production.structs v]
    have hmatch : panShapeMatches (shapeOfHOL shape) (panSemShapeOf v) =
        shapeEqHOL shape (shapeOfHOLExact (panValueToHOL v)) := by
      rw [panShapeMatches_eq_shapeEqHOL _ _ (shapeOfHOL_byteRanged_bridge shape)
        hshapeRanged, shapeToHOL_shapeOfHOL, hshapeExact]
    rw [← hmatch]
    by_cases hm : panShapeMatches (shapeOfHOL shape) (panSemShapeOf v) = true
    · simp only [hm, if_true]
      have hbodyRel := PanSemStateRelExec.updateLocals hrel (toStringOfBytes name) hn v
      rw [ofString_toStringOfBytes] at hbodyRel
      have hbodyRanged := PanSemStateRelExecRanged.updateLocals hranged
        (toStringOfBytes name) v hbv
      obtain ⟨hres, hstate⟩ := ihBody _ _ hbodyRel hbodyRanged
      refine ⟨hres, ?_⟩
      have hold : Option.map panValueToHOL (production.locals (toStringOfBytes name)) =
          exact.locals.lookup name := by
        have h := hrel.1 (toStringOfBytes name) hn
        rw [ofString_toStringOfBytes] at h
        exact h
      have hrestore := PanSemStateRelExec.resVarLocals hstate (toStringOfBytes name) hn
        (production.locals (toStringOfBytes name))
      rw [ofString_toStringOfBytes, hold] at hrestore
      exact hrestore
    · simp only [hm]
      exact ⟨trivial, hrel⟩

/-- Production/exact agreement for the `While` constructor from the body's
    agreement at every related, ranged state and the loop's agreement at every
    related, ranged state with a strictly smaller production clock (the
    well-founded hypothesis of the eventual total agreement).  It covers a
    failed or non-word condition, a zero condition, the clock-0 `TimeOut` with
    `empty_locals`, and every body result through `dec_clock`/`fix_clock`.
    `hbodyRanged` is the same open rangedness gap as in
    `panSemTotalEvaluate_seq_agree` (`flapjack-pxn.18.4.3.77.2.15`). -/
theorem panSemTotalEvaluate_while_agree {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (condition : ExpHOL 64) (body : ProgHOL 64)
    (ihBody : ∀ (production' : PanSemState (RiscV.Word 64) (FfiState σ))
        (exact' : PanSemStateFiniteExact 64 σ),
        PanSemStateRelExec production' exact'.toExact →
        PanSemStateRelExecRanged production' →
        PanSemHOLResultOptionRel
            (panSemTotalEvaluate primitive (progOfHOL body) production').1
            (evaluateHOLFiniteState exact' body).1 ∧
          PanSemStateRelExec
            (panSemTotalEvaluate primitive (progOfHOL body) production').2
            (evaluateHOLFiniteState exact' body).2.toExact)
    (hbodyRanged : PanSemStateRelExecRanged
        (panSemTotalEvaluate primitive (progOfHOL body)
          { production with clock := production.clock - 1 }).2)
    (ihLoop : ∀ (production' : PanSemState (RiscV.Word 64) (FfiState σ))
        (exact' : PanSemStateFiniteExact 64 σ),
        PanSemStateRelExec production' exact'.toExact →
        PanSemStateRelExecRanged production' →
        production'.clock < production.clock →
        PanSemHOLResultOptionRel
            (panSemTotalEvaluate primitive (progOfHOL (.while condition body)) production').1
            (evaluateHOLFiniteState exact' (.while condition body)).1 ∧
          PanSemStateRelExec
            (panSemTotalEvaluate primitive (progOfHOL (.while condition body)) production').2
            (evaluateHOLFiniteState exact' (.while condition body)).2.toExact) :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive (progOfHOL (.while condition body)) production).1
        (evaluateHOLFiniteState exact (.while condition body)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive (progOfHOL (.while condition body)) production).2
        (evaluateHOLFiniteState exact (.while condition body)).2.toExact := by
  letI : DecidablePred exact.memaddrs := fun a => Classical.propDecidable _
  have hc := evalPanSemStateExp_agree production exact hrel hranged
    (expOfHOL condition) (expOfHOL_byteRanged_bridge condition)
  simp only [expToHOL_expOfHOL] at hc
  have hck : exact.clock = production.clock := hrel.2.2.2.2.2.2.2.2.1
  simp only [progOfHOL] at ihLoop ⊢
  rw [panSemTotalEvaluate, evaluateHOLFiniteState_while_total, ← hc]
  cases hev : evalPanSemStateExp production (expOfHOL condition) with
  | none => exact ⟨trivial, hrel⟩
  | some cv =>
    cases cv with
    | rStruct _ => simp only [Option.map_some, panValueToHOL.eq_2]; exact ⟨trivial, hrel⟩
    | nStruct _ _ => simp only [Option.map_some, panValueToHOL.eq_3]; exact ⟨trivial, hrel⟩
    | word a =>
      simp only [Option.map_some, panValueToHOL_word]
      by_cases ha : a = 0
      · simp only [ha, if_true, ne_eq, not_true_eq_false, if_false]
        exact ⟨trivial, hrel⟩
      · simp only [ha, if_false, ne_eq, not_false_eq_true, if_true, hck]
        by_cases hz : production.clock = 0
        · simp only [hz, if_true]
          exact ⟨trivial, by
            simpa only [panEmptyLocals, toExact_emptyLocalsHOLFinite] using
              PanSemStateRelExec.emptyLocals hrel⟩
        · simp only [hz, if_false]
          have hdecRel : PanSemStateRelExec { production with clock := production.clock - 1 }
              (decClockHOLFinite exact).toExact := by
            simpa only [toExact_decClockHOLFinite] using PanSemStateRelExec.decClock hrel
          obtain ⟨hres, hstate⟩ := ihBody _ _ hdecRel (hranged.setClock _)
          have hfix := PanSemStateRelExec.fixClockHOLFinite (decClockHOLFinite exact)
            (evaluateHOLFiniteState (decClockHOLFinite exact) body) hstate
          have hdc : (decClockHOLFinite exact).clock = production.clock - 1 := by
            simp [decClockHOLFinite, hck]
          rw [hdc] at hfix
          have hlt : ∀ s : PanSemState (RiscV.Word 64) (FfiState σ),
              (panSemFixClock (production.clock - 1) s).clock < production.clock := by
            intro s
            have := panSemFixClock_clock_le (production.clock - 1) s
            omega
          revert hres hfix hbodyRanged
          generalize panSemTotalEvaluate primitive (progOfHOL body)
            { production with clock := production.clock - 1 } = P
          generalize evaluateHOLFiniteState (decClockHOLFinite exact) body = E
          intro hranged' hres hfix
          rcases P with ⟨_ | r, p⟩ <;> rcases E with ⟨_ | e, q⟩
          · exact ihLoop _ _ hfix (hranged'.setClock _) (hlt p)
          · exact hres.elim
          · exact hres.elim
          · cases r <;> cases e <;> simp only [PanSemHOLResultOptionRel, PanSemHOLResultRel] at hres <;>
              first
              | exact ihLoop _ _ hfix (hranged'.setClock _) (hlt p)
              | exact ⟨trivial, hfix⟩
              | exact ⟨hres, hfix⟩

end Flapjack
