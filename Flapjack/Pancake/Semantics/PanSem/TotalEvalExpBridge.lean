import Flapjack.Pancake.Semantics.PanSem.TotalEvalBridge
import Flapjack.Pancake.Semantics.PanSem.EvalFinite
import Flapjack.Pancake.Semantics.PanSem.MemLoadHOL
import Flapjack.Pancake.Semantics.PanSem.StateExactFinite

/-!
# Production/exact expression-evaluation agreement for the total `panSem` bridge

`Flapjack/Pancake/Semantics/PanSem/TotalEvalBridge.lean` records
`PanSemStateRelExec` between the executable production `PanSemState` and the
exact `PanSemStateFiniteExact`, but only the expression-free `Prog` leaf clauses.

This module proves the missing prerequisite: for the production `Exp`
constructors that do not need a structured-context or structured-load carrier
bridge, the executable expression evaluator `evalPanSemStateExp` agrees with the
exact `evalHOLExact` on the `expToHOL` image.  The agreement is stated through
the value codec `panValueToHOL` (the executable `PanValue` is mapped into the
exact `ValueHOL` carrier), for arbitrary hosts `σ`.

The constructors proved here are `const`, `var`, `rStruct`, `rField`,
`baseAddr`, `topAddr`, `bytesInWord`, `op`, `panOp`, `cmp`, `shift`, `load32`,
and `loadByte`, together with the list/field/name/shape/memory bridge
infrastructure.  The three remaining constructors (`nStruct`, `nField`, `load`)
need the production `StructContext` / `panMemLoadHOL` versus the exact
`StructContextExact` / `memLoadHOLExact` carrier agreement; they are tracked by
the child bead `flapjack-pxn.18.4.3.77.2.12.1` and are deliberately not claimed
here.

## Representation premises

`PanSemStateRelExec` compares the executable `String`-keyed state with the exact
`mlstring`-keyed state only at byte-ranged names, and its `structs`/`memory`
comparison does not constrain the production `String` names or value field names
to the byte range that HOL `char`/`mlstring` represents.  Two representation
premises are therefore needed and recorded explicitly rather than assumed away:

* `ExpByteRanged e` / `ShapeByteRanged shape` -- every identifier and shape name
  occurring in the expression is byte-ranged, so its `expToHOL` image (through the
  low-byte `ofString`) round-trips and name comparisons transfer;
* `PanSemStateRelExecRanged state` -- the executable local/global values and the
  structure context are byte-ranged, so a stored record's field-name lookups and
  a context shape comparison agree with their `mlstring` images.

Neither premise is a semantic condition on evaluation: both hold for
parser-produced programs and states.  Everything in this module is untagged
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

/-- `ofString` is injective on byte-ranged strings. -/
theorem ofString_injective_of_ranged {a b : String} (ha : NameRanged a) (hb : NameRanged b)
    (h : ofString a = ofString b) : a = b := by
  have h' := congrArg toStringOfBytes h
  rwa [toStringOfBytes_ofString_of_bytes a ha,
    toStringOfBytes_ofString_of_bytes b hb] at h'

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

end Flapjack
