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

/-! ## Structured-carrier bridges for the `.nStruct`/`.nField`/`.load` clauses

The remaining three structured constructors need the production `String`-keyed
carriers (`StructContext`/`StructContextHOL`/`HolValue`/`Shape`) bridged to the
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

end Flapjack
