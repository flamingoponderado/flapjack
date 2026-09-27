/-
# Production/exact carrier bridge for the captured `panSem$state`

HOL `panSem$evaluate_def` (`cakeml/pancake/semantics/panSemScript.sml:556-736`)
consumes the exact `panLang$prog` syntax over the faithful `mlstring` name
carrier (`ProgHOL`/`ExpHOL`) together with the finite-map `panSem$state`
(`locals`/`globals`/`code`/`eshapes` are `|->`, names are `mlstring`, word
payloads are `'a word_lab`).  The production executable evaluator instead runs
over `Prog (BitVec width)` with Lean `String` names and the generic
`PanSemState (BitVec width) ffi` carrier whose `locals`/`globals` are
unrestricted lookup functions, `code`/`eshapes` are association lists
(`InfoMap`), `memory` is a partial `BitVec width → Option (PanValue _)` map and
`memaddrs`/`sharedMemaddrs` are Boolean predicates.

This module supplies the kernel-checked representation bridge between the two
boundaries.  Nothing here is a port of a HOL declaration (there is no HOL
statement for a production/exact codec), so every declaration is untagged.

The bridge is built from the already-reviewed name/shape/expression/program
codecs (`ofString`/`toStringOfBytes`, `shapeToHOL`/`shapeOfHOL`,
`progToHOL`/`progOfHOL`, `paramToHOL`/`paramOfHOL`) and the struct-context
codec of the declaration bridge (`structContextToHOL`/`structContextOfHOL`).

Two genuine carrier mismatches are recorded explicitly rather than papered
over:

* production `memory : α → Option (PanValue α)` is partial and can hold record
  values, while HOL `memory : 'a word → 'a word_lab` is total and holds only
  word payloads.  The bridge does not invent a default: the forward codec takes
  the exact memory function as an argument together with the representation
  premise `PanSemMemoryRel` that the production map agrees with it on
  (`some (.word _)`) values.  This is a representation premise, not a semantic
  one.
* production `StructInfo` carries a source-only `shapedFields` cache that HOL
  `struct_info` does not have.  The exact-to-production direction erases it
  (`panStructContextOfHOL`); the production-to-exact direction drops it.  The
  production round-trip is therefore stated at the lookup level and the exact
  round-trip is unconditional.

The finite-support premise `∃ keys, ∀ key, f key ≠ none → key ∈ keys` on the
exact `code` map is the representation obligation needed to turn the function
carrier back into the production `InfoMap` association list
(`panSemStateOfExact`); HOL `code` is a finite map, so every real exact state
satisfies it.
-/

import Flapjack.Pancake.Semantics.PanSem.StateExactFinite
import Flapjack.Pancake.PanLang.Prog
import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.PanStatic

namespace Flapjack

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- A list map by an endofunction is the identity when the function fixes every
    element. -/
theorem listMap_eq_self_of {α : Type} {f : α → α} (l : List α)
    (h : ∀ x ∈ l, f x = x) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, h a (by simp)]
      exact congrArg (a :: ·) (ih (fun x hx => h x (by simp [hx])))

/-! ## Value codec -/

/-- Production values all of whose identifier payloads are byte-ranged (every
    character code `< 256`), hence exactly representable over HOL `mlstring`.
    The word payloads are always representable, so this is only a restriction on
    the `nStruct` name and field names. -/
def PanValueByteRanged {width : Nat} : PanValue (BitVec width) → Prop
  | .word _ => True
  | .rStruct fields => ∀ value ∈ fields, PanValueByteRanged value
  | .nStruct name fields =>
      NameRanged name ∧ ∀ field ∈ fields, NameRanged field.1 ∧ PanValueByteRanged field.2
termination_by value => sizeOf value
decreasing_by
  all_goals
    simp_wf
    first
      | (rename_i hmem
         have hlt := List.sizeOf_lt_of_mem hmem
         omega)
      | (rename_i hmem
         have hsnd : sizeOf field.snd < sizeOf field := by cases field; simp +arith
         have hlt := List.sizeOf_lt_of_mem hmem
         omega)

/-- Encode a production value into the exact HOL-shaped `ValueHOL`.  Names use
    the total `ofString`; word payloads are preserved. -/
def panValueToHOL {width : Nat} [NeZero width] :
    PanValue (BitVec width) → ValueHOL width
  | .word bits => .val (.word bits)
  | .rStruct fields => .rStruct (fields.map panValueToHOL)
  | .nStruct name fields =>
      .nStruct (ofString name)
        (fields.map (fun field => (ofString field.1, panValueToHOL field.2)))
termination_by value => sizeOf value
decreasing_by
  all_goals
    simp_wf
    first
      | (rename_i hmem
         have hlt := List.sizeOf_lt_of_mem hmem
         omega)
      | (rename_i hmem
         have hsnd : sizeOf field.snd < sizeOf field := by cases field; simp +arith
         have hlt := List.sizeOf_lt_of_mem hmem
         omega)

/-- Decode the exact `ValueHOL` back to a production `PanValue`.  Names use the
    total `toStringOfBytes`; word payloads are preserved. -/
def panValueOfHOL {width : Nat} [NeZero width] :
    ValueHOL width → PanValue (BitVec width)
  | .val (.word bits) => .word bits
  | .rStruct fields => .rStruct (fields.map panValueOfHOL)
  | .nStruct name fields =>
      .nStruct (toStringOfBytes name)
        (fields.map (fun field => (toStringOfBytes field.1, panValueOfHOL field.2)))
termination_by value => sizeOf value
decreasing_by
  all_goals
    simp_wf
    first
      | (rename_i hmem
         have hlt := List.sizeOf_lt_of_mem hmem
         omega)
      | (rename_i hmem
         have hsnd : sizeOf field.snd < sizeOf field := by cases field; simp +arith
         have hlt := List.sizeOf_lt_of_mem hmem
         omega)

@[simp] theorem panValueToHOL_word {width : Nat} [NeZero width] (bits : BitVec width) :
    panValueToHOL (.word bits) = .val (.word bits) := by
  simp only [panValueToHOL]

/-- Decoding an encoded exact value is the identity (the exact side carries
    `mlstring`, which `ofString`/`toStringOfBytes` round-trip exactly). -/
@[simp] theorem panValueToHOL_panValueOfHOL {width : Nat} [NeZero width]
    (value : ValueHOL width) :
    panValueToHOL (panValueOfHOL value) = value := by
  induction value using panValueOfHOL.induct with
  | case1 bits => simp only [panValueOfHOL, panValueToHOL]
  | case2 fields ih =>
      simp only [panValueOfHOL, panValueToHOL]
      rw [List.map_map]
      apply congrArg ValueHOL.rStruct
      apply listMap_eq_self_of
      intro x hx
      simp only [Function.comp_apply]
      exact ih x hx
  | case3 name fields ih =>
      simp only [panValueOfHOL, panValueToHOL]
      rw [ofString_toStringOfBytes name, List.map_map]
      apply congrArg (ValueHOL.nStruct name)
      apply listMap_eq_self_of
      intro a ha
      obtain ⟨an, av⟩ := a
      simp only [Function.comp_apply, ofString_toStringOfBytes]
      exact congrArg (fun v => (an, v)) (ih (an, av) ha)

/-- Decoding the encoding of a byte-ranged production value recovers it. -/
theorem panValueOfHOL_panValueToHOL {width : Nat} [NeZero width]
    (value : PanValue (BitVec width)) :
    PanValueByteRanged value → panValueOfHOL (panValueToHOL value) = value := by
  induction value using panValueToHOL.induct with
  | case1 bits => intro _; simp only [panValueToHOL, panValueOfHOL]
  | case2 fields ih =>
      intro h
      simp only [PanValueByteRanged] at h
      simp only [panValueToHOL, panValueOfHOL]
      rw [List.map_map]
      apply congrArg PanValue.rStruct
      apply listMap_eq_self_of
      intro x hx
      simp only [Function.comp_apply]
      exact ih x hx (h x hx)
  | case3 name fields ih =>
      intro h
      simp only [PanValueByteRanged] at h
      obtain ⟨hname, hfields⟩ := h
      simp only [panValueToHOL, panValueOfHOL]
      rw [toStringOfBytes_ofString_of_bytes name hname, List.map_map]
      apply congrArg (PanValue.nStruct name)
      apply listMap_eq_self_of
      intro a ha
      obtain ⟨an, av⟩ := a
      obtain ⟨han, hav⟩ := hfields (an, av) ha
      simp only [Function.comp_apply, toStringOfBytes_ofString_of_bytes an han]
      exact congrArg (fun v => (an, v)) (ih (an, av) ha hav)

/-! ## Code-entry and struct-context codecs -/

/-- Encode one `panSem$state.code` entry: parameter shapes, body and return
    shape. -/
def panLangEntryToHOL {width : Nat} [NeZero width]
    (entry : List (VarName × Shape) × Prog (BitVec width) × Shape) :
    List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL :=
  (entry.1.map paramToHOL, progToHOL entry.2.1, shapeToHOL entry.2.2)

/-- Decode one `panSem$state.code` entry back to production syntax. -/
def panLangEntryOfHOL {width : Nat} [NeZero width]
    (entry : List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL) :
    List (VarName × Shape) × Prog (BitVec width) × Shape :=
  (entry.1.map paramOfHOL, progOfHOL entry.2.1, shapeOfHOL entry.2.2)

/-- A production code entry that survives the exact round-trip. -/
def PanLangEntryByteRanged {width : Nat} [NeZero width]
    (entry : List (VarName × Shape) × Prog (BitVec width) × Shape) : Prop :=
  ListParamByteRanged entry.1 ∧ ProgByteRanged entry.2.1 ∧ ShapeByteRanged entry.2.2

@[simp] theorem panLangEntryToHOL_panLangEntryOfHOL {width : Nat} [NeZero width]
    (entry : List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL) :
    panLangEntryToHOL (panLangEntryOfHOL entry) = entry := by
  obtain ⟨params, body, returnShape⟩ := entry
  simp [panLangEntryToHOL, panLangEntryOfHOL, progToHOL_progOfHOL]

theorem panLangEntryOfHOL_panLangEntryToHOL {width : Nat} [NeZero width]
    (entry : List (VarName × Shape) × Prog (BitVec width) × Shape)
    (h : PanLangEntryByteRanged entry) :
    panLangEntryOfHOL (panLangEntryToHOL entry) = entry := by
  obtain ⟨params, body, returnShape⟩ := entry
  obtain ⟨hparams, hbody, hshape⟩ := h
  simp [panLangEntryToHOL, panLangEntryOfHOL, listParamOfHOL_paramToHOL params hparams,
    progOfHOL_progToHOL body hbody, shapeOfHOL_shapeToHOL returnShape hshape]

/-- Encode a production struct context into the exact `MlS`-keyed context,
    dropping the source-only `shapedFields` cache. -/
def panStructContextToHOL (context : StructContext) : StructContextExact :=
  structContextToHOL context.toHOL

/-- Decode the exact `MlS`-keyed struct context back to production, filling the
    cache with the empty list. -/
def panStructContextOfHOL (context : StructContextExact) : StructContext :=
  (structContextOfHOL context).map
    (fun entry => (entry.1, { fields := entry.2.fields, size := entry.2.size, shapedFields := [] }))

theorem toHOL_panStructContextOfHOL (context : StructContextExact) :
    (panStructContextOfHOL context).toHOL = structContextOfHOL context := by
  unfold panStructContextOfHOL StructContext.toHOL
  rw [List.map_map]
  apply listMap_eq_self_of
  intro entry _
  obtain ⟨name, info⟩ := entry
  rfl

@[simp] theorem panStructContextToHOL_panStructContextOfHOL
    (context : StructContextExact) :
    panStructContextToHOL (panStructContextOfHOL context) = context := by
  unfold panStructContextToHOL
  rw [toHOL_panStructContextOfHOL, structContextToHOL_structContextOfHOL]

/-! ## Code-map finite-support helper

Production `code` is an association list (`InfoMap`); the exact `code` is a
lookup function.  `mlFunctionToInfoMap` is the finite-support inverse: given a
support list covering every non-`none` value of the function, it builds the
association list (in support order) whose first-match lookup agrees with the
function everywhere. -/

/-- Build a production `InfoMap` from an exact lookup function and a support
    list that covers every key with a non-`none` value. -/
def mlFunctionToInfoMap {β : Type} (f : MlS → Option β) : List MlS → InfoMap β
  | [] => []
  | key :: keys =>
      match f key with
      | none => mlFunctionToInfoMap f keys
      | some value => (toStringOfBytes key, value) :: mlFunctionToInfoMap f keys

/-- `lookupInfo` of the finite-support InfoMap returns exactly the function
    value at every key whose `MlString` encoding is queried, provided the
    queried key's `some` value is covered by the support. -/
theorem lookupInfo_mlFunctionToInfoMap {β : Type} [BEq String] [LawfulBEq String]
    (f : MlS → Option β) (keys : List MlS) :
    ∀ query, (f query ≠ none → query ∈ keys) →
      lookupInfo (toStringOfBytes query) (mlFunctionToInfoMap f keys) = f query := by
  induction keys with
  | nil =>
      intro query hquery
      by_cases hf : f query = none
      · simp [mlFunctionToInfoMap, lookupInfo, hf]
      · exact absurd (hquery hf) (List.not_mem_nil)
  | cons head tail ih =>
      intro query hquery
      cases hhead : f head with
      | none =>
          have htail : f query ≠ none → query ∈ tail := by
            intro hq
            rcases List.mem_cons.mp (hquery hq) with hmem | hmem
            · subst hmem
              exact absurd hhead hq
            · exact hmem
          simp only [mlFunctionToInfoMap, hhead]
          exact ih query htail
      | some value =>
          by_cases hbeq : toStringOfBytes head == toStringOfBytes query
          · have heq : head = query := toStringOfBytes_injective (beq_iff_eq.mp hbeq)
            subst heq
            simp only [mlFunctionToInfoMap, hhead, lookupInfo,
              if_pos (beq_self_eq_true _)]
          · have hne : head ≠ query := by
              intro h
              exact hbeq (by rw [h]; exact beq_self_eq_true _)
            have htail : f query ≠ none → query ∈ tail := by
              intro hq
              rcases List.mem_cons.mp (hquery hq) with hmem | hmem
              · exact absurd hmem.symm hne
              · exact hmem
            simp only [mlFunctionToInfoMap, hhead, lookupInfo, if_neg hbeq]
            exact ih query htail

/-! ## State relation and codecs -/

/-- Word payload of an exact `word_lab`. -/
def holWordLabBits {width : Nat} [NeZero width] : HolWordLab width → BitVec width
  | .word bits => bits

@[simp] theorem holWordLabBits_word {width : Nat} [NeZero width] (bits : BitVec width) :
    holWordLabBits (.word bits) = bits := rfl

/-- Memory agreement: the production partial memory is `some` exactly on its
    word-valued entries and matches the exact total word-lab memory there.  This
    is the representation premise for the otherwise incompatible memory
    carriers (partial generic value versus total `word_lab`). -/
def PanSemMemoryRel {width : Nat} [NeZero width]
    (memory : RiscV.Word width → Option (PanValue (BitVec width)))
    (exactMemory : RiscV.Word width → HolWordLab width) : Prop :=
  ∀ address, memory address = some (.word (holWordLabBits (exactMemory address)))

/-- Field-wise representation relation between a production `PanSemState` over
    `BitVec width`/`HolFfiState σ` and the exact `PanSemStateExact` carrier.

    The map fields are compared at byte-ranged production keys (the only keys
    whose `MlString` image round-trips); the code payloads use the exact
    `panLangEntryToHOL` codec; `structs` uses the cache-dropping context codec;
    `memaddrs`/`sharedMemaddrs` relate production Booleans to HOL propositions;
    `memory` uses `PanSemMemoryRel`; and the scalar/FFI fields agree by
    equality. -/
def PanSemStateRel {width : Nat} [NeZero width] {σ : Type}
    (production : PanSemState (RiscV.Word width) (HolFfiState σ))
    (exact : PanSemStateExact width σ) : Prop :=
  (∀ name, NameRanged name →
      Option.map panValueToHOL (production.locals name) = exact.locals (ofString name)) ∧
  (∀ name, NameRanged name →
      Option.map panValueToHOL (production.globals name) = exact.globals (ofString name)) ∧
  panStructContextToHOL production.structs = exact.structs ∧
  (∀ name, NameRanged name →
      Option.map panLangEntryToHOL (panSemCodeLookup production.code name) =
        exact.code (ofString name)) ∧
  (∀ name, NameRanged name →
      Option.map shapeToHOL (production.exceptionShapes name) = exact.eshapes (ofString name)) ∧
  PanSemMemoryRel production.memory exact.memory ∧
  (∀ address, production.memaddrs address = true ↔ exact.memaddrs address) ∧
  (∀ address, production.sharedMemaddrs address = true ↔ exact.shMemaddrs address) ∧
  exact.clock = production.clock ∧
  exact.be = production.be ∧
  exact.baseAddr = production.baseAddress ∧
  exact.topAddr = production.topAddress

/-- Forward state codec: view a production state as the exact carrier.  The
    exact memory function is supplied together with the representation premise
    `PanSemMemoryRel`, because the production memory is partial and the exact
    one is total. -/
def panSemStateToExact {width : Nat} [NeZero width] {σ : Type}
    (production : PanSemState (RiscV.Word width) (HolFfiState σ))
    (exactMemory : RiscV.Word width → HolWordLab width)
    (_hmem : PanSemMemoryRel production.memory exactMemory) :
    PanSemStateExact width σ where
  locals := fun name => Option.map panValueToHOL (production.locals (toStringOfBytes name))
  globals := fun name => Option.map panValueToHOL (production.globals (toStringOfBytes name))
  structs := panStructContextToHOL production.structs
  code := fun name =>
    Option.map panLangEntryToHOL (panSemCodeLookup production.code (toStringOfBytes name))
  eshapes := fun name =>
    Option.map shapeToHOL (production.exceptionShapes (toStringOfBytes name))
  memory := exactMemory
  memaddrs := fun address => production.memaddrs address = true
  shMemaddrs := fun address => production.sharedMemaddrs address = true
  clock := production.clock
  be := production.be
  ffi := production.ffi
  baseAddr := production.baseAddress
  topAddr := production.topAddress

/-- The forward codec lands in the state relation. -/
theorem panSemStateRel_toExact {width : Nat} [NeZero width] {σ : Type}
    (production : PanSemState (RiscV.Word width) (HolFfiState σ))
    (exactMemory : RiscV.Word width → HolWordLab width)
    (hmem : PanSemMemoryRel production.memory exactMemory) :
    PanSemStateRel production (panSemStateToExact production exactMemory hmem) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro name hname
    simp only [panSemStateToExact, toStringOfBytes_ofString_of_bytes name hname]
  · intro name hname
    simp only [panSemStateToExact, toStringOfBytes_ofString_of_bytes name hname]
  · simp only [panSemStateToExact]
  · intro name hname
    simp only [panSemStateToExact, toStringOfBytes_ofString_of_bytes name hname]
  · intro name hname
    simp only [panSemStateToExact, toStringOfBytes_ofString_of_bytes name hname]
  · simpa only [panSemStateToExact] using hmem
  · intro address
    simp only [panSemStateToExact]
  · intro address
    simp only [panSemStateToExact]
  · simp only [panSemStateToExact]
  · simp only [panSemStateToExact]
  · simp only [panSemStateToExact]
  · simp only [panSemStateToExact]

/-- Reverse state codec: view the exact carrier as a production state.  The
    finite-support premise on the exact `code` map is the representation
    obligation that lets the function carrier be turned back into the
    production association list; `memaddrs`/`sharedMemaddrs` are decided. -/
noncomputable def panSemStateOfExact {width : Nat} [NeZero width] {σ : Type}
    (exact : PanSemStateExact width σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (codeSupport : ∃ keys : List MlS, ∀ key, exact.code key ≠ none → key ∈ keys) :
    PanSemState (RiscV.Word width) (HolFfiState σ) where
  locals := fun name => Option.map panValueOfHOL (exact.locals (ofString name))
  globals := fun name => Option.map panValueOfHOL (exact.globals (ofString name))
  structs := panStructContextOfHOL exact.structs
  code := mlFunctionToInfoMap
    (fun key => Option.map panLangEntryOfHOL (exact.code key))
    (Classical.choose codeSupport)
  exceptionShapes := fun name => Option.map shapeOfHOL (exact.eshapes (ofString name))
  memory := fun address => some (.word (holWordLabBits (exact.memory address)))
  memaddrs := fun address => decide (exact.memaddrs address)
  sharedMemaddrs := fun address => decide (exact.shMemaddrs address)
  clock := exact.clock
  be := exact.be
  ffi := exact.ffi
  baseAddress := exact.baseAddr
  topAddress := exact.topAddr

theorem panSemStateMemoryRel_ofExact {width : Nat} [NeZero width] {σ : Type}
    (exact : PanSemStateExact width σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (codeSupport : ∃ keys : List MlS, ∀ key, exact.code key ≠ none → key ∈ keys) :
    PanSemMemoryRel (panSemStateOfExact exact codeSupport).memory exact.memory := by
  intro address
  simp only [panSemStateOfExact]

/-- The reverse codec lands in the state relation. -/
theorem panSemStateRel_ofExact {width : Nat} [NeZero width] {σ : Type}
    (exact : PanSemStateExact width σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (codeSupport : ∃ keys : List MlS, ∀ key, exact.code key ≠ none → key ∈ keys) :
    PanSemStateRel (panSemStateOfExact exact codeSupport) exact := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro name _
    cases hloc : exact.locals (ofString name) with
    | none => simp only [panSemStateOfExact, hloc, Option.map_none]
    | some value => simp only [panSemStateOfExact, hloc, Option.map_some,
        panValueToHOL_panValueOfHOL]
  · intro name _
    cases hloc : exact.globals (ofString name) with
    | none => simp only [panSemStateOfExact, hloc, Option.map_none]
    | some value => simp only [panSemStateOfExact, hloc, Option.map_some,
        panValueToHOL_panValueOfHOL]
  · simp only [panSemStateOfExact, panStructContextToHOL_panStructContextOfHOL]
  · intro name hname
    have hsupport := Classical.choose_spec codeSupport
    have hname' : name = toStringOfBytes (ofString name) :=
      (toStringOfBytes_ofString_of_bytes name hname).symm
    simp only [panSemStateOfExact, panSemCodeLookup]
    rw [hname']
    simp only [ofString_toStringOfBytes]
    rw [lookupInfo_mlFunctionToInfoMap
      (fun key => Option.map panLangEntryOfHOL (exact.code key)) (Classical.choose codeSupport)
      (ofString name) (fun hq => hsupport (ofString name) (by
        intro hc
        exact hq (by rw [hc]; rfl)))]
    cases hcode : exact.code (ofString name) with
    | none => simp only [Option.map_none]
    | some value => simp only [Option.map_some, panLangEntryToHOL_panLangEntryOfHOL]
  · intro name _
    cases heshape : exact.eshapes (ofString name) with
    | none => simp only [panSemStateOfExact, heshape, Option.map_none]
    | some value => simp only [panSemStateOfExact, heshape, Option.map_some,
        shapeToHOL_shapeOfHOL]
  · exact panSemStateMemoryRel_ofExact exact codeSupport
  · intro address
    simp only [panSemStateOfExact, decide_eq_true_eq]
  · intro address
    simp only [panSemStateOfExact, decide_eq_true_eq]
  · simp only [panSemStateOfExact]
  · simp only [panSemStateOfExact]
  · simp only [panSemStateOfExact]
  · simp only [panSemStateOfExact]

/-- Extensionality for `PanSemStateExact` (the structure is not registered with
    the `ext` attribute). -/
theorem PanSemStateExact.extBridge {width : Nat} {σ : Type} [NeZero width]
    {left right : PanSemStateExact width σ}
    (hlocals : left.locals = right.locals) (hglobals : left.globals = right.globals)
    (hstructs : left.structs = right.structs) (hcode : left.code = right.code)
    (heshapes : left.eshapes = right.eshapes) (hmemory : left.memory = right.memory)
    (hmemaddrs : left.memaddrs = right.memaddrs)
    (hshMemaddrs : left.shMemaddrs = right.shMemaddrs)
    (hclock : left.clock = right.clock) (hbe : left.be = right.be)
    (hffi : left.ffi = right.ffi) (hbaseAddr : left.baseAddr = right.baseAddr)
    (htopAddr : left.topAddr = right.topAddr) : left = right := by
  cases left
  cases right
  simp_all

/-- Exact-side round-trip: encoding the decoded exact state recovers it.  The
    memory function is `exact.memory` itself, so the `PanSemMemoryRel` premise
    is definitional. -/
theorem panSemStateToExact_ofExact {width : Nat} [NeZero width] {σ : Type}
    (exact : PanSemStateExact width σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (codeSupport : ∃ keys : List MlS, ∀ key, exact.code key ≠ none → key ∈ keys) :
    panSemStateToExact (panSemStateOfExact exact codeSupport) exact.memory
      (panSemStateMemoryRel_ofExact exact codeSupport) = exact := by
  cases exact with
  | mk locals globals structs code eshapes memory memaddrs shMemaddrs clock be ffi baseAddr topAddr =>
    refine PanSemStateExact.extBridge ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · funext name
      simp only [panSemStateToExact, panSemStateOfExact, ofString_toStringOfBytes]
      cases locals name <;> simp [panValueToHOL_panValueOfHOL]
    · funext name
      simp only [panSemStateToExact, panSemStateOfExact, ofString_toStringOfBytes]
      cases globals name <;> simp [panValueToHOL_panValueOfHOL]
    · simp only [panSemStateToExact, panSemStateOfExact,
        panStructContextToHOL_panStructContextOfHOL]
    · funext name
      simp only [panSemStateToExact, panSemStateOfExact, panSemCodeLookup]
      rw [lookupInfo_mlFunctionToInfoMap
        (fun key => Option.map panLangEntryOfHOL (code key)) (Classical.choose codeSupport)
        name (fun hq => Classical.choose_spec codeSupport name (by
          intro hc
          exact hq (by rw [show code name = none from hc]; rfl)))]
      cases code name <;> simp [panLangEntryToHOL_panLangEntryOfHOL]
    · funext name
      simp only [panSemStateToExact, panSemStateOfExact, ofString_toStringOfBytes]
      cases eshapes name <;> simp [shapeToHOL_shapeOfHOL]
    · simp only [panSemStateToExact, panSemStateOfExact]
    · funext address
      simp only [panSemStateToExact, panSemStateOfExact]
      exact decide_eq_true_eq
    · funext address
      simp only [panSemStateToExact, panSemStateOfExact]
      exact decide_eq_true_eq
    · simp only [panSemStateToExact, panSemStateOfExact]
    · simp only [panSemStateToExact, panSemStateOfExact]
    · simp only [panSemStateToExact, panSemStateOfExact]
    · simp only [panSemStateToExact, panSemStateOfExact]
    · simp only [panSemStateToExact, panSemStateOfExact]

end Flapjack
