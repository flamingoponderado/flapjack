/-
  Finite-support PanSem state carrier.

  HOL `panSem$state` stores its `locals`, `globals`, `code` and `eshapes`
  components as finite maps (`|->`).  `PanSemStateExact` instead quantifies
  them as unrestricted lookup functions (`MlS → Option _`), which is a strict
  superset of the finite-map carriers. Five exact state helpers
  (`dec_clock`, `fix_clock`, `lookup_kvar`, `set_kvar`, `empty_locals`) were
  temporarily withdrawn from `@[hol]` tagging at audit
  `flapjack-pxn.18.3.7.1.3.1.2`. This module provides a carrier that is
  finite-support *by type*; those five and the `set_var`/`set_global` helpers
  have since been reviewed and tagged over it.

  Statement/side-condition review for `flapjack-pxn.18.3.7.1.3.1.1.2`
  (2026-09-25): the five HOL definitions
  (`cakeml/pancake/semantics/panSemScript.sml:396-449`) quantify the state
  component as a finite map `varname |-> v`, written with `FUPDATE`/`FLOOKUP`,
  whereas `PanSemStateFiniteExact` carries a   `HolFiniteMapExact` value (a
  `lookup` function together with a `finiteSupport` proof).  `HolFiniteMapExact`
  is the reviewed *standard* Lean translation of HOL's finite map: it is closed,
  extensional (see `HolFiniteMapExact.ext`), and invertible with the
  finite-support subtype of the broad `PanSemStateExact` carrier (see
  `PanSemStateFiniteExact.ofExact` / `toExact` and the canonical witness
  `holFmapAsFiniteSupportWitness`).  The representation is recorded by the
  `@[hol ...]` qualifier `fmap_as_finite_support` implemented in
  `Flapjack/HolRef.lean` and enforced by `scripts/check-hol-refs.py`; it is a
  representation statement only and does not authorize changed quantifiers,
  hypotheses, results, `BEq` side conditions, or word-model differences.

  Seven helper definitions have passed their case-by-case review and carry
  `@[hol ...]` with that qualifier: `decClockHOLFinite` (`dec_clock_def`),
  `fixClockHOLFinite` (`fix_clock_def`), `lookupKvarHOLFinite` (`lookup_kvar_def`),
  `emptyLocalsHOLFinite` (`empty_locals_def`) and `setKvarHOLFinite`
  (`set_kvar_def`), plus `setVarHOLFinite` (`set_var_def`) and
  `setGlobalHOLFinite` (`set_global_def`). `setKvarHOLFinite` routes through
  these canonical-update helpers, which use
  `HolFiniteMapExact.update` (`FUPDATE`) exactly like HOL `set_var`/`set_global`;
  the `MlS` `BEq`/`LawfulBEq` instances required by `update` are declared below.
  The broad-carrier helpers over `PanSemStateExact` (`StateExact.lean`) remain the
  `documented_mismatch` analogues.  Work tracked by
  `flapjack-pxn.18.3.7.1.3.1.1.2.4`.

  Word-model review for `flapjack-pxn.18.3.7.1.3.1.1.2.4.6` (2026-09-25): HOL
  types the state components over `'a word` for an arbitrary finite type `'a`
  (the `finite_index` class; `panSemScript.sml:48-63` uses `'a word` for
  `memory`/`base_addr`/`top_addr` and `'a word_lab` for the memory values), while
  this module uses `RiscV.Word width` (`= BitVec width`, `RiscV/Model.lean:17`)
  together with `[NeZero width]` and `HolWordLab width`.  A HOL finite type is
  nonempty, so `dimindex 'a >= 1`, and the positive-width `BitVec width` carrier
  is the standard faithful translation of `'a word` (with `HolWordLab` its
  `word_lab` wrapper).  The five helpers themselves are word-agnostic: they only
  read/write `clock` and the finite-map fields, so they add no word-model side
  condition; `[NeZero width]` mirrors HOL nonemptiness and is a carrier artifact,
  not a changed side condition of the tagged definitions.
-/

import Flapjack.Pancake.Semantics.PanSem.StateExactFinite
import Flapjack.Pancake.Semantics.PanSem.EvalExact
import Flapjack.Pancake.Semantics.PanSem.FiniteSupportStep
import Flapjack.Pancake.Semantics.PanSem.ExtCallExact
import Flapjack.Pancake.Semantics.PanSem.GlobalsShapesExact

namespace Flapjack

open Flapjack.Pancake.PanLang
  (MlS ShapeHOL StructContextExact ProgHOL ExpHOL DeclHOL FunDeclHOL isWfShapeExactHOL isNameHOL
    functionsHOL)

/-- `HolFiniteMapExact` is extensional: two values with the same `lookup` are
    equal, because the `finiteSupport` field is a proof of a proposition.  This
    is separate from the canonical roundtrip witness below. -/
theorem HolFiniteMapExact.ext {α β : Type} {left right : HolFiniteMapExact α β}
    (h : left.lookup = right.lookup) : left = right := by
  obtain ⟨lleft, pleft⟩ := left
  obtain ⟨lright, pright⟩ := right
  simp only at h
  subst h
  rfl

/-- `MlString` only derives `DecidableEq`; the canonical `FUPDATE`-based finite-map
    operations need a `BEq`/`LawfulBEq` instance, so boolean equality is the
    decidability test.  Declared here as representation infrastructure (additive:
    `MlS` had no `BEq` instance before). -/
instance : BEq MlS where
  beq left right := decide (left = right)

instance : LawfulBEq MlS where
  eq_of_beq h := of_decide_eq_true h

/-- Reading `HolFiniteMapExact.update` (`FUPDATE`) pointwise.  The canonical
    update's `if name == current` is the same test as the pointwise
    `if current = name` used by the broad `set_var`/`set_global` mirrors. -/
theorem HolFiniteMapExact.lookup_update_pointwise {α β : Type} [BEq α] [LawfulBEq α]
    [DecidableEq α] (map : HolFiniteMapExact α β) (name : α) (value : β) :
    (map.update (name, value)).lookup =
      fun current => if current = name then some value else map.lookup current := by
  funext current
  by_cases h : current = name
  · subst h
    simp [HolFiniteMapExact.update, FUPDATE]
  · have hbeq : (name == current) = false := by
      cases hb : (name == current) with
      | true => exact absurd (beq_iff_eq.mp hb) (fun hc => h hc.symm)
      | false => rfl
    simp [HolFiniteMapExact.update, FUPDATE, hbeq, h]

/-- Finite-support mirror of `PanSemStateExact`.  The four map-shaped
    components are `HolFiniteMapExact` values, i.e. finite support holds by
    construction, matching HOL's `|->` fields.

    This is the exact Lean counterpart of the HOL `panSem$state` datatype
    (`cakeml/pancake/semantics/panSemScript.sml:46-64`): the 13 fields appear in
    the same order with the same meaning.  The name-bearing maps
    `locals`/`globals`/`code`/`eshapes` are the reviewed canonical
    `HolFiniteMapExact` translation of HOL's `|->` fields; the `structs`
    component is the exact `StructContextExact` context, `memory` is the exact
    `RiscV.Word width → HolWordLab width` carrier, the address domains are
    predicates, and `ffi`/`clock`/`be`/`base_addr`/`top_addr` keep HOL's
    meanings.  The `fmap_as_finite_support` qualifier records only this
    finite-map representation and authorizes no other difference; the canonical
    witness `holFmapAsFiniteSupportWitness` below is the roundtrip between this
    structure and the broad `PanSemStateExact`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "state"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
structure PanSemStateFiniteExact (width : Nat) (σ : Type) [NeZero width] where
  locals : HolFiniteMapExact MlS (ValueHOL width)
  globals : HolFiniteMapExact MlS (ValueHOL width)
  structs : StructContextExact
  code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)
  eshapes : HolFiniteMapExact MlS ShapeHOL
  memory : RiscV.Word width → HolWordLab width
  memaddrs : RiscV.Word width → Prop
  shMemaddrs : RiscV.Word width → Prop
  clock : Nat
  be : Bool
  ffi : HolFfiState σ
  baseAddr : RiscV.Word width
  topAddr : RiscV.Word width

namespace PanSemStateFiniteExact

/-- Forget the finite-support witnesses, reading every map through `.lookup`. -/
@[reducible] def toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) : PanSemStateExact width σ where
  locals := state.locals.lookup
  globals := state.globals.lookup
  structs := state.structs
  code := state.code.lookup
  eshapes := state.eshapes.lookup
  memory := state.memory
  memaddrs := state.memaddrs
  shMemaddrs := state.shMemaddrs
  clock := state.clock
  be := state.be
  ffi := state.ffi
  baseAddr := state.baseAddr
  topAddr := state.topAddr

/-- The forgetful projection lands in the finite-support subtype of the broad
    exact carrier. -/
theorem toExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    state.toExact.FiniteSupport :=
  ⟨state.locals.finiteSupport, state.globals.finiteSupport,
    state.code.finiteSupport, state.eshapes.finiteSupport⟩

/-- Rebuild the finite-support carrier from a broad exact state together with a
    finite-support proof: each unrestricted lookup function becomes a
    `HolFiniteMapExact` using the supplied witness.  This is the inverse of
    `toExact` on the finite-support subtype. -/
def ofExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (h : state.FiniteSupport) :
    PanSemStateFiniteExact width σ where
  locals := { lookup := state.locals, finiteSupport := h.1 }
  globals := { lookup := state.globals, finiteSupport := h.2.1 }
  structs := state.structs
  code := { lookup := state.code, finiteSupport := h.2.2.1 }
  eshapes := { lookup := state.eshapes, finiteSupport := h.2.2.2 }
  memory := state.memory
  memaddrs := state.memaddrs
  shMemaddrs := state.shMemaddrs
  clock := state.clock
  be := state.be
  ffi := state.ffi
  baseAddr := state.baseAddr
  topAddr := state.topAddr

/-- One roundtrip: `toExact` after `ofExact` is the identity on a finite-support
    broad state. -/
theorem toExact_ofExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (h : state.FiniteSupport) :
    (ofExact state h).toExact = state :=
  rfl

/-- The other roundtrip: `ofExact` after `toExact` is the identity on the
    finite-support carrier.  The `finiteSupport` proofs are propositionally
    irrelevant. -/
theorem ofExact_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    ofExact state.toExact state.toExact_finiteSupport = state := by
  cases state
  rfl

/-- Canonical global kernel witness for the `fmap_as_finite_support` `@[hol]`
    qualifier: the finite-support carrier is invertibly related to the broad
    exact one. Extensionality is the separate `HolFiniteMapExact.ext` theorem.
    The checker requires this
    declaration in the module of a `fmap_as_finite_support`-qualified tag. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  ⟨fun state h => toExact_ofExact state h, fun state => ofExact_toExact state⟩


/-- HOL `dec_clock_def` (`cakeml/pancake/semantics/panSemScript.sml:441-444`):
    `dec_clock s = s with clock := s.clock - 1`.  The body matches clause for
    clause; the state carrier's four finite-map fields (`locals`, `globals`,
    `code`, `eshapes`) are recorded by the `fmap_as_finite_support` qualifier. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "dec_clock_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
def decClockHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) : PanSemStateFiniteExact width σ :=
  { state with clock := state.clock - 1 }

/-- The finite-support dec-clock is compatible with the broad exact one. -/
@[simp] theorem toExact_decClockHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    state.decClockHOLFinite.toExact = decClockHOLExact state.toExact :=
  rfl

/-- HOL `fix_clock_def` (`cakeml/pancake/semantics/panSemScript.sml:446-449`):
    `fix_clock old_s (res, new_s) = (res, new_s with clock := if old_s.clock <
    new_s.clock then old_s.clock else new_s.clock)`.  The pair result and the
    clamped clock match clause for clause; the four finite-map fields are
    recorded by the `fmap_as_finite_support` qualifier. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "fix_clock_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
def fixClockHOLFinite {width : Nat} {σ : Type} [NeZero width] {β : Type}
    (oldState : PanSemStateFiniteExact width σ)
    (step : β × PanSemStateFiniteExact width σ) :
    β × PanSemStateFiniteExact width σ :=
  (step.1, { step.2 with
    clock := if oldState.clock < step.2.clock then oldState.clock else step.2.clock })

/-- The finite-support fix-clock is compatible with the broad exact one. -/
@[simp] theorem toExact_fixClockHOLFinite {width : Nat} {σ : Type} [NeZero width]
    {β : Type} (oldState : PanSemStateFiniteExact width σ)
    (step : β × PanSemStateFiniteExact width σ) :
    (fixClockHOLFinite oldState step).2.toExact =
      (fixClockHOLExact oldState.toExact (step.1, step.2.toExact)).2 :=
  rfl

/-- HOL `lookup_kvar_def` (`cakeml/pancake/semantics/panSemScript.sml:415-420`):
    `lookup_kvar vk v s = case vk of Local => FLOOKUP s.locals v | Global =>
    FLOOKUP s.globals v`.  The two branches match; `HolFiniteMapExact.lookup` is
    the standard Lean translation of `FLOOKUP` and the carrier's finite-map
    fields are recorded by the `fmap_as_finite_support` qualifier. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "lookup_kvar_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
def lookupKvarHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (state : PanSemStateFiniteExact width σ) :
    Option (ValueHOL width) :=
  match kind with
  | .local => state.locals.lookup name
  | .global => state.globals.lookup name

/-- The finite-support keyed-variable lookup is compatible with the broad exact
    one. -/
@[simp] theorem lookupKvarHOLFinite_eq {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (state : PanSemStateFiniteExact width σ) :
    lookupKvarHOLFinite kind name state =
      lookupKvarHOLExact kind name state.toExact := by
  cases kind <;> rfl

/-- HOL `is_valid_value_def` (`cakeml/pancake/semantics/panSemScript.sml:469-475`)
    over the finite-map state carrier. It performs the selected `FLOOKUP` and
    compares the two `shape_of` results; absent variables are invalid. The
    finite-map qualifier records the carrier translation used by
    `PanSemStateFiniteExact`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "is_valid_value_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
def isValidValueHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (kind : VarKind) (name : MlS)
    (value : ValueHOL width) : Bool :=
  match lookupKvarHOLFinite kind name state with
  | some existing => shapeEqHOL (shapeOfHOLExact value) (shapeOfHOLExact existing)
  | none => false

/-- Finite-map and broad lookup renderings agree on a finite carrier state. -/
@[simp] theorem isValidValueHOLFinite_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ) (kind : VarKind)
    (name : MlS) (value : ValueHOL width) :
    isValidValueHOLFinite state kind name value =
      isValidValueHOLExact state.toExact kind name value := by
  unfold isValidValueHOLFinite isValidValueHOLExact
    lookupKvarHOLFinite lookupKvarHOLExact
  cases kind <;> rfl

/-- HOL `set_var_def` (`cakeml/pancake/semantics/panSemScript.sml:398-401`):
    `set_var v value s = s with locals := s.locals |+ (v,value)`.  The `|+`
    (FUPDATE) is the canonical `HolFiniteMapExact.update` on the finite-support
    carrier.  The `locals`/`globals`/`code`/`eshapes` fields are the canonical
    finite-map representation, recorded by the `fmap_as_finite_support`
    qualifier (canonical witness `holFmapAsFiniteSupportWitness` in this
    module). -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "set_var_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
def setVarHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateFiniteExact width σ) :
    PanSemStateFiniteExact width σ :=
  { state with locals := state.locals.update (name, value) }

/-- HOL `set_global_def` (`cakeml/pancake/semantics/panSemScript.sml:403-406`):
    `set_global v value s = s with globals := s.globals |+ (v,value)`, i.e. the
    canonical `HolFiniteMapExact.update` on the `globals` component.  Its
    finite-map fields are recorded by the `fmap_as_finite_support` qualifier
    (canonical witness `holFmapAsFiniteSupportWitness` in this module). -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "set_global_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
def setGlobalHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateFiniteExact width σ) :
    PanSemStateFiniteExact width σ :=
  { state with globals := state.globals.update (name, value) }

/-- HOL `set_kvar_def` (`cakeml/pancake/semantics/panSemScript.sml:408-413`):
    `set_kvar vk v value s = case vk of Local => set_var v value s
    | Global => set_global v value s`.  Body-exact over `PanSemStateFiniteExact`
    via the canonical-update wrappers above.  The `locals`/`globals`/`code`/
    `eshapes` fields are the canonical finite-map representation, recorded by the
    `fmap_as_finite_support` qualifier. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "set_kvar_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
def setKvarHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (value : ValueHOL width)
    (state : PanSemStateFiniteExact width σ) : PanSemStateFiniteExact width σ :=
  match kind with
  | .local => setVarHOLFinite name value state
  | .global => setGlobalHOLFinite name value state

/-- The finite-support keyed-variable write is compatible with the broad exact
    one. -/
@[simp] theorem toExact_setKvarHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (value : ValueHOL width)
    (state : PanSemStateFiniteExact width σ) :
    (setKvarHOLFinite kind name value state).toExact =
      setKvarHOLExact kind name value state.toExact := by
  cases kind
  · simp only [setKvarHOLFinite, setVarHOLFinite, setKvarHOLExact,
      PanSemStateFiniteExact.toExact]
    rw [HolFiniteMapExact.lookup_update_pointwise]
  · simp only [setKvarHOLFinite, setGlobalHOLFinite, setKvarHOLExact,
      PanSemStateFiniteExact.toExact]
    rw [HolFiniteMapExact.lookup_update_pointwise]

/-- HOL `empty_locals_def` (`cakeml/pancake/semantics/panSemScript.sml:437-439`):
    `empty_locals s = s with locals := FEMPTY`.  The cleared `locals` is the
    canonical empty finite map (`HolFiniteMapExact.empty`); the carrier's
    finite-map fields are recorded by the `fmap_as_finite_support` qualifier. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "empty_locals_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
def emptyLocalsHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) : PanSemStateFiniteExact width σ :=
  { state with
    locals :=
      { lookup := fun _ => none
        finiteSupport := ⟨[], by intro key hkey; exact absurd rfl hkey⟩ } }

/-- The finite-support locals-clearing is compatible with the broad exact
    one. -/
@[simp] theorem toExact_emptyLocalsHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    (emptyLocalsHOLFinite state).toExact = emptyLocalsHOLExact state.toExact :=
  rfl

/-- Flapjack-specific composition of finite-map `set_kvar` with the FFI field
    update used by a successful shared-memory read. HOL has no standalone
    declaration for this composed helper; `sh_mem_load_def` names the two
    operations separately. -/
def setKvarFfiHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (value : ValueHOL width)
    (state : PanSemStateFiniteExact width σ) (newFfi : HolFfiState σ) :
    PanSemStateFiniteExact width σ :=
  { setKvarHOLFinite kind name value state with ffi := newFfi }

/-- Flapjack-specific projection bridge for `setKvarFfiHOLFinite`; it has no
    standalone HOL declaration because it only packages two state updates. -/
@[simp] theorem toExact_setKvarFfiHOLFinite {width : Nat} {σ : Type}
    [NeZero width] (kind : VarKind) (name : MlS) (value : ValueHOL width)
    (state : PanSemStateFiniteExact width σ) (newFfi : HolFfiState σ) :
    (setKvarFfiHOLFinite kind name value state newFfi).toExact =
      { setKvarHOLExact kind name value state.toExact with ffi := newFfi } := by
  change { (setKvarHOLFinite kind name value state).toExact with ffi := newFfi } = _
  rw [toExact_setKvarHOLFinite]

/-- HOL `sh_mem_load_def` (`cakeml/pancake/semantics/panSemScript.sml:510-527`)
    over the finite-map state carrier. The branches follow HOL directly: test
    the raw address when `nb = 0`, otherwise the byte-aligned address; call
    `call_FFI` with `SharedMem MappedRead`, `[n2w nb]`, and
    `word_to_bytes addr F`; on `FFI_final`, clear locals; on `FFI_return`,
    install the loaded word with `set_kvar` and update only `ffi`. The four
    map fields use the canonical finite-support carrier recorded by the tag. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "sh_mem_load_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
def shMemLoadHOLFiniteExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [DecidablePred state.shMemaddrs]
    (kind : VarKind) (name : MlS) (address : RiscV.Word width) (nb : Nat) :
    Option (PanSemResultExact width) × PanSemStateFiniteExact width σ :=
  if nb = 0 then
    if state.shMemaddrs address then
      match callFFIHOL state.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          (panWordToBytesHOL address false) with
      | .final event => (some (.finalFfi event), emptyLocalsHOLFinite state)
      | .ret newFfi newBytes =>
          (none, setKvarFfiHOLFinite kind name
            (.val (.word (panWordOfBytesHOL false 0 newBytes))) state newFfi)
    else (some .error, state)
  else
    if state.shMemaddrs (panByteAlignHOL address) then
      match callFFIHOL state.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          (panWordToBytesHOL address false) with
      | .final event => (some (.finalFfi event), emptyLocalsHOLFinite state)
      | .ret newFfi newBytes =>
          (none, setKvarFfiHOLFinite kind name
            (.val (.word (panWordOfBytesHOL false 0 newBytes))) state newFfi)
    else (some .error, state)

/-- Flapjack-specific representation bridge, not a separate HOL declaration:
    forgetting finite-map support after the direct finite-carrier load gives
    the broad helper's result on the same finite input. -/
theorem shMemLoadHOLFiniteExact_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [DecidablePred state.shMemaddrs]
    (kind : VarKind) (name : MlS) (address : RiscV.Word width) (nb : Nat) :
    let loaded := shMemLoadHOLFiniteExact state kind name address nb
    (loaded.1, loaded.2.toExact) =
      shMemLoadHOLExact state.toExact kind name address nb := by
  classical
  by_cases hnb : nb = 0
  · subst nb
    by_cases haddr : state.shMemaddrs address
    · cases hffi : callFFIHOL state.ffi (.sharedMem .mappedRead)
          [BitVec.ofNat 8 0]
          (panWordToBytesHOL address false) with
      | final event =>
          simp [shMemLoadHOLFiniteExact, shMemLoadHOLExact, haddr, hffi]
      | ret newFfi newBytes =>
          simp [shMemLoadHOLFiniteExact, shMemLoadHOLExact, haddr, hffi]
    · simp [shMemLoadHOLFiniteExact, shMemLoadHOLExact, haddr]
  · by_cases haddr : state.shMemaddrs (panByteAlignHOL address)
    · cases hffi : callFFIHOL state.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          (panWordToBytesHOL address false) with
      | final event =>
          simp [shMemLoadHOLFiniteExact, shMemLoadHOLExact, hnb, haddr, hffi]
      | ret newFfi newBytes =>
          simp [shMemLoadHOLFiniteExact, shMemLoadHOLExact, hnb, haddr, hffi]
    · simp [shMemLoadHOLFiniteExact, shMemLoadHOLExact, hnb, haddr]

/-- Flapjack-specific proof-irrelevance bridge for the finite/broad carrier
    roundtrip. HOL has no declaration for this proof plumbing. -/
private theorem ofExact_eq_finite_of_toExact_eq {width : Nat} {σ : Type}
    [NeZero width] (broad : PanSemStateExact width σ)
    (finite : PanSemStateFiniteExact width σ) (h : broad = finite.toExact)
    (support : broad.FiniteSupport) :
    ofExact broad support = finite := by
  cases h
  exact ofExact_toExact finite

/-- Flapjack-specific representation bridge, not a separate HOL declaration:
    rebuilding the broad load result with its finite-support proof gives the
    direct finite-carrier helper's result. -/
theorem shMemLoadHOLFiniteExact_repack {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [DecidablePred state.shMemaddrs]
    (kind : VarKind) (name : MlS) (address : RiscV.Word width) (nb : Nat) :
    let loaded := shMemLoadHOLFiniteExact state kind name address nb
    let broad := shMemLoadHOLExact state.toExact kind name address nb
    (broad.1, ofExact broad.2
    (shMemLoadHOLExact_finiteSupport state.toExact kind name address nb
        state.toExact_finiteSupport)) = (loaded.1, loaded.2) := by
  have h := shMemLoadHOLFiniteExact_toExact state kind name address nb
  dsimp only at h
  apply Prod.ext
  · exact (congrArg Prod.fst h).symm
  · have hsnd :
        (shMemLoadHOLExact state.toExact kind name address nb).2 =
          (shMemLoadHOLFiniteExact state kind name address nb).2.toExact :=
      (congrArg Prod.snd h).symm
    exact ofExact_eq_finite_of_toExact_eq _ _ hsnd
      (shMemLoadHOLExact_finiteSupport state.toExact kind name address nb
        state.toExact_finiteSupport)

/-- Flapjack-specific repack bridge for the ExtCall return state: rebuilding the
broad carrier after updating only `memory` and `ffi` with a finite-support proof
gives the direct finite-carrier record update. HOL has no declaration for this
representation plumbing (the two carriers are the same underlying data). -/
theorem ofExact_update_memory_ffi {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (memory : RiscV.Word width → HolWordLab width) (ffi : HolFfiState σ)
    (support :
      ({ state.toExact with memory := memory, ffi := ffi } : PanSemStateExact width σ).FiniteSupport) :
    PanSemStateFiniteExact.ofExact { state.toExact with memory := memory, ffi := ffi } support =
      { state with memory := memory, ffi := ffi } :=
  ofExact_eq_finite_of_toExact_eq _ _ (by rfl) support

/-- The finite-support local write is compatible with the broad exact one. -/
@[simp] theorem toExact_setVarHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateFiniteExact width σ) :
    (setVarHOLFinite name value state).toExact = setVarHOLExact name value state.toExact := by
  simp only [setVarHOLFinite, setVarHOLExact, PanSemStateFiniteExact.toExact]
  rw [HolFiniteMapExact.lookup_update_pointwise]

/-- The finite-support global write is compatible with the broad exact one. -/
@[simp] theorem toExact_setGlobalHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateFiniteExact width σ) :
    (setGlobalHOLFinite name value state).toExact = setGlobalHOLExact name value state.toExact := by
  simp only [setGlobalHOLFinite, setGlobalHOLExact, PanSemStateFiniteExact.toExact]
  rw [HolFiniteMapExact.lookup_update_pointwise]

/-- The finite-support local restore is compatible with the broad exact one. -/
@[simp] theorem lookup_resVarEq_toExact {width : Nat} [NeZero width]
    (map : HolFiniteMapExact MlS (ValueHOL width))
    (entry : MlS × Option (ValueHOL width)) :
    (HolFiniteMapExact.resVarEq map entry).lookup = resVarHOLExact map.lookup entry := by
  obtain ⟨key, valueOpt⟩ := entry
  cases valueOpt with
  | none =>
      funext current
      simp only [HolFiniteMapExact.resVarEq, resVarHOLExact,
        HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL]
  | some value =>
      funext current
      simp only [HolFiniteMapExact.resVarEq, resVarHOLExact,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

/-- A finite-support local `resVarEq` record update is compatible with the broad
    exact one.  This bridges the `Dec` clause's restored state. -/
@[simp] theorem toExact_resVarEq_locals {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (entry : MlS × Option (ValueHOL width)) :
    ({ state with locals := HolFiniteMapExact.resVarEq state.locals entry } :
        PanSemStateFiniteExact width σ).toExact =
      { state.toExact with locals := resVarHOLExact state.toExact.locals entry } := by
  simp only [PanSemStateFiniteExact.toExact, lookup_resVarEq_toExact]

/-- A finite-support plain `locals` record update is compatible with the broad
    exact one.  This bridges the `Call`/`DecCall` caller-locals restore. -/
@[simp] theorem toExact_setLocals {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (locals : HolFiniteMapExact MlS (ValueHOL width)) :
    ({ state with locals := locals } : PanSemStateFiniteExact width σ).toExact =
      { state.toExact with locals := locals.lookup } := by
  cases state
  rfl

/-- A combined finite `locals`/`clock` record update is compatible with the broad
    exact one.  This bridges the `Call`/`DecCall` entry state. -/
@[simp] theorem toExact_setLocals_clock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (clock : Nat) :
    ({ state with locals := locals, clock := clock } :
        PanSemStateFiniteExact width σ).toExact =
      { state.toExact with locals := locals.lookup, clock := clock } := by
  cases state
  rfl

/-- HOL `eval_def` (`cakeml/pancake/semantics/panSemScript.sml:209-283`) over the
    finite-support state carrier.  The body delegates to the exact broad
    evaluator through the canonical translation `toExact`; it does NOT
    syntactically present HOL's clause-shaped definition body.  The clause-shaped
    equations in `Flapjack/Pancake/Semantics/PanSem/EvalFinite.lean` expose each
    of the fifteen HOL clauses one by one over this carrier, and the state's four
    finite-map fields (`locals`, `globals`, `code`, `eshapes`) are recorded by the
    `fmap_as_finite_support` qualifier (canonical `HolFiniteMapExact`
    translation, witness `holFmapAsFiniteSupportWitness`). -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "eval_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
def evalHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    ExpHOL width → Option (ValueHOL width) :=
  @evalHOLExact width σ _ state.toExact h

/-- FLAPJACK-SPECIFIC provisional rendering (no `@[hol]` tag): HOL
    `eval_upd_clock_eq` (`cakeml/pancake/semantics/panPropsScript.sml:645`) is a
    PanProps declaration, so its HOL port belongs in the PanProps counterpart
    module, not this PanSem module (coordinator HOLD 2026-09-26T16:46Z). The tag
    was withdrawn pending relocation. `eval (t with clock := ck) e = eval t e`
    still holds here over the finite-support state carrier; the evaluator never
    inspects `clock`, and the untagged broad-carrier support is
    `evalHOLExact_upd_clock_eq`. -/
theorem evalHOLFinite_upd_clock_eq {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (ck : Nat) (e : ExpHOL width) :
    evalHOLFinite { state with clock := ck } e = evalHOLFinite state e := by
  simp only [evalHOLFinite]
  exact evalHOLExact_upd_clock_eq state.toExact e ck

/-- FLAPJACK-SPECIFIC provisional rendering (no `@[hol]` tag): HOL
    `eval_upd_code_eq` (`cakeml/pancake/semantics/panPropsScript.sml:654`) is a
    PanProps declaration, so its HOL port belongs in the PanProps counterpart
    module, not this PanSem module (coordinator HOLD 2026-09-26T16:46Z). The tag
    was withdrawn pending relocation. `eval (t with code := code) e = eval t e`
    still holds here; the evaluator never inspects `code`, and the untagged
    broad-carrier support is `evalHOLExact_upd_code_eq`. -/
theorem evalHOLFinite_upd_code_eq {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (e : ExpHOL width) :
    evalHOLFinite { state with code := code } e = evalHOLFinite state e := by
  simp only [evalHOLFinite]
  exact evalHOLExact_upd_code_eq state.toExact e code.lookup

/-- FLAPJACK-SPECIFIC provisional rendering (no `@[hol]` tag): HOL
    `eval_upd_eshapes_eq` (`cakeml/pancake/semantics/panPropsScript.sml:663`) is a
    PanProps declaration, so its HOL port belongs in the PanProps counterpart
    module, not this PanSem module (coordinator HOLD 2026-09-26T16:46Z). The tag
    was withdrawn pending relocation. `eval (t with eshapes := esh) e = eval t e`
    still holds here; the evaluator never inspects `eshapes`, and the untagged
    broad-carrier support is `evalHOLExact_upd_eshapes_eq`. -/
theorem evalHOLFinite_upd_eshapes_eq {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (es : HolFiniteMapExact MlS ShapeHOL) (e : ExpHOL width) :
    evalHOLFinite { state with eshapes := es } e = evalHOLFinite state e := by
  simp only [evalHOLFinite]
  exact evalHOLExact_upd_eshapes_eq state.toExact e es.lookup

/-- Finite-support carrier rendering of the `OPT_MMAP eval` list step; delegates
    through `toExact` (untagged helper, not a HOL declaration). -/
def evalListHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    List (ExpHOL width) → Option (List (ValueHOL width)) :=
  @evalListHOLExact width σ _ state.toExact h

/-- Finite-support carrier rendering of the named-struct field-expression step;
    delegates through `toExact` (untagged helper, not a HOL declaration). -/
def evalListFieldsHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    List (MlS × ExpHOL width) → Option (List (MlS × ValueHOL width)) :=
  @evalListFieldsHOLExact width σ _ state.toExact h

/-- Projection equality: the tagged finite-support evaluator is the broad exact
    evaluator applied to `toExact`, i.e. the canonical translation is used. -/
@[simp] theorem evalHOLFinite_eq_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (expression : ExpHOL width) :
    state.evalHOLFinite expression =
      @evalHOLExact width σ _ state.toExact h expression := rfl

@[simp] theorem evalListHOLFinite_eq_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (expressions : List (ExpHOL width)) :
    state.evalListHOLFinite expressions =
      @evalListHOLExact width σ _ state.toExact h expressions := rfl

@[simp] theorem evalListFieldsHOLFinite_eq_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (fields : List (MlS × ExpHOL width)) :
    state.evalListFieldsHOLFinite fields =
      @evalListFieldsHOLExact width σ _ state.toExact h fields := rfl

/-- FLAPJACK-SPECIFIC ADAPTER (not itself the tagged HOL `evaluate_def` port):
    it runs the broad, context-returning exact evaluator
    `evalPanSemRecursiveCallContextHOLExact` on the forgetful projection
    `toExact`, then rebuilds the resulting state as a finite-support value via
    `ofExact`, using the result-state preservation theorem
    `evalPanSemRecursiveCallContextHOLExact_finiteSupport`.  Because it returns
    the assembly-marked `Option (Option PanSemResultExact × state)` pair and
    reconstructs the state through `ofExact`, this declaration is deliberately
    untagged.  A faithful tagged `evaluate_def` port over the finite-support
    carrier requires a finite eval context that threads
    `memaddrsDecidable`/`shMemaddrsDecidable`; tracked by `flapjack-6yq`. -/
def evalPanSemRecursiveCallHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    ProgHOL width →
      Option (Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
  | program =>
      match hres : evalPanSemRecursiveCallContextHOLExact program
          { state := state.toExact
            memaddrsDecidable := h
            shMemaddrsDecidable := hshared } with
      | none => none
      | some pair =>
          some (pair.1,
            ofExact pair.2.state
              (evalPanSemRecursiveCallContextHOLExact_finiteSupport program
                { state := state.toExact
                  memaddrsDecidable := h
                  shMemaddrsDecidable := hshared }
                state.toExact_finiteSupport pair hres))

/-- Projecting the finite recursive evaluator back through `toExact` recovers the
    broad exact evaluator, so the wrapper uses the canonical finite-map
    translation of the state carrier. -/
theorem evalPanSemRecursiveCallHOLFinite_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width) :
    (evalPanSemRecursiveCallHOLFinite state program).map
        (fun pair => (pair.1, pair.2.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact program
        { state := state.toExact
          memaddrsDecidable := h
          shMemaddrsDecidable := hshared }).map
        (fun pair => (pair.1, pair.2.state)) := by
  unfold evalPanSemRecursiveCallHOLFinite
  dsimp only
  split <;> simp_all only [Option.map_some, toExact_ofExact] <;> rfl

/-- The finite-support recursive evaluator is total: its assembly marker is
    always `some`, so it is a genuine `result × post-state` evaluator over the
    exact finite-map state carrier. -/
theorem evalPanSemRecursiveCallHOLFinite_exists {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width) :
    ∃ pair, evalPanSemRecursiveCallHOLFinite state program = some pair := by
  obtain ⟨output, houtput⟩ :=
    evalPanSemRecursiveCallContextHOLExact_total program
      { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }
  cases hv : evalPanSemRecursiveCallHOLFinite state program with
  | none =>
      have hproj := evalPanSemRecursiveCallHOLFinite_toExact state program
      rw [hv] at hproj
      simp only [Option.map_none] at hproj
      rw [houtput] at hproj
      simp at hproj
  | some pair => exact ⟨pair, rfl⟩

/-- Finite-support projection of the reviewed nonrecursive `evaluate_def` clause
    dispatcher `evalPanSemNonrecursiveHOLExact`: it runs the dispatcher on
    `state.toExact` and rebuilds the post-state as a finite-support value using
    `evalPanSemNonrecursiveHOLExact_finiteSupport`. -/
def evalPanSemNonrecursiveHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width) :
    Option (Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) :=
  match hres : evalPanSemNonrecursiveHOLExact program state.toExact with
  | none => none
  | some pair =>
      some (pair.1, ofExact pair.2
        (evalPanSemNonrecursiveHOLExact_finiteSupport program state.toExact
          state.toExact_finiteSupport pair hres))

/-- Forgetting the finite support of the finite nonrecursive dispatcher recovers
    the broad exact dispatcher transported along `toExact`. -/
theorem evalPanSemNonrecursiveHOLFinite_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width) :
    (evalPanSemNonrecursiveHOLFinite state program).map
        (fun pair => (pair.1, pair.2.toExact)) =
      (evalPanSemNonrecursiveHOLExact program state.toExact).map
        (fun pair => (pair.1, pair.2)) := by
  unfold evalPanSemNonrecursiveHOLFinite
  split <;> simp_all only [Option.map_some, toExact_ofExact] <;> rfl

/-- Flapjack-specific finite-carrier invariant: the nonrecursive dispatcher
    preserves `memaddrs`, with the post-state rebuilt through `ofExact`.
    HOL has no standalone declaration for this adapter theorem. -/
theorem evalPanSemNonrecursiveHOLFinite_memaddrs {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width)
    (output : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
    (hout : evalPanSemNonrecursiveHOLFinite state program = some output) :
    output.2.memaddrs = state.memaddrs := by
  unfold evalPanSemNonrecursiveHOLFinite at hout
  split at hout
  · simp at hout
  · rename_i pair hres
    simp only [Option.some.injEq] at hout
    subst hout
    have hpair := evalPanSemNonrecursiveHOLExact_memaddrs program state.toExact pair hres
    change pair.2.memaddrs = state.toExact.memaddrs
    exact hpair

/-- Flapjack-specific finite-carrier `shMemaddrs` preservation theorem for the
    nonrecursive dispatcher; no standalone HOL declaration has this shape. -/
theorem evalPanSemNonrecursiveHOLFinite_shMemaddrs {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width)
    (output : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
    (hout : evalPanSemNonrecursiveHOLFinite state program = some output) :
    output.2.shMemaddrs = state.shMemaddrs := by
  unfold evalPanSemNonrecursiveHOLFinite at hout
  split at hout
  · simp at hout
  · rename_i pair hres
    simp only [Option.some.injEq] at hout
    subst hout
    have hpair := evalPanSemNonrecursiveHOLExact_shMemaddrs program state.toExact pair hres
    change pair.2.shMemaddrs = state.toExact.shMemaddrs
    exact hpair

/-- Finite nonrecursive dispatcher on `Skip`. -/
@[simp] theorem evalPanSemNonrecursiveHOLFinite_skip {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evalPanSemNonrecursiveHOLFinite state (.skip : ProgHOL width) = some (none, state) := by
  unfold evalPanSemNonrecursiveHOLFinite
  simp [evalPanSemNonrecursiveHOLExact, ofExact_toExact]

/-- Finite nonrecursive dispatcher on `Break`. -/
@[simp] theorem evalPanSemNonrecursiveHOLFinite_break {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evalPanSemNonrecursiveHOLFinite state (.break : ProgHOL width) =
      some (some .break, state) := by
  unfold evalPanSemNonrecursiveHOLFinite
  simp [evalPanSemNonrecursiveHOLExact, ofExact_toExact]

/-- Finite nonrecursive dispatcher on `Continue`. -/
@[simp] theorem evalPanSemNonrecursiveHOLFinite_continue {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evalPanSemNonrecursiveHOLFinite state (.continue : ProgHOL width) =
      some (some .continue, state) := by
  unfold evalPanSemNonrecursiveHOLFinite
  simp [evalPanSemNonrecursiveHOLExact, ofExact_toExact]

/-- FLAPJACK-SPECIFIC (not the tagged HOL `evaluate_def` port): finite-support
    rendering of HOL `evaluate` (`cakeml/pancake/semantics/panSemScript.sml:556`)
    returning a genuine `result option × state` pair.  The body extracts the
    total finite-support recursive evaluator `evalPanSemRecursiveCallHOLFinite`
    (its outer assembly marker is always `some`, so the assembly `Option` is
    dropped).  It is deliberately untagged: the body delegates through
    `toExact`, so it does not syntactically present HOL's clause-shaped body,
    and the delegating wrapper exposes only the Skip/Break/Continue equations
    uniformly, not the six recursive HOL clauses.  The faithful tagged port
    requires threading `memaddrsDecidable`/`shMemaddrsDecidable` through a
    finite eval context; tracked by `flapjack-6yq` (which blocks
    `flapjack-qj5`). -/
def evaluateHOLFiniteViaExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    ProgHOL width →
      Option (PanSemResultExact width) × PanSemStateFiniteExact width σ
  | program =>
      match evalPanSemRecursiveCallHOLFinite state program with
      | some pair => pair
      | none => (none, state)

/-- Result bridge: the finite evaluator is exactly the `some` output of
    the total finite-support recursive evaluator, so it is the canonical
    finite-map rendering of HOL `evaluate` (Flapjack-specific, untagged). -/
theorem evaluateHOLFiniteViaExact_eq_some {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width) :
    evalPanSemRecursiveCallHOLFinite state program =
      some (evaluateHOLFiniteViaExact state program) := by
  obtain ⟨pair, hp⟩ := evalPanSemRecursiveCallHOLFinite_exists state program
  unfold evaluateHOLFiniteViaExact
  simp only [hp]

/-- Projection bridge: forgetting the finite support of the finite evaluator's
    post-state recovers the broad exact evaluator's output, transported along
    `toExact`. -/
theorem evaluateHOLFiniteViaExact_snd_toExact_eq {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width) :
    ∃ pair,
      evalPanSemRecursiveCallHOLFinite state program = some pair ∧
        evaluateHOLFiniteViaExact state program = pair ∧
          (Prod.snd (evaluateHOLFiniteViaExact state program)).toExact = pair.2.toExact := by
  obtain ⟨pair, hp⟩ := evalPanSemRecursiveCallHOLFinite_exists state program
  have heq : evaluateHOLFiniteViaExact state program = pair := by
    unfold evaluateHOLFiniteViaExact
    simp only [hp]
  exact ⟨pair, hp, heq, by rw [heq]⟩

/-- FLAPJACK-SPECIFIC helper (not a HOL declaration): the finite-support code
    lookup.  It wraps `lookupCodeHOLExact`'s callee-local function as a
    `HolFiniteMapExact`, so the finite evaluator can bind the lookup result in a
    plain `match` instead of a dependent `match hlookup : ...` (whose equation
    blocks the projection proofs). -/
def lookupCodeHOLFinite {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (fname : MlS) (values : List (ValueHOL width)) :
    Option (ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL) :=
  match h : lookupCodeHOLExact code fname values with
  | none => none
  | some (body, calleeLocals, returnShape) =>
      some (body,
        { lookup := calleeLocals,
          finiteSupport := lookupCodeHOLExact_calleeLocals_finiteSupport
            code fname values body calleeLocals returnShape h },
        returnShape)

/-- `lookupCodeHOLFinite` fails exactly when the underlying HOL lookup fails. -/
theorem lookupCodeHOLFinite_eq_none_iff {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (fname : MlS) (values : List (ValueHOL width)) :
    lookupCodeHOLFinite code fname values = none ↔
      lookupCodeHOLExact code fname values = none := by
  unfold lookupCodeHOLFinite
  split <;> simp_all

/-- A successful `lookupCodeHOLFinite` forgets to the underlying HOL lookup
    result (the callee map is projected through `.lookup`). -/
theorem lookupCodeHOLFinite_eq_some {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (fname : MlS) (values : List (ValueHOL width)) (body : ProgHOL width)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
    (h : lookupCodeHOLFinite code fname values = some (body, callee, returnShape)) :
    lookupCodeHOLExact code fname values = some (body, callee.lookup, returnShape) := by
  unfold lookupCodeHOLFinite at h
  split at h
  · simp at h
  · rename_i heq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hb, hcallee, hrs⟩ := h
    rw [hb, hrs] at heq
    subst hcallee
    simpa using heq

/-- FLAPJACK-SPECIFIC evaluation context threading the decidability of the two
    address-domain predicates through the recursive finite evaluator.  Mirroring
    `PanSemExactEvalContext`, this is required because a recursive result state
    is opaque, so its `DecidablePred` instances cannot be reconstructed by
    computation.  Not a HOL declaration. -/
structure FiniteEvalContext (width : Nat) (σ : Type) [NeZero width] where
  state : PanSemStateFiniteExact width σ
  memaddrsDecidable : DecidablePred state.memaddrs
  shMemaddrsDecidable : DecidablePred state.shMemaddrs

namespace FiniteEvalContext

/-- Transport an evaluation context across a state whose two address-domain
    predicates are definitionally the same as the old state's. -/
def withState {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) (state : PanSemStateFiniteExact width σ)
    (hmem : state.memaddrs = context.state.memaddrs)
    (hshared : state.shMemaddrs = context.state.shMemaddrs) : FiniteEvalContext width σ :=
  { state := state
    memaddrsDecidable := fun address => by rw [hmem]; exact context.memaddrsDecidable address
    shMemaddrsDecidable := fun address => by rw [hshared]; exact context.shMemaddrsDecidable address }

@[simp] theorem withState_state {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) (state : PanSemStateFiniteExact width σ)
    (hmem : state.memaddrs = context.state.memaddrs)
    (hshared : state.shMemaddrs = context.state.shMemaddrs) :
    (withState context state hmem hshared).state = state := rfl

/-- Threading a context through its own state is the identity. -/
@[simp] theorem withState_self {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ)
    (hmem : context.state.memaddrs = context.state.memaddrs)
    (hshared : context.state.shMemaddrs = context.state.shMemaddrs) :
    context.withState context.state hmem hshared = context := by
  cases context
  simp [FiniteEvalContext.withState]

/-- `withState` is independent of the particular equality proofs. -/
theorem withState_congr {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) (state : PanSemStateFiniteExact width σ)
    (h1 h1' : state.memaddrs = context.state.memaddrs)
    (h2 h2' : state.shMemaddrs = context.state.shMemaddrs) :
    withState context state h1 h2 = withState context state h1' h2' := by
  cases context
  simp only [withState]

/-- FLAPJACK-SPECIFIC context constructor for HOL DecCall timeout: clearing
    locals preserves both address domains, and naming those proofs keeps the
    generated DecCall equation from synthesizing dependent `withState` proof
    arguments against the wrong state endpoint. -/
def emptyLocalsContextHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) : FiniteEvalContext width σ :=
  context.withState (emptyLocalsHOLFinite context.state) (by rfl) (by rfl)

@[simp] theorem emptyLocalsContextHOLFinite_state {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) :
    (emptyLocalsContextHOLFinite context).state = emptyLocalsHOLFinite context.state := rfl

/-- FLAPJACK-SPECIFIC (not a HOL declaration): forgetful projection of a finite
    evaluation context to the exact (unrestricted-map) evaluation context, by
    translating the state through `toExact` and reusing the two address-domain
    deciders.  This is the context-level relation used to relate the finite
    evaluator to `evalPanSemRecursiveCallContextHOLExact`. -/
def toExact {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) : PanSemExactEvalContext width σ :=
  { state := context.state.toExact
    memaddrsDecidable := context.memaddrsDecidable
    shMemaddrsDecidable := context.shMemaddrsDecidable }

@[simp] theorem toExact_emptyLocalsContextHOLFinite {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) :
    (emptyLocalsContextHOLFinite context).toExact =
      PanSemExactEvalContext.emptyLocalsContextHOLExact context.toExact := by
  apply PanSemExactEvalContext.ext
  change (emptyLocalsHOLFinite context.state).toExact =
    emptyLocalsHOLExact context.state.toExact
  exact toExact_emptyLocalsHOLFinite context.state

/-- `toExact` commutes with `withState`. -/
@[simp] theorem toExact_withState {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) (state : PanSemStateFiniteExact width σ)
    (hmem : state.memaddrs = context.state.memaddrs)
    (hshared : state.shMemaddrs = context.state.shMemaddrs) :
    (withState context state hmem hshared).toExact =
      context.toExact.withState state.toExact hmem hshared := by
  cases context
  rfl

/-- FLAPJACK-SPECIFIC (not a HOL declaration): the finite `Call`/`DecCall` entry
    context (entry state `{ state with clock := state.clock - 1, locals := callee }`)
    projects to the broad exact entry context.  This names the otherwise head-only
    let-bound `entryContext` occurrence so the `Call`/`DecCall` projection proofs
    can rewrite it without touching the evaluator or its `decreasing_by`. -/
@[simp] theorem toExact_callEntryContext {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) :
    (context.withState
        ({ context.state with clock := context.state.clock - 1, locals := callee } :
          PanSemStateFiniteExact width σ) rfl rfl).toExact =
      context.toExact.withState
        ({ context.state.toExact with clock := context.state.clock - 1, locals := callee.lookup } : PanSemStateExact width σ) rfl rfl := by
  cases context
  rfl

/-- FLAPJACK-SPECIFIC (not a HOL declaration): same bridge as
    `toExact_callEntryContext`, stated with the record-literal form the
    `Call`/`DecCall` clause equations zeta-reduce to on the broad side, so the
    projection proofs can rewrite the otherwise unnameable let-bound entry
    context.  Written this way because the broad occurrence is not syntactically
    the record-update form. -/
theorem toExact_callEntryContext_eq {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ)
    (callee : HolFiniteMapExact MlS (ValueHOL width))
    (p1 : ({ locals := callee.lookup, globals := context.toExact.state.globals, structs := context.toExact.state.structs, code := context.state.code.lookup, eshapes := context.toExact.state.eshapes, memory := context.toExact.state.memory, memaddrs := context.toExact.state.memaddrs, shMemaddrs := context.toExact.state.shMemaddrs, clock := context.toExact.state.clock - 1, be := context.toExact.state.be, ffi := context.toExact.state.ffi, baseAddr := context.toExact.state.baseAddr, topAddr := context.toExact.state.topAddr } : PanSemStateExact width σ).memaddrs = context.toExact.state.memaddrs)
    (p2 : ({ locals := callee.lookup, globals := context.toExact.state.globals, structs := context.toExact.state.structs, code := context.state.code.lookup, eshapes := context.toExact.state.eshapes, memory := context.toExact.state.memory, memaddrs := context.toExact.state.memaddrs, shMemaddrs := context.toExact.state.shMemaddrs, clock := context.toExact.state.clock - 1, be := context.toExact.state.be, ffi := context.toExact.state.ffi, baseAddr := context.toExact.state.baseAddr, topAddr := context.toExact.state.topAddr } : PanSemStateExact width σ).shMemaddrs = context.toExact.state.shMemaddrs) :
    context.toExact.withState
        ({ locals := callee.lookup, globals := context.toExact.state.globals, structs := context.toExact.state.structs, code := context.state.code.lookup, eshapes := context.toExact.state.eshapes, memory := context.toExact.state.memory, memaddrs := context.toExact.state.memaddrs, shMemaddrs := context.toExact.state.shMemaddrs, clock := context.toExact.state.clock - 1, be := context.toExact.state.be, ffi := context.toExact.state.ffi, baseAddr := context.toExact.state.baseAddr, topAddr := context.toExact.state.topAddr } : PanSemStateExact width σ) p1 p2 =
      (context.withState
        ({ context.state with clock := context.state.clock - 1, locals := callee } :
          PanSemStateFiniteExact width σ) rfl rfl).toExact := by
  apply PanSemExactEvalContext.ext
  cases context
  rfl

/-- FLAPJACK-SPECIFIC (not a HOL declaration): the record-update form of the
    `Call`/`DecCall` entry-context bridge.  The `Call`/`DecCall` projection proofs
    see the broad entry context as the record update `{ context.toExact.state with
    ... }` rather than the explicit literal used by `toExact_callEntryContext_eq`,
    so this restatement is needed to rewrite that occurrence. -/
theorem toExact_callEntryContext_state {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (p1 : ({ context.toExact.state with clock := context.toExact.state.clock - 1, locals := callee.lookup } : PanSemStateExact width σ).memaddrs = context.toExact.state.memaddrs)
    (p2 : ({ context.toExact.state with clock := context.toExact.state.clock - 1, locals := callee.lookup } : PanSemStateExact width σ).shMemaddrs = context.toExact.state.shMemaddrs) :
    context.toExact.withState ({ context.toExact.state with clock := context.toExact.state.clock - 1, locals := callee.lookup } : PanSemStateExact width σ) p1 p2 =
      (context.withState ({ context.state with clock := context.state.clock - 1, locals := callee } : PanSemStateFiniteExact width σ) rfl rfl).toExact := by
  apply PanSemExactEvalContext.ext
  cases context
  rfl

/-- FLAPJACK-SPECIFIC (not a HOL declaration): `toExact_callEntryContext_state`
    composed with a name for the finite entry context, giving the broad entry
    context projection directly as `ent.toExact`. -/
theorem toExact_callEntryContext_ent {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (ent : FiniteEvalContext width σ)
    (hent : context.withState ({ context.state with clock := context.state.clock - 1, locals := callee } : PanSemStateFiniteExact width σ) rfl rfl = ent)
    (p1 : ({ context.toExact.state with clock := context.toExact.state.clock - 1, locals := callee.lookup } : PanSemStateExact width σ).memaddrs = context.toExact.state.memaddrs)
    (p2 : ({ context.toExact.state with clock := context.toExact.state.clock - 1, locals := callee.lookup } : PanSemStateExact width σ).shMemaddrs = context.toExact.state.shMemaddrs) :
    context.toExact.withState ({ context.toExact.state with clock := context.toExact.state.clock - 1, locals := callee.lookup } : PanSemStateExact width σ) p1 p2 =
      ent.toExact := by
  rw [toExact_callEntryContext_state context callee p1 p2, hent]

/-- FLAPJACK-SPECIFIC (not a HOL declaration): a finite evaluation context is
    determined by its state; the two `DecidablePred` fields are proof-irrelevant
    for the respective (transported) predicates.  Used to compare contexts built
    by different `withState` call sites without unfolding their proof terms. -/
theorem ext {width : Nat} {σ : Type} [NeZero width]
    {c1 c2 : FiniteEvalContext width σ} (h : c1.state = c2.state) : c1 = c2 := by
  cases c1 with
  | mk s1 m1 sh1 =>
  cases c2 with
  | mk s2 m2 sh2 =>
  dsimp only at h
  subst h
  congr
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

/-- FLAPJACK-SPECIFIC (not a HOL declaration): a general `withState` projection
    bridge.  Whenever two states agree through `toExact`, their `withState`
    contexts project onto each other.  The seven explicit arguments let the
    projection proofs invoke it with `_ _ _ _` holes at the rewrite site, so the
    definition's auto-generated `withState` proof arguments unify even though the
    occurrence cannot be named syntactically. -/
theorem toExact_withState_eq {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ)
    (state : PanSemStateFiniteExact width σ) (broadState : PanSemStateExact width σ)
    (hstate : state.toExact = broadState)
    (hmem : state.memaddrs = context.state.memaddrs)
    (hshared : state.shMemaddrs = context.state.shMemaddrs)
    (hmem' : broadState.memaddrs = context.toExact.state.memaddrs)
    (hshared' : broadState.shMemaddrs = context.toExact.state.shMemaddrs) :
    (context.withState state hmem hshared).toExact =
      context.toExact.withState broadState hmem' hshared' := by
  apply PanSemExactEvalContext.ext
  exact hstate

/-- FLAPJACK-SPECIFIC (not a HOL declaration): `Call` exception-handler context
    bridge.  When the finite and broad fixed contexts agree through `toExact`,
    wrapping them with the handler `setVar` record update keeps projecting.  All
    arguments are explicit so the projection proofs can invoke it with `_` holes
    at the rewrite site (the definition's auto-generated `withState` proofs then
    unify). -/
theorem toExact_withState_setVarLocals {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ)
    (fixedFin : FiniteEvalContext width σ) (fixedBroad : PanSemExactEvalContext width σ)
    (hfix : fixedFin.toExact = fixedBroad)
    (name : MlS) (value : ValueHOL width)
    (p1 : (setVarHOLFinite name value
            ({ fixedFin.state with locals := context.state.locals } : PanSemStateFiniteExact width σ)).memaddrs
          = fixedFin.state.memaddrs)
    (p2 : (setVarHOLFinite name value
            ({ fixedFin.state with locals := context.state.locals } : PanSemStateFiniteExact width σ)).shMemaddrs
          = fixedFin.state.shMemaddrs)
    (q1 : (setVarHOLExact name value
            ({ fixedBroad.state with locals := context.toExact.state.locals } : PanSemStateExact width σ)).memaddrs
          = fixedBroad.state.memaddrs)
    (q2 : (setVarHOLExact name value
            ({ fixedBroad.state with locals := context.toExact.state.locals } : PanSemStateExact width σ)).shMemaddrs
          = fixedBroad.state.shMemaddrs) :
    (fixedFin.withState
        (setVarHOLFinite name value
          ({ fixedFin.state with locals := context.state.locals } : PanSemStateFiniteExact width σ)) p1 p2).toExact =
      fixedBroad.withState
        (setVarHOLExact name value
          ({ fixedBroad.state with locals := context.toExact.state.locals } : PanSemStateExact width σ)) q1 q2 := by
  apply PanSemExactEvalContext.ext
  change (setVarHOLFinite name value ({ fixedFin.state with locals := context.state.locals } : PanSemStateFiniteExact width σ)).toExact =
    setVarHOLExact name value ({ fixedBroad.state with locals := context.toExact.state.locals } : PanSemStateExact width σ)
  rw [toExact_setVarHOLFinite, toExact_setLocals]
  have hstate : fixedFin.state.toExact = fixedBroad.state := by
    have := congrArg PanSemExactEvalContext.state hfix
    simpa only [FiniteEvalContext.toExact] using this
  rw [hstate]
  rfl

end FiniteEvalContext

/-- FLAPJACK-SPECIFIC (not a HOL declaration): named `Call`/`DecCall` handler
    state.  Naming it (instead of an inline record-update literal) makes the
    projection bridges syntactic, because the definition no longer exposes an
    expanded record in which the `fixedContext` projections are unfolded. -/
def handlerStateHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) (fixedContext : FiniteEvalContext width σ)
    (name : MlS) (value : ValueHOL width) : PanSemStateFiniteExact width σ :=
  setVarHOLFinite name value { fixedContext.state with locals := context.state.locals }

/-- FLAPJACK-SPECIFIC (not a HOL declaration): the named finite handler state
    projects to the broad named handler state. -/
theorem toExact_handlerStateHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) (fixedFin : FiniteEvalContext width σ)
    (fixedBroad : PanSemExactEvalContext width σ) (hfix : fixedFin.toExact = fixedBroad)
    (name : MlS) (value : ValueHOL width) :
    (handlerStateHOLFinite context fixedFin name value).toExact =
      Flapjack.handlerStateHOLExact context.toExact fixedBroad name value := by
  unfold handlerStateHOLFinite Flapjack.handlerStateHOLExact
  rw [toExact_setVarHOLFinite, toExact_setLocals]
  have h : fixedFin.state.toExact = fixedBroad.state := by
    have := congrArg PanSemExactEvalContext.state hfix
    simpa only [FiniteEvalContext.toExact] using this
  rw [h]
  rfl

/-- FLAPJACK-SPECIFIC (not a HOL declaration): the named finite `DecCall`
    continuation context, so the projection bridges stay syntactic. -/
def callContinuationContextHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) (fixedContext : FiniteEvalContext width σ)
    (resultName : MlS) (value : ValueHOL width) : FiniteEvalContext width σ :=
  fixedContext.withState
    (handlerStateHOLFinite context fixedContext resultName value) rfl rfl

/-- FLAPJACK-SPECIFIC (not a HOL declaration): the named finite continuation
    context projects to the broad named continuation context. -/
theorem toExact_callContinuationContextHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) (fixedFin : FiniteEvalContext width σ)
    (fixedBroad : PanSemExactEvalContext width σ) (hfix : fixedFin.toExact = fixedBroad)
    (resultName : MlS) (value : ValueHOL width) :
    (callContinuationContextHOLFinite context fixedFin resultName value).toExact =
      Flapjack.callContinuationContextHOLExact context.toExact fixedBroad resultName value := by
  unfold callContinuationContextHOLFinite Flapjack.callContinuationContextHOLExact
  apply PanSemExactEvalContext.ext
  change (handlerStateHOLFinite context fixedFin resultName value).toExact =
    Flapjack.handlerStateHOLExact context.toExact fixedBroad resultName value
  exact toExact_handlerStateHOLFinite context fixedFin fixedBroad hfix resultName value

/-- FLAPJACK-SPECIFIC (not a HOL declaration): named finite fixed context for
    `Call`/`DecCall`, so the projection bridges stay syntactic. -/
def callFixedContextHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (entry : PanSemStateFiniteExact width σ)
    (bodyResult : Option (PanSemResultExact width))
    (bodyContext : FiniteEvalContext width σ) : FiniteEvalContext width σ :=
  bodyContext.withState
    (fixClockHOLFinite entry (bodyResult, bodyContext.state)).2 rfl rfl

/-- `callFixedContextHOLFinite` is independent of the equality proofs used to
    transport the memory-domain deciders. This normalizes the generated
    fixed-body `withState` context in the recursive DecCall equation. -/
theorem callFixedContextHOLFinite_normalize {width : Nat} {σ : Type} [NeZero width]
    (entry : PanSemStateFiniteExact width σ)
    (bodyResult : Option (PanSemResultExact width))
    (bodyContext : FiniteEvalContext width σ)
    (hmem : (fixClockHOLFinite entry (bodyResult, bodyContext.state)).2.memaddrs =
      bodyContext.state.memaddrs)
    (hshared : (fixClockHOLFinite entry (bodyResult, bodyContext.state)).2.shMemaddrs =
      bodyContext.state.shMemaddrs) :
    bodyContext.withState (fixClockHOLFinite entry (bodyResult, bodyContext.state)).2
        hmem hshared =
      callFixedContextHOLFinite entry bodyResult bodyContext := by
  unfold callFixedContextHOLFinite
  exact FiniteEvalContext.withState_congr bodyContext
    (fixClockHOLFinite entry (bodyResult, bodyContext.state)).2 hmem rfl hshared rfl

/-- FLAPJACK-SPECIFIC (not a HOL declaration): restore a finite Call's caller
    locals after a handler-free result. This names the dependent context update
    used by the evaluator equation. -/
def callRestoreLocalsContextHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (caller fixedContext : FiniteEvalContext width σ) : FiniteEvalContext width σ :=
  fixedContext.withState { fixedContext.state with locals := caller.state.locals } rfl rfl

/-- FLAPJACK-SPECIFIC (not a HOL declaration): install a finite Call result
    after restoring caller locals, naming the dependent context update. -/
def callSetKvarContextHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (caller fixedContext : FiniteEvalContext width σ)
    (kind : VarKind) (name : MlS) (value : ValueHOL width) : FiniteEvalContext width σ :=
  fixedContext.withState
    (setKvarHOLFinite kind name value
      { fixedContext.state with locals := caller.state.locals })
    (by cases kind <;> rfl) (by cases kind <;> rfl)

/-- FLAPJACK-SPECIFIC projection bridge for a handler-free Call's restored
    caller-locals context. -/
@[simp] theorem toExact_callRestoreLocalsContextHOLFinite {width : Nat} {σ : Type}
    [NeZero width] (caller fixedContext : FiniteEvalContext width σ) :
    (callRestoreLocalsContextHOLFinite caller fixedContext).toExact =
      fixedContext.toExact.withState
        { fixedContext.toExact.state with locals := caller.toExact.state.locals } rfl rfl := by
  apply PanSemExactEvalContext.ext
  rfl

/-- FLAPJACK-SPECIFIC projection bridge for a Call result installed after
    restoring caller locals. -/
@[simp] theorem toExact_callSetKvarContextHOLFinite {width : Nat} {σ : Type}
    [NeZero width] (caller fixedContext : FiniteEvalContext width σ)
    (kind : VarKind) (name : MlS) (value : ValueHOL width) :
    (callSetKvarContextHOLFinite caller fixedContext kind name value).toExact =
      fixedContext.toExact.withState
        (setKvarHOLExact kind name value
          { fixedContext.toExact.state with locals := caller.toExact.state.locals })
        (by cases kind <;> rfl) (by cases kind <;> rfl) := by
  apply PanSemExactEvalContext.ext
  change (setKvarHOLFinite kind name value
      { fixedContext.state with locals := caller.state.locals }).toExact =
    setKvarHOLExact kind name value
      { fixedContext.toExact.state with locals := caller.toExact.state.locals }
  rw [toExact_setKvarHOLFinite, toExact_setLocals]
  rfl

/-- FLAPJACK-SPECIFIC (not a HOL declaration): the named finite fixed context
    projects to the broad named fixed context. -/
theorem toExact_callFixedContextHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (entry : PanSemStateFiniteExact width σ)
    (bodyResult : Option (PanSemResultExact width))
    (bodyContext : FiniteEvalContext width σ) :
    (callFixedContextHOLFinite entry bodyResult bodyContext).toExact =
      Flapjack.callFixedContextHOLExact entry.toExact bodyResult bodyContext.toExact := by
  unfold callFixedContextHOLFinite Flapjack.callFixedContextHOLExact
  apply PanSemExactEvalContext.ext
  change (fixClockHOLFinite entry (bodyResult, bodyContext.state)).2.toExact =
    (fixClockHOLExact entry.toExact (bodyResult, bodyContext.state.toExact)).2
  rw [toExact_fixClockHOLFinite]

/-- FLAPJACK-SPECIFIC (not a HOL declaration): named finite `Call`/`DecCall`
    entry state.  Naming it (instead of an inline record-update literal) makes
    the projection bridges syntactic. -/
def callEntryStateHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) : PanSemStateFiniteExact width σ :=
  { state with clock := state.clock - 1, locals := callee }

/-- FLAPJACK-SPECIFIC (not a HOL declaration): the named finite
    `Call`/`DecCall` entry context. -/
def callEntryContextHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) : FiniteEvalContext width σ :=
  context.withState (callEntryStateHOLFinite context.state callee) rfl rfl

/-- `callEntryContextHOLFinite` is independent of the equality proofs used to
    transport the memory-domain deciders. This normalizes the generated
    `withState` arguments in the recursive evaluator equation to the named
    DecCall entry context. -/
theorem callEntryContextHOLFinite_normalize {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ)
    (callee : HolFiniteMapExact MlS (ValueHOL width))
    (hmem : (callEntryStateHOLFinite context.state callee).memaddrs = context.state.memaddrs)
    (hshared : (callEntryStateHOLFinite context.state callee).shMemaddrs = context.state.shMemaddrs) :
    context.withState (callEntryStateHOLFinite context.state callee) hmem hshared =
      callEntryContextHOLFinite context callee := by
  unfold callEntryContextHOLFinite
  exact FiniteEvalContext.withState_congr context
    (callEntryStateHOLFinite context.state callee) hmem rfl hshared rfl

/-- FLAPJACK-SPECIFIC (not a HOL declaration): the named finite entry state
    projects to the broad named entry state. -/
theorem toExact_callEntryStateHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) :
    (callEntryStateHOLFinite state callee).toExact =
      Flapjack.callEntryStateHOLExact state.toExact callee.lookup := by
  unfold callEntryStateHOLFinite Flapjack.callEntryStateHOLExact
  rw [toExact_setLocals_clock]

/-- The finite fix-clock never increases the clock. -/
theorem fixClockHOLFinite_clock_le {width : Nat} {σ : Type} [NeZero width] {β : Type}
    (oldState : PanSemStateFiniteExact width σ)
    (step : β × PanSemStateFiniteExact width σ) :
    (fixClockHOLFinite oldState step).2.clock ≤ oldState.clock := by
  change (if oldState.clock < step.2.clock then oldState.clock else step.2.clock) ≤
    oldState.clock
  split <;> omega

/-- FLAPJACK-SPECIFIC (not a HOL declaration): clause-for-clause finite-support
    rendering of the exact recursive program evaluator
    `evalPanSemRecursiveCallContextHOLExact`, returning a `FiniteEvalContext`
    so that the `memaddrs`/`shMemaddrs` deciders are threaded through recursive
    calls on updated finite states.  This is the prerequisite for the tagged
    `evaluate_def` port (bead `flapjack-6yq`). -/
def evalPanSemRecursiveCallFiniteContext {width : Nat} {σ : Type} [NeZero width] :
    ProgHOL width → FiniteEvalContext width σ →
      Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)
  | program, context => by
      let state := context.state
      letI : DecidablePred state.memaddrs := context.memaddrsDecidable
      letI : DecidablePred state.shMemaddrs := context.shMemaddrsDecidable
      exact match program with
      | .dec name shape initializer body =>
          match evalHOLFinite state initializer with
          | none => some (some .error, context)
          | some value =>
              if shapeEqHOL shape (shapeOfHOLExact value) then
                let bodyState := setVarHOLFinite name value state
                let bodyContext := context.withState bodyState rfl rfl
                match evalPanSemRecursiveCallFiniteContext body bodyContext with
                | none => none
                | some (result, postContext) =>
                    let restored := { postContext.state with
                      locals := HolFiniteMapExact.resVarEq postContext.state.locals
                        (name, state.locals.lookup name) }
                    some (result, postContext.withState restored rfl rfl)
              else some (some .error, context)
      | .seq first second =>
          match evalPanSemRecursiveCallFiniteContext first context with
          | none => none
          | some (firstResult, firstContext) =>
              let fixed := fixClockHOLFinite state (firstResult, firstContext.state)
              let fixedContext := firstContext.withState fixed.2 rfl rfl
              match firstResult with
              | none => evalPanSemRecursiveCallFiniteContext second fixedContext
              | some _ => some (firstResult, fixedContext)
      | .ite condition thenBranch elseBranch =>
          match evalHOLFinite state condition with
          | some (.val (.word value)) =>
              if value != 0 then
                evalPanSemRecursiveCallFiniteContext thenBranch context
              else
                evalPanSemRecursiveCallFiniteContext elseBranch context
          | _ => some (some .error, context)
      | .while condition body =>
          match evalHOLFinite state condition with
          | some (.val (.word word)) =>
              if word ≠ 0 then
                if state.clock = 0 then
                  some (some .timeOut,
                    context.withState (emptyLocalsHOLFinite state) rfl rfl)
                else
                  let entry := decClockHOLFinite state
                  let entryContext := context.withState entry rfl rfl
                  match evalPanSemRecursiveCallFiniteContext body entryContext with
                  | none => none
                  | some (bodyResult, bodyContext) =>
                      let fixed := fixClockHOLFinite entry (bodyResult, bodyContext.state)
                      let fixedContext := bodyContext.withState fixed.2 rfl rfl
                      match bodyResult with
                      | some .continue | none =>
                          evalPanSemRecursiveCallFiniteContext
                            (.while condition body) fixedContext
                      | some .break => some (none, fixedContext)
                      | _ => some (bodyResult, fixedContext)
              else some (none, context)
          | _ => some (some .error, context)
      | .call info function arguments =>
          match evalListHOLFinite state arguments with
          | none => some (some .error, context)
          | some values =>
              match lookupCodeHOLFinite state.code.lookup function values with
              | none => some (some .error, context)
              | some (body, callee, returnShape) =>
                  if state.clock = 0 then
                    some (some .timeOut,
                      FiniteEvalContext.emptyLocalsContextHOLFinite context)
                  else
                    let entry : PanSemStateFiniteExact width σ := callEntryStateHOLFinite state callee
                    let entryContext := callEntryContextHOLFinite context callee
                    match evalPanSemRecursiveCallFiniteContext body entryContext with
                    | none => none
                    | some (bodyResult, bodyContext) =>
                        let fixed := fixClockHOLFinite entry (bodyResult, bodyContext.state)
                        let fixedContext := callFixedContextHOLFinite entry bodyResult bodyContext
                        match bodyResult with
                        | none => some (some .error, fixedContext)
                        | some .break => some (some .error, fixedContext)
                        | some .continue => some (some .error, fixedContext)
                        | some (.returned value) =>
                            if shapeEqHOL (shapeOfHOLExact value) returnShape then
                              match info with
                              | none =>
                                  some (some (.returned value),
                                    FiniteEvalContext.emptyLocalsContextHOLFinite fixedContext)
                              | some (none, _) =>
                                  some (none,
                                    callRestoreLocalsContextHOLFinite context fixedContext)
                              | some (some (kind, name), _) =>
                                  if isValidValueHOLExact state.toExact kind name value then
                                    some (none, callSetKvarContextHOLFinite context fixedContext
                                      kind name value)
                                  else some (some .error, fixedContext)
                            else some (some .error, fixedContext)
                        | some (.exception exceptionId value) =>
                            match info with
                            | none =>
                                some (some (.exception exceptionId value),
                                  FiniteEvalContext.emptyLocalsContextHOLFinite fixedContext)
                            | some (_, none) =>
                                some (some (.exception exceptionId value),
                                  FiniteEvalContext.emptyLocalsContextHOLFinite fixedContext)
                            | some (_, some (handlerId, handlerVar, handlerProgram)) =>
                                if exceptionId = handlerId then
                                  match state.eshapes.lookup exceptionId with
                                  | some shape =>
                                      if shapeEqHOL (shapeOfHOLExact value) shape &&
                                          isValidValueHOLExact state.toExact .local handlerVar value then
                                        let handlerState := handlerStateHOLFinite context fixedContext handlerVar value
                                        let handlerContext :=
                                          callContinuationContextHOLFinite context fixedContext
                                            handlerVar value
                                        evalPanSemRecursiveCallFiniteContext handlerProgram
                                          handlerContext
                                      else some (some .error, fixedContext)
                                  | none => some (some .error, fixedContext)
                                else
                                  some (some (.exception exceptionId value),
                                    FiniteEvalContext.emptyLocalsContextHOLFinite fixedContext)
                        | some other =>
                            some (some other,
                              FiniteEvalContext.emptyLocalsContextHOLFinite fixedContext)
      | .decCall resultName shape function arguments continuation =>
          match evalListHOLFinite state arguments with
          | none => some (some .error, context)
          | some values =>
              match lookupCodeHOLFinite state.code.lookup function values with
              | none => some (some .error, context)
              | some (body, callee, returnShape) =>
                  if state.clock = 0 then
                    some (some .timeOut,
                      FiniteEvalContext.emptyLocalsContextHOLFinite context)
                  else
                    let entry : PanSemStateFiniteExact width σ := callEntryStateHOLFinite state callee
                    let entryContext := context.withState entry rfl rfl
                    match evalPanSemRecursiveCallFiniteContext body entryContext with
                    | none => none
                    | some (bodyResult, bodyContext) =>
                        let fixed := fixClockHOLFinite entry (bodyResult, bodyContext.state)
                        let fixedContext := callFixedContextHOLFinite entry bodyResult bodyContext
                        match bodyResult with
                        | none => some (some .error, fixedContext)
                        | some .break => some (some .error, fixedContext)
                        | some .continue => some (some .error, fixedContext)
                        | some (.returned value) =>
                            if shapeEqHOL (shapeOfHOLExact value) shape &&
                                shapeEqHOL (shapeOfHOLExact value) returnShape then
                              let continuationContext :=
                                callContinuationContextHOLFinite context fixedContext resultName value
                              match evalPanSemRecursiveCallFiniteContext continuation
                                  continuationContext with
                              | none => none
                              | some (continuationResult, continuationPost) =>
                                  let restored := { continuationPost.state with
                                    locals := HolFiniteMapExact.resVarEq
                                      continuationPost.state.locals
                                      (resultName, state.locals.lookup resultName) }
                                  some (continuationResult,
                                    continuationPost.withState restored rfl rfl)
                            else some (some .error, fixedContext)
                        | some other =>
                            some (some other, fixedContext.withState
                              (emptyLocalsHOLFinite fixedContext.state) rfl rfl)
      | .skip => some (none, context)
      | .break => some (some .break, context)
      | .continue => some (some .continue, context)
      | .annot _ _ => some (none, context)
      | .tick =>
          if state.clock = 0 then
            some (some .timeOut, context.withState (emptyLocalsHOLFinite state) rfl rfl)
          else
            some (none, context.withState (decClockHOLFinite state) rfl rfl)
      | .return value =>
          match evalHOLFinite state value with
          | none => some (some .error, context)
          | some returned =>
              if Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
                  (shapeOfHOLExact returned) ≤ 32 then
                some (some (.returned returned),
                  context.withState (emptyLocalsHOLFinite state) rfl rfl)
              else some (some .error, context)
      | .raise exception value =>
          match evalHOLFinite state value with
          | none => some (some .error, context)
          | some raised =>
              match state.eshapes.lookup exception with
              | none => some (some .error, context)
              | some shape =>
                  if shapeEqHOL (shapeOfHOLExact raised) shape then
                    if Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
                        (shapeOfHOLExact raised) ≤ 32 then
                      some (some (.exception exception raised),
                        context.withState (emptyLocalsHOLFinite state) rfl rfl)
                    else some (some .error, context)
                  else some (some .error, context)
      | .shMemLoad size kind name address =>
          let evalExpression := fun (_ : PanSemStateExact width σ)
              (expression : ExpHOL width) => evalHOLExact state.toExact expression
          let output := shMemLoadClauseHOLExact state.toExact size kind name address
            evalExpression
          some (output.1, context.withState
            (ofExact output.2 (shMemLoadClauseHOLExact_finiteSupport state.toExact
              size kind name address evalExpression state.toExact_finiteSupport))
            (by
              have hdom := (shMemLoadClauseHOLExact_preservesDomains state.toExact
                size kind name address evalExpression).1
              exact hdom)
            (by
              have hdom := (shMemLoadClauseHOLExact_preservesDomains state.toExact
                size kind name address evalExpression).2
              exact hdom))
      | .shMemStore size address value =>
          let evalExpression := fun (_ : PanSemStateExact width σ)
              (expression : ExpHOL width) => evalHOLExact state.toExact expression
          let output := shMemStoreClauseHOLExact state.toExact size address value
            evalExpression
          some (output.1, context.withState
            (ofExact output.2 (shMemStoreClauseHOLExact_finiteSupport state.toExact
              size address value evalExpression state.toExact_finiteSupport))
            (by
              have hdom := (shMemStoreClauseHOLExact_preservesDomains state.toExact
                size address value evalExpression).1
              exact hdom)
            (by
              have hdom := (shMemStoreClauseHOLExact_preservesDomains state.toExact
                size address value evalExpression).2
              exact hdom))
      | other =>
          match hres : evalPanSemNonrecursiveHOLFinite state other with
          | none => none
          | some pair =>
              some (pair.1, context.withState pair.2
                (evalPanSemNonrecursiveHOLFinite_memaddrs state other pair hres)
                (evalPanSemNonrecursiveHOLFinite_shMemaddrs state other pair hres))
termination_by _program context => (context.state.clock, sizeOf _program)
decreasing_by
  · simp_wf
    apply Prod.Lex.right
    simp_wf
    omega
  · simp_wf
    apply Prod.Lex.right
    simp_wf
    omega
  · simp only [FiniteEvalContext.withState]
    by_cases hlt : fixed.2.clock < state.clock
    · apply Prod.Lex.left
      exact hlt
    · have hle : fixed.2.clock ≤ state.clock :=
        fixClockHOLFinite_clock_le state (firstResult, firstContext.state)
      have heq : fixed.2.clock = state.clock := by omega
      rw [heq]
      apply Prod.Lex.right
      simp_wf
      omega
  · simp_wf
    apply Prod.Lex.right
    simp_wf
    omega
  · simp_wf
    apply Prod.Lex.right
    simp_wf
    omega
  · simp only [FiniteEvalContext.withState]
    apply Prod.Lex.left
    exact Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) (by decide)
  · simp only [FiniteEvalContext.withState]
    apply Prod.Lex.left
    exact Nat.lt_of_le_of_lt
      (fixClockHOLFinite_clock_le entry (bodyResult, bodyContext.state))
      (Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) (by decide))
  · try simp only [FiniteEvalContext.withState]
    apply Prod.Lex.left
    exact Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) (by decide)
  · try simp only [FiniteEvalContext.withState]
    apply Prod.Lex.left
    exact Nat.lt_of_le_of_lt
      (fixClockHOLFinite_clock_le entry (bodyResult, bodyContext.state))
      (Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) (by decide))
  · simp only [FiniteEvalContext.withState]
    apply Prod.Lex.left
    exact Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) (by decide)
  · simp only [callContinuationContextHOLFinite, FiniteEvalContext.withState]
    apply Prod.Lex.left
    exact Nat.lt_of_le_of_lt
      (fixClockHOLFinite_clock_le entry (bodyResult, bodyContext.state))
      (Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) (by decide))

/-- FLAPJACK-SPECIFIC normalization check for the generated DecCall timeout
    branch. Naming the cleared-locals context in the evaluator lets this exact
    branch equation reduce without exposing the equation compiler's dependent
    proof placeholder. -/
theorem evalPanSemRecursiveCallFiniteContext_decCall_timeout_branch
    {width : Nat} {σ : Type} [NeZero width]
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL)
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock = 0) :
    evalPanSemRecursiveCallFiniteContext
      (.decCall resultName shape function arguments continuation) context =
      some (some .timeOut, FiniteEvalContext.emptyLocalsContextHOLFinite context) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_6]
  simp only [hargs, hlookup, if_pos hclock]

/-- HOL `evaluate_decls_def` (`cakeml/pancake/semantics/panSemScript.sml:814-837`)
    over the finite-support state carrier.  Its clauses match the HOL definition
    one by one: `[]` returns the state unchanged; a `Name` declaration is
    skipped; a `Decl` evaluates its initialiser with the tagged `evalHOLFinite`
    under cleared locals (`emptyLocalsHOLFinite`, i.e. `s with locals := FEMPTY`)
    and, on shape agreement, updates `globals`; a `Function` is admitted when its
    parameters and return shape are well formed and then stored in `code`; an
    `ExnDecl` is admitted when its identifier is fresh and its shape is well
    formed, then stored in `eshapes`.  Every HOL `|+` (`FUPDATE`) is the
    canonical `HolFiniteMapExact.update`.  The four map-shaped fields
    (`locals`, `globals`, `code`, `eshapes`) are recorded by the
    `fmap_as_finite_support` qualifier (canonical witness
    `holFmapAsFiniteSupportWitness` in this module). -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_decls_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
def evaluateDeclsHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    List (DeclHOL width) → Option (PanSemStateFiniteExact width σ)
  | [] => some state
  | .name _ _ :: declarations => evaluateDeclsHOLFinite state declarations
  | .decl shape name expression :: declarations =>
      letI : DecidablePred (state.emptyLocalsHOLFinite.memaddrs) := h
      match evalHOLFinite (emptyLocalsHOLFinite state) expression with
      | some value =>
          if shapeEqHOL shape (shapeOfHOLExact value) then
            letI : DecidablePred (setGlobalHOLFinite name value state).memaddrs := h
            evaluateDeclsHOLFinite (setGlobalHOLFinite name value state) declarations
          else none
      | none => none
  | .function declaration :: declarations =>
      let entry : List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL :=
        (declaration.params, declaration.body, declaration.returnShape)
      if declaration.params.all
            (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
          isWfShapeExactHOL state.structs declaration.returnShape then
        let updated : PanSemStateFiniteExact width σ :=
          { state with code := state.code.update (declaration.name, entry) }
        letI : DecidablePred updated.memaddrs := h
        evaluateDeclsHOLFinite updated declarations
      else none
  | .exnDecl exceptionName shape :: declarations =>
      if (state.eshapes.lookup exceptionName).isNone &&
          isWfShapeExactHOL state.structs shape then
        let updated : PanSemStateFiniteExact width σ :=
          { state with eshapes := state.eshapes.update (exceptionName, shape) }
        letI : DecidablePred updated.memaddrs := h
        evaluateDeclsHOLFinite updated declarations
      else none

/-- FLAPJACK-SPECIFIC provisional rendering (no `@[hol]` tag): HOL
    `panProps$evaluate_decls_names` (`panPropsScript.sml:1552-1559`) is a PanProps
    declaration, so its HOL port belongs in the PanProps counterpart module, not
    this PanSem module (coordinator HOLD 2026-09-26T16:46Z). The tag was
    withdrawn pending relocation to a PanProps submodule that owns the state
    carrier and its canonical witness. The Lean fact still holds: when every
    declaration is a `Name`, `evaluateDeclsHOLFinite` succeeds and leaves the
    state unchanged (`decs.all isNameHOL = true` renders HOL `EVERY is_name
    decs`). -/
theorem evaluateDeclsHOLFinite_names {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (decs : List (DeclHOL width)) (hnames : decs.all isNameHOL = true) :
    evaluateDeclsHOLFinite state decs = some state := by
  induction decs generalizing state with
  | nil => rfl
  | cons declaration rest ih =>
      rw [List.all_cons, Bool.and_eq_true] at hnames
      obtain ⟨hhead, hrest⟩ := hnames
      cases declaration with
      | name name fields => exact ih state hrest
      | decl shape name expression => simp [isNameHOL] at hhead
      | function declaration => simp [isNameHOL] at hhead
      | exnDecl exceptionName shape => simp [isNameHOL] at hhead

/-- Flapjack finite-map support: a single `FUPDATE` followed by `FUPDATE_LIST`
    is the `FUPDATE_LIST` with the entry prepended. Infrastructure for the
    `evaluate_decls_functions` port, not a separate HOL declaration. -/
private theorem updateList_cons {α β : Type} [BEq α] [LawfulBEq α]
    (map : HolFiniteMapExact α β) (entry : α × β) (entries : List (α × β)) :
    (map.update entry).updateList entries = map.updateList (entry :: entries) := by
  apply HolFiniteMapExact.ext
  funext key
  simp only [HolFiniteMapExact.lookup_updateList, FUPDATE_LIST_cons]
  rfl

/-- Flapjack finite-map support: `updateList` with no entries is the identity.
    Infrastructure for the `evaluate_decls_functions` port, not a separate HOL
    declaration. -/
private theorem updateList_nil {α β : Type} [BEq α] [LawfulBEq α]
    (map : HolFiniteMapExact α β) : map.updateList [] = map := by
  apply HolFiniteMapExact.ext
  funext key
  rfl

/-- FLAPJACK-SPECIFIC provisional rendering (no `@[hol]` tag): HOL
    `panProps$evaluate_decls_functions` (`panPropsScript.sml:1518-1526`) is a
    PanProps declaration, so its HOL port belongs in the PanProps counterpart
    module, not this PanSem module (coordinator HOLD 2026-09-26T16:46Z). The tag
    was withdrawn pending relocation to a PanProps submodule that owns the state
    carrier and its canonical witness. The Lean fact still holds: a successful
    `evaluateDeclsHOLFinite` records exactly the function entries of the program
    in `code` (`updateList` is the canonical finite-map `|++`). -/
theorem evaluateDeclsHOLFinite_functions {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanSemStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) (result : PanSemStateFiniteExact width σ),
      evaluateDeclsHOLFinite state program = some result →
      result.code = state.code.updateList (functionsHOL program) := by
  intro state hstate program
  induction program generalizing state with
  | nil =>
      intro result hresult
      simp only [evaluateDeclsHOLFinite, Option.some.injEq] at hresult
      subst hresult
      exact (updateList_nil state.code).symm
  | cons declaration rest ih =>
      intro result hresult
      cases declaration with
      | name name fields =>
          simp only [evaluateDeclsHOLFinite, functionsHOL] at hresult ⊢
          exact ih state result hresult
      | decl shape name expression =>
          simp only [evaluateDeclsHOLFinite, functionsHOL] at hresult ⊢
          letI : DecidablePred (emptyLocalsHOLFinite state).memaddrs := hstate
          cases heval : evalHOLFinite (emptyLocalsHOLFinite state) expression with
          | none => simp [heval] at hresult
          | some value =>
              by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value)
              · simp only [heval, if_pos hshape] at hresult
                have htail := ih
                  { state with globals := state.globals.update (name, value) }
                  result hresult
                simpa using htail
              · simp [heval, hshape] at hresult
      | function declaration =>
          let condition := declaration.params.all
            (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          simp only [evaluateDeclsHOLFinite, functionsHOL] at hresult ⊢
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_true] at hresult
            have htail := ih
              { state with code := state.code.update (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape)) }
              result hresult
            rw [htail]
            exact updateList_cons state.code
              (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape))
              (functionsHOL rest)
          · have hfalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact absurd hcond hcondition
            simp [condition, hfalse] at hresult
      | exnDecl exceptionName shape =>
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          simp only [evaluateDeclsHOLFinite, functionsHOL] at hresult ⊢
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_true] at hresult
            have htail := ih
              { state with eshapes := state.eshapes.update (exceptionName, shape) }
              result hresult
            simpa using htail
          · have hfalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact absurd hcond hcondition
            simp [condition, hfalse] at hresult

/-- Infrastructure for `evaluate_decl_commute`: the canonical finite evaluator
    is unchanged when only the `code` field of a state whose locals have been
    cleared is updated (`eval_upd_code_eq` applied under `emptyLocalsHOLFinite`).
    Not a separate HOL declaration. -/
private theorem evalHOLFinite_emptyLocals_code {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (e : ExpHOL width) :
    @evalHOLFinite width σ _ (emptyLocalsHOLFinite { state with code := c }) h e
      = @evalHOLFinite width σ _ (emptyLocalsHOLFinite state) h e :=
  @evalHOLFinite_upd_code_eq width σ _ (emptyLocalsHOLFinite state) h c e

section

set_option maxHeartbeats 4000000

/-- FLAPJACK-SPECIFIC provisional rendering (no `@[hol]` tag): HOL
    `panProps$evaluate_decl_commute` (`panPropsScript.sml:1472-1480`) is a PanProps
    declaration, so its HOL port belongs in the PanProps counterpart module, not
    this PanSem module (coordinator HOLD 2026-09-26T16:46Z). The tag was
    withdrawn pending relocation to a PanProps submodule that owns the state
    carrier and its canonical witness. The Lean fact still holds: swapping an
    adjacent `Function` and `Decl` declaration leaves `evaluateDeclsHOLFinite`
    unchanged, because `Decl` clears the locals and updates only
    `globals`/`eshapes`, while `Function` updates only `code` and the evaluator
    does not read `code`. -/
theorem evaluateDeclsHOLFinite_declCommute {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (fi : FunDeclHOL width) (sh : ShapeHOL) (v' : MlS) (e : ExpHOL width)
    (ds : List (DeclHOL width)) :
    evaluateDeclsHOLFinite state (.function fi :: .decl sh v' e :: ds)
      = evaluateDeclsHOLFinite state (.decl sh v' e :: .function fi :: ds) := by
  simp only [evaluateDeclsHOLFinite]
  rw [evalHOLFinite_emptyLocals_code]
  simp only [setGlobalHOLFinite]
  by_cases hwf : (fi.params.all (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
      isWfShapeExactHOL state.structs fi.returnShape) = true
  · rw [if_pos hwf]
    letI : DecidablePred state.emptyLocalsHOLFinite.memaddrs := h
    cases hev : evalHOLFinite (emptyLocalsHOLFinite state) e with
    | none => rfl
    | some value =>
        by_cases hshape : shapeEqHOL sh (shapeOfHOLExact value) = true
        · simp [hshape, hwf]
        · simp [hshape]
  · rw [if_neg hwf]
    letI : DecidablePred state.emptyLocalsHOLFinite.memaddrs := h
    cases hev : evalHOLFinite (emptyLocalsHOLFinite state) e with
    | none => rfl
    | some value =>
        by_cases hshape : shapeEqHOL sh (shapeOfHOLExact value) = true
        · simp [hshape, hwf]
        · simp [hshape]

end

/-- FLAPJACK-SPECIFIC (no `@[hol]` tag): the clause-for-clause finite context
    evaluator is total.  Its outer `Option` is only the recursive-case assembly
    marker, so it is always `some`; this is the finite-context analogue of
    `evalPanSemRecursiveCallContextHOLExact_total`. -/
theorem evalPanSemRecursiveCallFiniteContext_total {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (context : FiniteEvalContext width σ) :
    ∃ output, evalPanSemRecursiveCallFiniteContext program context = some output := by
  fun_induction evalPanSemRecursiveCallFiniteContext program context <;> simp_all
  case case65 =>
    rename_i instNeZero ctx stateFinite program decNeg seqNeg x12 x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 hres
    cases program <;> simp_all [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact]
    · exact decNeg _ _ _ _ rfl rfl rfl rfl
    · exact x9 _ _ _ _ _ rfl rfl rfl rfl rfl

/-- FLAPJACK-SPECIFIC (not a HOL declaration): the finite recursive evaluator
    depends on a `FiniteEvalContext` only through its source state. This is the
    finite-support counterpart of `eval_context_state` in `AddClock.lean` and
    avoids unfolding the generated `DecidablePred` proof terms when normalizing
    recursive body and continuation calls. -/
theorem evalPanSemRecursiveCallFiniteContext_state_eq {width : Nat} {σ : Type}
    [NeZero width] (program : ProgHOL width)
    (context context' : FiniteEvalContext width σ)
    (hstate : context.state = context'.state) :
    evalPanSemRecursiveCallFiniteContext program context =
      evalPanSemRecursiveCallFiniteContext program context' :=
  congrArg (evalPanSemRecursiveCallFiniteContext program)
    (FiniteEvalContext.ext hstate)

/-- FLAPJACK-SPECIFIC specialization of `evalPanSemRecursiveCallFiniteContext_state_eq`
    for the dependent `withState` context generated at the DecCall entry. The
    explicit domain-equality proofs may differ from the canonical proofs in
    `callEntryContextHOLFinite`; the recursive evaluator depends only on the
    transported state. -/
theorem evalPanSemRecursiveCallFiniteContext_callEntryContext_normalize
    {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (context : FiniteEvalContext width σ)
    (callee : HolFiniteMapExact MlS (ValueHOL width))
    (hmem : (callEntryStateHOLFinite context.state callee).memaddrs =
      context.state.memaddrs)
    (hshared : (callEntryStateHOLFinite context.state callee).shMemaddrs =
      context.state.shMemaddrs) :
    evalPanSemRecursiveCallFiniteContext program
        (context.withState (callEntryStateHOLFinite context.state callee) hmem hshared) =
      evalPanSemRecursiveCallFiniteContext program
        (callEntryContextHOLFinite context callee) := by
  apply evalPanSemRecursiveCallFiniteContext_state_eq
  rfl

/-- FLAPJACK-SPECIFIC DecCall body-`NONE` case for the finite context
    evaluator. After successful arguments and lookup and a nonzero clock, the
    recursive body result `NONE` produces `Error` with the fixed callee
    post-context. This keeps the generated `withState` decider proofs out of
    the body induction hypothesis; the exact finite-state HOL case is stated
    separately below. -/
theorem evalPanSemRecursiveCallFiniteContext_decCall_body_none
    {width : Nat} {σ : Type} [NeZero width]
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (bodyContext : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock ≠ 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (callEntryContextHOLFinite context callee) =
      some (none, bodyContext)) :
    evalPanSemRecursiveCallFiniteContext
        (.decCall resultName shape function arguments continuation) context =
      some (some .error,
        callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
          none bodyContext) := by
  have hbodyGenerated : evalPanSemRecursiveCallFiniteContext body
      (context.withState (callEntryStateHOLFinite context.state callee) rfl rfl) =
      some (none, bodyContext) := by
    calc
      _ = evalPanSemRecursiveCallFiniteContext body
          (callEntryContextHOLFinite context callee) := by
        apply evalPanSemRecursiveCallFiniteContext_state_eq
        rfl
      _ = _ := hbody
  rw [evalPanSemRecursiveCallFiniteContext.eq_6]
  simp only [hargs]
  rw [hlookup]
  simp only [if_neg hclock, hbodyGenerated]

/-- FLAPJACK-SPECIFIC DecCall body-`Break` case for the finite context
    evaluator: the source clause maps a callee `Break` outcome to `Error` at
    the fixed callee post-context. -/
theorem evalPanSemRecursiveCallFiniteContext_decCall_body_break
    {width : Nat} {σ : Type} [NeZero width]
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (bodyContext : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock ≠ 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (callEntryContextHOLFinite context callee) =
      some (some .break, bodyContext)) :
    evalPanSemRecursiveCallFiniteContext
        (.decCall resultName shape function arguments continuation) context =
      some (some .error,
        callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
          (some .break) bodyContext) := by
  have hbodyGenerated : evalPanSemRecursiveCallFiniteContext body
      (context.withState (callEntryStateHOLFinite context.state callee) rfl rfl) =
      some (some .break, bodyContext) := by
    calc
      _ = evalPanSemRecursiveCallFiniteContext body
          (callEntryContextHOLFinite context callee) := by
        apply evalPanSemRecursiveCallFiniteContext_state_eq
        rfl
      _ = _ := hbody
  rw [evalPanSemRecursiveCallFiniteContext.eq_6]
  simp only [hargs]
  rw [hlookup]
  simp only [if_neg hclock, hbodyGenerated]

/-- FLAPJACK-SPECIFIC DecCall body-`Continue` case for the finite context
    evaluator: the source clause maps a callee `Continue` outcome to `Error`
    at the fixed callee post-context. -/
theorem evalPanSemRecursiveCallFiniteContext_decCall_body_continue
    {width : Nat} {σ : Type} [NeZero width]
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (bodyContext : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock ≠ 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (callEntryContextHOLFinite context callee) =
      some (some .continue, bodyContext)) :
    evalPanSemRecursiveCallFiniteContext
        (.decCall resultName shape function arguments continuation) context =
      some (some .error,
        callFixedContextHOLFinite (callEntryStateHOLFinite context.state callee)
          (some .continue) bodyContext) := by
  have hbodyGenerated : evalPanSemRecursiveCallFiniteContext body
      (context.withState (callEntryStateHOLFinite context.state callee) rfl rfl) =
      some (some .continue, bodyContext) := by
    calc
      _ = evalPanSemRecursiveCallFiniteContext body
          (callEntryContextHOLFinite context callee) := by
        apply evalPanSemRecursiveCallFiniteContext_state_eq
        rfl
      _ = _ := hbody
  rw [evalPanSemRecursiveCallFiniteContext.eq_6]
  simp only [hargs]
  rw [hlookup]
  simp only [if_neg hclock, hbodyGenerated]

/-- FLAPJACK-SPECIFIC specialization for the fixed callee context in the
    DecCall equation. This hides the generated finite-domain proof arguments
    behind the canonical `callFixedContextHOLFinite` context. -/
theorem evalPanSemRecursiveCallFiniteContext_callFixedContext_normalize
    {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (entry : PanSemStateFiniteExact width σ)
    (bodyResult : Option (PanSemResultExact width))
    (bodyContext : FiniteEvalContext width σ)
    (hmem : (fixClockHOLFinite entry (bodyResult, bodyContext.state)).2.memaddrs =
      bodyContext.state.memaddrs)
    (hshared : (fixClockHOLFinite entry (bodyResult, bodyContext.state)).2.shMemaddrs =
      bodyContext.state.shMemaddrs) :
    evalPanSemRecursiveCallFiniteContext program
        (bodyContext.withState
          (fixClockHOLFinite entry (bodyResult, bodyContext.state)).2 hmem hshared) =
      evalPanSemRecursiveCallFiniteContext program
        (callFixedContextHOLFinite entry bodyResult bodyContext) := by
  apply evalPanSemRecursiveCallFiniteContext_state_eq
  rfl

/-- FLAPJACK-SPECIFIC (not a HOL declaration): the generated successful
    `DecCall` continuation context and the named finite `callContinuationContextHOLFinite`
    have the same state. This keeps the clock-fixed body context and the
    caller-local restoration visible when proving the unconditional DecCall
    equation, without relying on generated `withState` proof arguments. -/
theorem evalPanSemRecursiveCallFiniteContext_callContinuationContext_normalize
    {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ)
    (entry : PanSemStateFiniteExact width σ)
    (bodyResult : Option (PanSemResultExact width))
    (bodyContext : FiniteEvalContext width σ)
    (resultName : MlS) (value : ValueHOL width)
    (hmem : (fixClockHOLFinite entry (bodyResult, bodyContext.state)).2.memaddrs =
      bodyContext.state.memaddrs)
    (hshared : (fixClockHOLFinite entry (bodyResult, bodyContext.state)).2.shMemaddrs =
      bodyContext.state.shMemaddrs) :
    ((bodyContext.withState
          (fixClockHOLFinite entry (bodyResult, bodyContext.state)).2 hmem hshared).withState
          (handlerStateHOLFinite context
            (bodyContext.withState
              (fixClockHOLFinite entry (bodyResult, bodyContext.state)).2 hmem hshared)
            resultName value) rfl rfl) =
      callContinuationContextHOLFinite context
        (callFixedContextHOLFinite entry bodyResult bodyContext) resultName value := by
  apply FiniteEvalContext.ext
  rfl

/-- FLAPJACK-SPECIFIC provisional projection (not a HOL declaration; carries no
    `@[hol]` tag): the state-level view of the clause-for-clause finite context
    evaluator `evalPanSemRecursiveCallFiniteContext`.

    As with the broad exact evaluator `evalPanSemRecursiveCallContextHOLExact`,
    the outer `Option` is the *assembly marker* for the recursive cases (it is
    `none` only on the not-yet-assembled internal branches), not part of HOL
    `evaluate_def`'s `result option × state` result. The marker is provably
    inert (`evaluateHOLFinite_ne_none`), and the 66-case projection to the broad
    exact evaluator is proved. This wrapper retains the marker for existing
    callers; a pair-shaped wrapper is available separately. A HOL tag still
    requires source review of the evaluator clauses and carriers.

    Exposed clause-by-clause in
    `Flapjack.Pancake.Semantics.PanSem.EvaluateFinite`. -/
def evaluateHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    ProgHOL width →
      Option (Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) :=
  fun program =>
    (evalPanSemRecursiveCallFiniteContext program ⟨state, h, hshared⟩).map
      (fun pair => (pair.1, pair.2.state))

/-- FLAPJACK-SPECIFIC (no `@[hol]` tag): the state-level projection never hits the
    assembly marker's `none`, by `evalPanSemRecursiveCallFiniteContext_total`. -/
theorem evaluateHOLFinite_ne_none {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width) : evaluateHOLFinite state program ≠ none := by
  obtain ⟨output, houtput⟩ :=
    evalPanSemRecursiveCallFiniteContext_total program (⟨state, h, hshared⟩ : FiniteEvalContext width σ)
  unfold evaluateHOLFinite
  rw [houtput]
  simp

/-- Flapjack-specific evaluator view that makes the two decidability witnesses
    explicit for callers that need to choose them. -/
def evaluateHOLFiniteStateWithDeciders {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width) :
    Option (PanSemResultExact width) × PanSemStateFiniteExact width σ :=
  match evalPanSemRecursiveCallFiniteContext program ⟨state, h, hshared⟩ with
  | some pair => (pair.1, pair.2.state)
  | none => (none, state)

/-- Flapjack-specific finite-support evaluator aligned with HOL
    `panSem$evaluate_def` (`panSemScript.sml:556-761`, rewritten as a theorem at
    line 780). It preserves the result-option × state pair, but this Lean
    declaration is a function definition, whereas HOL's cited declaration is
    a conjunction of constructor equations. Those equations still need an
    exact theorem port (tracked by `flapjack-qj5`); this wrapper must not carry
    the HOL theorem's tag. `FiniteEvalContext` threads
    Lean's operational `DecidablePred` evidence through local/state updates;
    this wrapper chooses that evidence classically, so it adds no logical
    premise. The internal evaluator's outer assembly marker is proved always
    populated, and `evaluateHOLFiniteStateWithDeciders_eq_getD` shows that its
    fallback does not change any result.

    The `(fmap_as_finite_support := [locals, globals, code, eshapes])`
    qualifier records exactly HOL's four finite-map state fields as
    `HolFiniteMapExact`. `PanSemStateFiniteExact` owns those fields in this
    module, whose `holFmapAsFiniteSupportWitness` proves the roundtrip to its
    broad counterpart. Source review compared every recursive and
    nonrecursive clause, including clock/fix-clock behavior, Dec restoration,
    Call/DecCall result and exception branches, shape/validity checks, FFI and
    shared-memory errors, and finite-map updates. The finite-to-broad
    projection is independently kernel-checked; the evaluator is not routed
    through the production compiler. -/
noncomputable def evaluateHOLFiniteState {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (program : ProgHOL width) :
    Option (PanSemResultExact width) × PanSemStateFiniteExact width σ := by
  classical
  exact evaluateHOLFiniteStateWithDeciders state program

/-- Flapjack-specific bridge: the pair-shaped finite source evaluator does not
depend on which decision procedures were supplied for the two memory domains.
This removes auxiliary Lean instance binders when reusing its clause equations
in the eventual HOL-shaped `evaluate_def` port. -/
theorem evaluateHOLFiniteState_eq_withDeciders {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    [hmem : DecidablePred state.memaddrs]
    [hshared : DecidablePred state.shMemaddrs] (program : ProgHOL width) :
    evaluateHOLFiniteState state program =
      evaluateHOLFiniteStateWithDeciders state program := by
  classical
  have hmemEq : (fun address => Classical.propDecidable (state.memaddrs address)) =
      hmem := by
    funext address
    exact Subsingleton.elim _ _
  have hsharedEq : (fun address => Classical.propDecidable (state.shMemaddrs address)) =
      hshared := by
    funext address
    exact Subsingleton.elim _ _
  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
    hmemEq, hsharedEq]

/-- FLAPJACK-SPECIFIC (no standalone HOL declaration): the general state-level
    projection of the clause-for-clause finite context evaluator. This is the
    reusable bridge that lets a HOL-shaped `evaluate_def` conjunct name the
    recursive result `evaluateHOLFiniteState ...` while its proof works with the
    internal `evalPanSemRecursiveCallFiniteContext` assembly pair. -/
theorem evaluateHOLFiniteState_eq_recursiveContext
    {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (program : ProgHOL width) :
    evaluateHOLFiniteState state program =
      (match evalPanSemRecursiveCallFiniteContext program
          ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
            fun address => Classical.propDecidable (state.shMemaddrs address)⟩ with
        | some pair => (pair.1, pair.2.state)
        | none => (none, state)) := by
  classical
  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders]

/-- FLAPJACK-SPECIFIC (no standalone HOL declaration): state-level reading of a
    known internal recursive-context result. Given an internal assembly pair for
    `program` over any context with the same state, the state-level evaluator
    returns exactly its projection. This is the rewrite that aligns a HOL-shaped
    recursive call `evaluateHOLFiniteState ...` with the internal evaluator's
    post-state context. -/
theorem evaluateHOLFiniteState_eq_of_recursiveContext
    {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (program : ProgHOL width)
    (context : FiniteEvalContext width σ) (hcontext : context.state = state)
    (pair : Option (PanSemResultExact width) × FiniteEvalContext width σ)
    (hpair : evalPanSemRecursiveCallFiniteContext program context = some pair) :
    evaluateHOLFiniteState state program = (pair.1, pair.2.state) := by
  classical
  rw [evaluateHOLFiniteState_eq_recursiveContext]
  have hctx :
      (⟨state, fun address => Classical.propDecidable (state.memaddrs address),
        fun address => Classical.propDecidable (state.shMemaddrs address)⟩ :
        FiniteEvalContext width σ) = context := by
    apply FiniteEvalContext.ext
    exact hcontext.symm
  rw [hctx, hpair]

/-- FLAPJACK-SPECIFIC recursive bridge (no standalone HOL declaration): a
    pair-shaped recursive evaluation equation can be consumed by the finite
    context evaluator while retaining its post-state context. The outer
    `Option` remains internal to this helper and is witnessed as `some`; the
    returned fact exposes only a source result and its state projection. -/
theorem evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
    {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (program : ProgHOL width)
    (context : FiniteEvalContext width σ) (hcontext : context.state = state)
    (output : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
    (houtput : evaluateHOLFiniteState state program = output) :
    ∃ postContext : FiniteEvalContext width σ,
      evalPanSemRecursiveCallFiniteContext program context =
        some (output.1, postContext) ∧ postContext.state = output.2 := by
  classical
  let classicalContext : FiniteEvalContext width σ :=
    ⟨state,
      fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have hcontexts : context = classicalContext := by
    apply FiniteEvalContext.ext
    exact hcontext
  obtain ⟨pair, hpair⟩ :=
    evalPanSemRecursiveCallFiniteContext_total program context
  have hclassicalPair :
      evalPanSemRecursiveCallFiniteContext program classicalContext = some pair := by
    rw [← hcontexts]
    exact hpair
  have hevaluate :
      evaluateHOLFiniteState state program = (pair.1, pair.2.state) := by
    simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
      classicalContext, hclassicalPair]
  have hpairOutput : (pair.1, pair.2.state) = output := hevaluate.symm.trans houtput
  refine ⟨pair.2, ?_, ?_⟩
  · have hresult : pair.1 = output.1 := congrArg Prod.fst hpairOutput
    rw [← hresult]
    exact hpair
  · exact congrArg Prod.snd hpairOutput

/-- Flapjack-specific projection fact: mapping the recursive evaluator's
    assembly `Option` through its pair/state projection commutes with a
    conditional recursive branch. -/
theorem projectFiniteEvalResult_if {width : Nat} {σ : Type} [NeZero width]
    {condition : Prop} [Decidable condition]
    (state : PanSemStateFiniteExact width σ)
    (left right : Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)) :
    (match (if condition then left else right) with
      | some pair => (pair.1, pair.2.state)
      | none => (none, state)) =
      if condition then
        (match left with
          | some pair => (pair.1, pair.2.state)
          | none => (none, state))
      else
        (match right with
          | some pair => (pair.1, pair.2.state)
          | none => (none, state)) := by
  by_cases h : condition <;> simp [h]

/-- HOL `evaluate_def`'s `Skip` equation (the first conjunct of the theorem at
    `panSemScript.sml:780`, whose definition clause is at line 557). This is one
    constructor case of the theorem; the full 21-arm assembly is
    `evaluateHOLFiniteState_eq_evaluate_def` (`PanSem/EvaluateClock.lean`).
    The finite-map qualifier records the four state maps' reviewed canonical
    finite-support representation. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_skip {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    evaluateHOLFiniteState state (.skip : ProgHOL width) = (none, state) := by
  classical
  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
    evalPanSemRecursiveCallFiniteContext]
attribute [simp] evaluateHOLFiniteState_skip

/-! HOL `evaluate_def`'s `Break` equation (the conjunct for the source clause at
`panSemScript.sml:623` in the theorem at line 780). The full 21-arm assembly is
`evaluateHOLFiniteState_eq_evaluate_def` (`PanSem/EvaluateClock.lean`). -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_break {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    evaluateHOLFiniteState state (.break : ProgHOL width) = (some .break, state) := by
  classical
  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
    evalPanSemRecursiveCallFiniteContext]
attribute [simp] evaluateHOLFiniteState_break

/-! HOL `evaluate_def`'s `Continue` equation (the conjunct for the source clause
at `panSemScript.sml:624` in the theorem at line 780). The full 21-arm
assembly is `evaluateHOLFiniteState_eq_evaluate_def`
(`PanSem/EvaluateClock.lean`). -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_continue {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    evaluateHOLFiniteState state (.continue : ProgHOL width) = (some .continue, state) := by
  classical
  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
    evalPanSemRecursiveCallFiniteContext]
attribute [simp] evaluateHOLFiniteState_continue

/-! HOL `evaluate_def`'s `Annot` equation (`panSemScript.sml:656`), one of the
line-780 theorem's 21 conjuncts. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_annot {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (tag text : MlS) :
    evaluateHOLFiniteState state (.annot tag text : ProgHOL width) = (none, state) := by
  classical
  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
    evalPanSemRecursiveCallFiniteContext]

attribute [simp] evaluateHOLFiniteState_annot

/-! HOL `evaluate_def`'s `Tick` equation (`panSemScript.sml:654-655`), one of
the line-780 theorem's 21 conjuncts. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_tick {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    evaluateHOLFiniteState state (.tick : ProgHOL width) =
      (if state.clock = 0 then (some .timeOut, emptyLocalsHOLFinite state)
       else (none, decClockHOLFinite state)) := by
  classical
  by_cases hclock : state.clock = 0
  · simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
      evalPanSemRecursiveCallFiniteContext, hclock]
    rfl
  · simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
      evalPanSemRecursiveCallFiniteContext, hclock]
    rfl

attribute [simp] evaluateHOLFiniteState_tick

/-! HOL `evaluate_def`'s `Return` equation (`panSemScript.sml:638-644`), one of
the line-780 theorem's 21 conjuncts. The expression result uses HOL `eval` via
the canonical broad projection `state.toExact`; the result and state pair are
returned over the finite-support carrier. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_return {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (expression : ExpHOL width) :
    evaluateHOLFiniteState state (.return expression : ProgHOL width) =
      match @evalHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) expression with
      | none => (some .error, state)
      | some value =>
          if Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
              (shapeOfHOLExact value) ≤ 32 then
            (some (.returned value), emptyLocalsHOLFinite state)
          else (some .error, state) := by
  classical
  cases hvalue : @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression with
  | none =>
      simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
        evalPanSemRecursiveCallFiniteContext, hvalue]
  | some value =>
      by_cases hsize : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL
          state.structs (shapeOfHOLExact value) ≤ 32
      · simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
          evalPanSemRecursiveCallFiniteContext, hvalue, hsize]
        rfl
      · simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
          evalPanSemRecursiveCallFiniteContext, hvalue, hsize]

attribute [simp] evaluateHOLFiniteState_return

/-! HOL `evaluate_def`'s `Raise` equation (`panSemScript.sml:645-652`), one of
the line-780 theorem's 21 conjuncts. Its shape test is stated as HOL equality;
the finite evaluator implements that test with `shapeEqHOL`, whose exact
equality bridge is `shapeEqHOL_eq_true`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_raise {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (exceptionId : MlS)
    (expression : ExpHOL width) :
    evaluateHOLFiniteState state (.raise exceptionId expression : ProgHOL width) =
      match state.eshapes.lookup exceptionId,
          @evalHOLExact width σ _ state.toExact
            (fun address => Classical.propDecidable (state.memaddrs address)) expression with
      | some shape, some value =>
          let condition : Prop := shapeOfHOLExact value = shape ∧
            Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
              (shapeOfHOLExact value) ≤ 32
          letI : Decidable condition := Classical.propDecidable condition
          if condition then
            (some (.exception exceptionId value), emptyLocalsHOLFinite state)
          else (some .error, state)
      | _, _ => (some .error, state) := by
  classical
  cases hshape : state.eshapes.lookup exceptionId with
  | none =>
      cases hvalue : @evalHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) expression with
      | none =>
          simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
            evalPanSemRecursiveCallFiniteContext, hvalue]
      | some value =>
          simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
            evalPanSemRecursiveCallFiniteContext, hshape, hvalue]
  | some shape =>
      cases hvalue : @evalHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) expression with
      | none =>
          simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
            evalPanSemRecursiveCallFiniteContext, hvalue]
      | some value =>
          by_cases heq : shapeOfHOLExact value = shape
          · by_cases hsize : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL
                state.structs (shapeOfHOLExact value) ≤ 32
            · have hsizeShape :
                  Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs shape ≤ 32 := by
                simpa [heq] using hsize
              simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                evalPanSemRecursiveCallFiniteContext, hshape, hvalue,
                shapeEqHOL_eq_true, heq, hsizeShape]
              rfl
            · have hsizeShape :
                  ¬ Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs shape ≤ 32 := by
                simpa [heq] using hsize
              simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                evalPanSemRecursiveCallFiniteContext, hshape, hvalue,
                shapeEqHOL_eq_true, heq, hsizeShape]
          · simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
              evalPanSemRecursiveCallFiniteContext, hshape, hvalue,
              shapeEqHOL_eq_true, heq]

attribute [simp] evaluateHOLFiniteState_raise

/-! HOL `evaluate_def`'s `If` equation (`panSemScript.sml:618-622`), one of
the line-780 theorem's 21 conjuncts. The equivalent zero test swaps the two
branches: HOL's `word <> 0w ? then : else` is rendered as
`word = 0 ? else : then` on the exact `BitVec width` carrier. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_ite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (condition : ExpHOL width)
    (thenBranch elseBranch : ProgHOL width) :
    evaluateHOLFiniteState state (.ite condition thenBranch elseBranch) =
      match @evalHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) condition with
      | some (.val (.word word)) =>
          if word = 0 then evaluateHOLFiniteState state elseBranch
          else evaluateHOLFiniteState state thenBranch
      | _ => (some .error, state) := by
  classical
  cases heval : @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) condition with
  | none =>
      simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
        evalPanSemRecursiveCallFiniteContext, heval]
  | some value =>
      cases value with
      | val payload =>
          cases payload with
          | word word =>
              simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                evalPanSemRecursiveCallFiniteContext, heval]
              rw [projectFiniteEvalResult_if]
      | rStruct fields =>
          simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
            evalPanSemRecursiveCallFiniteContext, heval]
      | nStruct name fields =>
          simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
            evalPanSemRecursiveCallFiniteContext, heval]

attribute [simp] evaluateHOLFiniteState_ite

/-! HOL `evaluate_def`'s `Assign` equation (`panSemScript.sml:566-572`), one
of the line-780 theorem's 21 conjuncts. `isValidValueHOLFinite` is the reviewed
Boolean validity test and `setKvarHOLFinite` is the canonical finite update. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_assign {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (kind : VarKind) (name : MlS)
    (source : ExpHOL width) :
    evaluateHOLFiniteState state (.assign kind name source : ProgHOL width) =
      match @evalHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) source with
      | none => (some .error, state)
      | some value =>
          if isValidValueHOLFinite state kind name value then
            (none, setKvarHOLFinite kind name value state)
          else (some .error, state) := by
  classical
  cases heval : @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) source with
  | none =>
      simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
        evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
        evalPanSemNonrecursiveHOLExact, assignStepHOLExact, heval,
        ofExact_toExact]
  | some value =>
      by_cases hvalid : isValidValueHOLFinite state kind name value = true
      · have hsupport :
            (setKvarHOLExact kind name value state.toExact).FiniteSupport :=
          PanSemStateExact.finiteSupport_setKvar state.toExact_finiteSupport kind name value
        have hroundtrip :
            ofExact (setKvarHOLExact kind name value state.toExact) hsupport =
              setKvarHOLFinite kind name value state := by
          cases kind <;> cases state <;>
            simp only [PanSemStateFiniteExact.mk.injEq, ofExact,
              setKvarHOLExact, setKvarHOLFinite, setVarHOLFinite,
              setGlobalHOLFinite]
          all_goals
            repeat' constructor
          all_goals
            apply HolFiniteMapExact.ext
            funext current
            by_cases h : current = name
            · simp [HolFiniteMapExact.update, FUPDATE, h]
            · have h' : name ≠ current := fun h' => h h'.symm
              simp [HolFiniteMapExact.update, FUPDATE, h, h']
        have hvalidWide :
            isValidValueHOLExact state.toExact kind name value = true := by
          simpa only [← isValidValueHOLFinite_eq] using hvalid
        simp [isValidValueHOLFinite_eq, evaluateHOLFiniteState,
          evaluateHOLFiniteStateWithDeciders,
          evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
          evalPanSemNonrecursiveHOLExact, assignStepHOLExact, heval, hvalidWide, hroundtrip]
      · have hinvalid : isValidValueHOLFinite state kind name value = false :=
          Bool.eq_false_iff.mpr hvalid
        have hinvalidWide :
            isValidValueHOLExact state.toExact kind name value = false := by
          simpa only [← isValidValueHOLFinite_eq] using hinvalid
        simp [isValidValueHOLFinite_eq, evaluateHOLFiniteState,
          evaluateHOLFiniteStateWithDeciders,
          evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
          evalPanSemNonrecursiveHOLExact, assignStepHOLExact, heval, hinvalidWide,
          ofExact_toExact]

attribute [simp] evaluateHOLFiniteState_assign

/-! HOL `evaluate_def`'s `Store` equation (`panSemScript.sml:583-589`), one
of the line-780 theorem's 21 conjuncts. Both expressions use the original
state, writes use `mem_stores` over the exact memory domain, and failed
evaluation or an out-of-domain write returns `Error` with the original state. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_store {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (destination source : ExpHOL width) :
    evaluateHOLFiniteState state (.store destination source : ProgHOL width) =
      match @evalHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) destination with
      | some (.val (.word address)) =>
          match @evalHOLExact width σ _ state.toExact
              (fun address => Classical.propDecidable (state.memaddrs address)) source with
          | some value =>
              match @panMemStoresHOL width _ address (flattenHOL value) state.memaddrs
                  (fun address => Classical.propDecidable (state.memaddrs address)) state.memory with
              | some memory => (none, { state with memory := memory })
              | none => (some .error, state)
          | none => (some .error, state)
      | _ => (some .error, state) := by
  classical
  cases hevalDestination : @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) destination with
  | none =>
      simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
        evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
        evalPanSemNonrecursiveHOLExact, storeStepHOLExact, hevalDestination,
        ofExact_toExact]
  | some destinationValue =>
      cases destinationValue with
      | val destinationPayload =>
          cases destinationPayload with
          | word address =>
              cases hevalSource : @evalHOLExact width σ _ state.toExact
                  (fun address => Classical.propDecidable (state.memaddrs address)) source with
              | none =>
                  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                    evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
                    evalPanSemNonrecursiveHOLExact, storeStepHOLExact,
                    hevalDestination, hevalSource, ofExact_toExact]
              | some value =>
                  cases hmemory : @panMemStoresHOL width _ address (flattenHOL value)
                      state.memaddrs
                      (fun address => Classical.propDecidable (state.memaddrs address))
                      state.memory with
                  | none =>
                      simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                        evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
                        evalPanSemNonrecursiveHOLExact, storeStepHOLExact,
                        hevalDestination, hevalSource, hmemory, ofExact_toExact]
                  | some memory =>
                      have hsupport :
                          ({ state.toExact with memory := memory } : PanSemStateExact width σ).FiniteSupport :=
                        state.toExact_finiteSupport
                      have hroundtrip :
                          ofExact ({ state.toExact with memory := memory }) hsupport =
                            { state with memory := memory } := by
                        cases state
                        rfl
                      simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                        evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
                        evalPanSemNonrecursiveHOLExact, storeStepHOLExact,
                        hevalDestination, hevalSource, hmemory, hroundtrip]
      | rStruct _ | nStruct _ _ =>
          simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
            evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
            evalPanSemNonrecursiveHOLExact, storeStepHOLExact,
            hevalDestination, ofExact_toExact]

attribute [simp] evaluateHOLFiniteState_store

/-! HOL `evaluate_def`'s `Store32` equation (`panSemScript.sml:590-596`), one
of the line-780 theorem's 21 conjuncts. It evaluates both expressions against
the original state, requires word values, and preserves the state on every
failure. HOL `w2w` is the low 32 bits, expressed as `BitVec.ofNat 32`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_store32 {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (destination source : ExpHOL width) :
    evaluateHOLFiniteState state (.store32 destination source : ProgHOL width) =
      match @evalHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) destination with
      | some (.val (.word address)) =>
          match @evalHOLExact width σ _ state.toExact
              (fun address => Classical.propDecidable (state.memaddrs address)) source with
          | some (.val (.word value)) =>
              match @panMemStore32HOL width _ state.memory state.memaddrs
                  (fun address => Classical.propDecidable (state.memaddrs address))
                  state.be address (BitVec.ofNat 32 value.toNat) with
              | some memory => (none, { state with memory := memory })
              | none => (some .error, state)
          | _ => (some .error, state)
      | _ => (some .error, state) := by
  classical
  cases hevalDestination : @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) destination with
  | none =>
      simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
        evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
        evalPanSemNonrecursiveHOLExact, store32StepHOLExact, hevalDestination,
        ofExact_toExact]
  | some destinationValue =>
      cases destinationValue with
      | val destinationPayload =>
          cases destinationPayload with
          | word address =>
              cases hevalSource : @evalHOLExact width σ _ state.toExact
                  (fun address => Classical.propDecidable (state.memaddrs address)) source with
              | none =>
                  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                    evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
                    evalPanSemNonrecursiveHOLExact, store32StepHOLExact,
                    hevalDestination, hevalSource, ofExact_toExact]
              | some value =>
                  cases value with
                  | val payload =>
                      cases payload with
                      | word value =>
                          cases hmemory : @panMemStore32HOL width _ state.memory
                              state.memaddrs
                              (fun address => Classical.propDecidable (state.memaddrs address))
                              state.be address (BitVec.ofNat 32 value.toNat) with
                          | none =>
                              have hmemory' : @panMemStore32HOL width _ state.memory
                                  state.memaddrs
                                  (fun address => Classical.propDecidable (state.memaddrs address))
                                  state.be address (BitVec.setWidth 32 value) = none := by
                                simpa using hmemory
                              simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                                evalPanSemRecursiveCallFiniteContext,
                                evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact,
                                store32StepHOLExact, hevalDestination, hevalSource, hmemory',
                                ofExact_toExact]
                          | some memory =>
                              have hmemory' : @panMemStore32HOL width _ state.memory
                                  state.memaddrs
                                  (fun address => Classical.propDecidable (state.memaddrs address))
                                  state.be address (BitVec.setWidth 32 value) = some memory := by
                                simpa using hmemory
                              have hsupport :
                                  ({ state.toExact with memory := memory } :
                                    PanSemStateExact width σ).FiniteSupport :=
                                state.toExact_finiteSupport
                              have hroundtrip :
                                  ofExact ({ state.toExact with memory := memory }) hsupport =
                                    { state with memory := memory } := by
                                cases state
                                rfl
                              simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                                evalPanSemRecursiveCallFiniteContext,
                                evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact,
                                store32StepHOLExact, hevalDestination, hevalSource, hmemory',
                                hroundtrip]
                  | rStruct _ | nStruct _ _ =>
                      simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                        evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
                        evalPanSemNonrecursiveHOLExact, store32StepHOLExact,
                        hevalDestination, hevalSource, ofExact_toExact]
      | rStruct _ | nStruct _ _ =>
          simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
            evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
            evalPanSemNonrecursiveHOLExact, store32StepHOLExact,
            hevalDestination, ofExact_toExact]

attribute [simp] evaluateHOLFiniteState_store32

/-! HOL `evaluate_def`'s `StoreByte` equation (`panSemScript.sml:597-603`),
one of the line-780 theorem's 21 conjuncts. The byte argument is HOL `word8`
(Lean `BitVec 8`) after `w2w`; the exact memory helper preserves the aligned
cell update and every untouched cell. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_storeByte {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (destination source : ExpHOL width) :
    evaluateHOLFiniteState state (.storeByte destination source : ProgHOL width) =
      match @evalHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) destination with
      | some (.val (.word address)) =>
          match @evalHOLExact width σ _ state.toExact
              (fun address => Classical.propDecidable (state.memaddrs address)) source with
          | some (.val (.word value)) =>
              match @panMemStoreByteWord8HOL width _ state.memory state.memaddrs
                  (fun address => Classical.propDecidable (state.memaddrs address))
                  state.be address (BitVec.ofNat 8 value.toNat) with
              | some memory => (none, { state with memory := memory })
              | none => (some .error, state)
          | _ => (some .error, state)
      | _ => (some .error, state) := by
  classical
  cases hevalDestination : @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) destination with
  | none =>
      simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
        evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
        evalPanSemNonrecursiveHOLExact, storeByteStepHOLExact, hevalDestination,
        ofExact_toExact]
  | some destinationValue =>
      cases destinationValue with
      | val destinationPayload =>
          cases destinationPayload with
          | word address =>
              cases hevalSource : @evalHOLExact width σ _ state.toExact
                  (fun address => Classical.propDecidable (state.memaddrs address)) source with
              | none =>
                  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                    evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
                    evalPanSemNonrecursiveHOLExact, storeByteStepHOLExact,
                    hevalDestination, hevalSource, ofExact_toExact]
              | some value =>
                  cases value with
                  | val payload =>
                      cases payload with
                      | word value =>
                          cases hmemory : @panMemStoreByteWord8HOL width _ state.memory
                              state.memaddrs
                              (fun address => Classical.propDecidable (state.memaddrs address))
                              state.be address (BitVec.ofNat 8 value.toNat) with
                          | none =>
                              have hmemoryExact : @panMemStoreByteWord8HOL width _ state.memory
                                  state.memaddrs
                                  (fun address => Classical.propDecidable (state.memaddrs address))
                                  state.be address (BitVec.setWidth 8 value) = none := by
                                simpa using hmemory
                              have hmemory' : @panMemStoreByteHOL width _ state.memory
                                  state.memaddrs
                                  (fun address => Classical.propDecidable (state.memaddrs address))
                                  state.be address (UInt8.ofNat value.toNat) = none := by
                                rw [panMemStoreByteHOL_eq_word8]
                                have hbyte : (UInt8.ofNat value.toNat).toBitVec =
                                    BitVec.ofNat 8 value.toNat := by
                                  rfl
                                rw [hbyte]
                                exact hmemory
                              simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                                evalPanSemRecursiveCallFiniteContext,
                                evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact,
                                storeByteStepHOLExact, hevalDestination, hevalSource, hmemory',
                                hmemoryExact,
                                ofExact_toExact]
                          | some memory =>
                              have hmemoryExact : @panMemStoreByteWord8HOL width _ state.memory
                                  state.memaddrs
                                  (fun address => Classical.propDecidable (state.memaddrs address))
                                  state.be address (BitVec.setWidth 8 value) = some memory := by
                                simpa using hmemory
                              have hmemory' : @panMemStoreByteHOL width _ state.memory
                                  state.memaddrs
                                  (fun address => Classical.propDecidable (state.memaddrs address))
                                  state.be address (UInt8.ofNat value.toNat) = some memory := by
                                rw [panMemStoreByteHOL_eq_word8]
                                have hbyte : (UInt8.ofNat value.toNat).toBitVec =
                                    BitVec.ofNat 8 value.toNat := by
                                  rfl
                                rw [hbyte]
                                exact hmemory
                              have hsupport :
                                  ({ state.toExact with memory := memory } :
                                    PanSemStateExact width σ).FiniteSupport :=
                                state.toExact_finiteSupport
                              have hroundtrip :
                                  ofExact ({ state.toExact with memory := memory }) hsupport =
                                    { state with memory := memory } := by
                                cases state
                                rfl
                              simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                                evalPanSemRecursiveCallFiniteContext,
                                evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact,
                                storeByteStepHOLExact, hevalDestination, hevalSource, hmemory',
                                hmemoryExact,
                                hroundtrip]
                  | rStruct _ | nStruct _ _ =>
                      simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                        evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
                        evalPanSemNonrecursiveHOLExact, storeByteStepHOLExact,
                        hevalDestination, hevalSource, ofExact_toExact]
      | rStruct _ | nStruct _ _ =>
          simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
            evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
            evalPanSemNonrecursiveHOLExact, storeByteStepHOLExact,
            hevalDestination, ofExact_toExact]

attribute [simp] evaluateHOLFiniteState_storeByte

/-! HOL `evaluate_def`'s `Primitive` equation (`panSemScript.sml:573-582`),
one of the line-780 theorem's 21 conjuncts. Argument expressions use
`OPT_MMAP eval`; `panPrimopHOLExact` is the tagged exact `pan_primop` port,
and a valid result updates only locals. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_primitive {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (name : MlS) (operator : PrimOp)
    (arguments : List (ExpHOL width)) :
    evaluateHOLFiniteState state (.primitive name operator arguments : ProgHOL width) =
      match @evalListHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) arguments with
      | none => (some .error, state)
      | some values =>
          match panPrimopHOLExact operator values with
          | none => (some .error, state)
          | some value =>
              if isValidValueHOLFinite state .local name value then
                (none, setVarHOLFinite name value state)
              else (some .error, state) := by
  classical
  cases heval : @evalListHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) arguments with
  | none =>
      simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
        evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
        evalPanSemNonrecursiveHOLExact, primitiveStepHOLExact, heval,
        ofExact_toExact]
  | some values =>
      cases hprim : panPrimopHOLExact operator values with
      | none =>
          simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
            evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
            evalPanSemNonrecursiveHOLExact, primitiveStepHOLExact, heval, hprim,
            ofExact_toExact]
      | some value =>
          by_cases hvalid : isValidValueHOLFinite state .local name value = true
          · have hsupport :
                (setVarHOLExact name value state.toExact).FiniteSupport :=
              PanSemStateExact.finiteSupport_setVar state.toExact_finiteSupport name value
            have hroundtrip :
                ofExact (setVarHOLExact name value state.toExact) hsupport =
                  setVarHOLFinite name value state := by
              cases state <;>
                simp only [PanSemStateFiniteExact.mk.injEq, ofExact,
                  setVarHOLExact, setVarHOLFinite]
              all_goals repeat' constructor
              all_goals
                apply HolFiniteMapExact.ext
                funext current
                by_cases h : current = name
                · simp [HolFiniteMapExact.update, FUPDATE, h]
                · have h' : name ≠ current := fun h' => h h'.symm
                  simp [HolFiniteMapExact.update, FUPDATE, h, h']
            have hvalidWide :
                isValidValueHOLExact state.toExact .local name value = true := by
              simpa only [← isValidValueHOLFinite_eq] using hvalid
            simp [isValidValueHOLFinite_eq, evaluateHOLFiniteState,
              evaluateHOLFiniteStateWithDeciders,
              evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
              evalPanSemNonrecursiveHOLExact, primitiveStepHOLExact,
              heval, hprim, hvalidWide, hroundtrip]
          · have hinvalid :
                isValidValueHOLFinite state .local name value = false :=
              Bool.eq_false_iff.mpr hvalid
            have hinvalidWide :
                isValidValueHOLExact state.toExact .local name value = false := by
              simpa only [← isValidValueHOLFinite_eq] using hinvalid
            simp [isValidValueHOLFinite_eq, evaluateHOLFiniteState,
              evaluateHOLFiniteStateWithDeciders,
              evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
              evalPanSemNonrecursiveHOLExact, primitiveStepHOLExact,
              heval, hprim, hinvalidWide, ofExact_toExact]

attribute [simp] evaluateHOLFiniteState_primitive

/-- Flapjack-specific carrier wrapper for the exact HOL ShMemLoad clause.
    Keeping the broad evaluator closure behind this helper leaves the tagged
    finite-carrier theorem unambiguously owned by `PanSemStateFiniteExact`.
    The HOL clause itself is tagged on the equation below. -/
noncomputable def shMemLoadClauseHOLFiniteExact {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ) (operator : OpSize)
    (kind : VarKind) (name : MlS) (address : ExpHOL width) :=
  let evalExpression := fun (_ : PanSemStateExact width σ) (expression : ExpHOL width) =>
    @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression
  @shMemLoadClauseHOLExact width σ _ state.toExact
    (fun address => Classical.propDecidable (state.shMemaddrs address))
    operator kind name address evalExpression

/-- Flapjack-specific support transport for the finite-carrier wrapper;
    HOL has no separate finite-support proposition. -/
theorem shMemLoadClauseHOLFiniteExact_finiteSupport {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ) (operator : OpSize)
    (kind : VarKind) (name : MlS) (address : ExpHOL width) :
    (shMemLoadClauseHOLFiniteExact state operator kind name address).2.FiniteSupport := by
  unfold shMemLoadClauseHOLFiniteExact
  exact @shMemLoadClauseHOLExact_finiteSupport width σ _ state.toExact
    (fun address => Classical.propDecidable (state.shMemaddrs address))
    operator kind name address
    (fun (_ : PanSemStateExact width σ) (expression : ExpHOL width) =>
      @evalHOLExact width σ _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) expression)
    state.toExact_finiteSupport

/-- Flapjack-specific carrier wrapper for the exact HOL ShMemStore clause.
    It is not a separate HOL declaration: the executable clause is
    `shMemStoreClauseHOLExact`, and the HOL `evaluate_def` equation is tagged
    below. Keeping the broad evaluator closure here leaves the tagged
    finite-carrier theorem unambiguously owned by `PanSemStateFiniteExact`. -/
noncomputable def shMemStoreClauseHOLFiniteExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (operator : OpSize)
    (address value : ExpHOL width) :=
  let evalExpression := fun (_ : PanSemStateExact width σ) (expression : ExpHOL width) =>
    @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression
  @shMemStoreClauseHOLExact width σ _ state.toExact
    (fun address => Classical.propDecidable (state.shMemaddrs address))
    operator address value evalExpression

/-- Flapjack-specific support transport for the finite-carrier wrapper above;
    HOL has no separate finite-support proposition. -/
theorem shMemStoreClauseHOLFiniteExact_finiteSupport {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ) (operator : OpSize)
    (address value : ExpHOL width) :
    (shMemStoreClauseHOLFiniteExact state operator address value).2.FiniteSupport := by
  unfold shMemStoreClauseHOLFiniteExact
  exact @shMemStoreClauseHOLExact_finiteSupport width σ _ state.toExact
    (fun address => Classical.propDecidable (state.shMemaddrs address))
    operator address value
    (fun (_ : PanSemStateExact width σ) (expression : ExpHOL width) =>
      @evalHOLExact width σ _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) expression)
    state.toExact_finiteSupport

/-- Flapjack-specific equation for the finite-carrier ShMemLoad evaluator.
    This is not tagged as HOL `evaluate_def`: its right-hand side hides the
    explicit source branches behind `shMemLoadClauseHOLFiniteExact`. The
    HOL-shaped case is restated and tagged as
    `evaluateHOLFiniteState_shMemLoad_source` below. -/
theorem evaluateHOLFiniteState_shMemLoad {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (operator : OpSize) (kind : VarKind)
    (name : MlS) (address : ExpHOL width) :
    let output := shMemLoadClauseHOLFiniteExact state operator kind name address
    evaluateHOLFiniteState state (.shMemLoad operator kind name address : ProgHOL width) =
      (output.1, ofExact output.2
        (shMemLoadClauseHOLFiniteExact_finiteSupport state operator kind name address)) := by
  classical
  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
    evalPanSemRecursiveCallFiniteContext, shMemLoadClauseHOLFiniteExact]
  rfl

attribute [simp] evaluateHOLFiniteState_shMemLoad

/-- Flapjack-specific proof-irrelevance bridge used to repack results from the
    broad finite-support subtype. HOL has no declaration for this proof
    plumbing. -/
private theorem ofExact_toExact_any {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (support : state.toExact.FiniteSupport) :
    PanSemStateFiniteExact.ofExact state.toExact support = state := by
  cases state
  rfl

/-- Flapjack-specific proof-irrelevance bridge for the empty-locals update.
    HOL has no declaration for this carrier repacking proof. -/
private theorem ofExact_emptyLocals_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    PanSemStateFiniteExact.ofExact (Flapjack.emptyLocalsHOLExact state.toExact)
      (PanSemStateExact.finiteSupport_emptyLocals state.toExact_finiteSupport) =
      PanSemStateFiniteExact.emptyLocalsHOLFinite state := by
  cases state
  rfl

/-- HOL `evaluate_def`'s ShMemLoad conjunct (`panSemScript.sml:605-610`,
    restated by the equation theorem at line 780). The address is evaluated
    first, then `lookup_kvar`; only a word address and word destination call
    `sh_mem_load_def` with `nb_op op`. Every failed match returns
    `(SOME Error, s)`. The statement directly names the finite-carrier helper.
    This theorem is placed beside `PanSemStateFiniteExact`, which owns the four
    `HolFiniteMapExact` fields recorded by the qualifier and the canonical
    same-module witness `holFmapAsFiniteSupportWitness`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_shMemLoad_source {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    (operator : OpSize) (kind : VarKind) (name : MlS)
    (address : ExpHOL width) :
    evaluateHOLFiniteState state
        (.shMemLoad operator kind name address : ProgHOL width) =
      match @evalHOLFinite width σ _ state
          (fun current => Classical.propDecidable (state.memaddrs current)) address with
      | some (.val (.word addr)) =>
          match lookupKvarHOLFinite kind name state with
          | some (.val (.word _)) =>
              let loaded := @shMemLoadHOLFiniteExact width σ _ state
                (fun current => Classical.propDecidable (state.shMemaddrs current))
                kind name addr (nbOpHOL operator)
              (loaded.1, loaded.2)
          | _ => (some .error, state)
      | _ => (some .error, state) := by
  classical
  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
    evalPanSemRecursiveCallFiniteContext,
    Flapjack.shMemLoadClauseHOLExact,
    evalHOLFinite_eq_toExact] <;>
    repeat' split <;> simp_all <;> try apply ofExact_toExact_any
  case h_1 =>
    exact (Prod.mk.inj
      (shMemLoadHOLFiniteExact_repack state kind name _ (nbOpHOL operator)))

/-- HOL `evaluate_def`'s `ExtCall` equation (`panSemScript.sml:711-726`,
    restated at line 780). It preserves the four ordered expression checks,
    both byte-array reads, the `call_FFI` split, and the returned-memory/FFI
    update. This tagged declaration is placed beside `PanSemStateFiniteExact`,
    which owns its four `HolFiniteMapExact` fields and the same-module canonical
    witness `holFmapAsFiniteSupportWitness`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_extCall_source {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    (function : MlS) (configuration configurationLength array arrayLength : ExpHOL width) :
    evaluateHOLFiniteState state
        (.extCall function configuration configurationLength array arrayLength : ProgHOL width) =
      match
        @evalHOLFinite width σ _ state
          (fun address => Classical.propDecidable (state.memaddrs address)) configuration,
        @evalHOLFinite width σ _ state
          (fun address => Classical.propDecidable (state.memaddrs address)) configurationLength,
        @evalHOLFinite width σ _ state
          (fun address => Classical.propDecidable (state.memaddrs address)) array,
        @evalHOLFinite width σ _ state
          (fun address => Classical.propDecidable (state.memaddrs address)) arrayLength with
      | some (.val (.word address1)), some (.val (.word length1)),
        some (.val (.word address2)), some (.val (.word length2)) =>
          match
            readBytearrayWordHOL (byteWidth := 8) address1 length1.toNat
              (@panMemLoadByteWord8HOL width _ state.memory state.memaddrs
                (fun address => Classical.propDecidable (state.memaddrs address)) state.be),
            readBytearrayWordHOL (byteWidth := 8) address2 length2.toNat
              (@panMemLoadByteWord8HOL width _ state.memory state.memaddrs
                (fun address => Classical.propDecidable (state.memaddrs address)) state.be) with
          | some bytes1, some bytes2 =>
              match callFFIHOL state.ffi (.extCall function) bytes1 bytes2 with
              | .final event =>
                  (some (.finalFfi event), emptyLocalsHOLFinite state)
              | .ret newFfi newBytes =>
                  let nextState : PanSemStateExact width σ :=
                    { state.toExact with
                      memory := @panWriteBytearrayWord8HOL width _ address2 newBytes
                        state.memory state.memaddrs
                        (fun address => Classical.propDecidable (state.memaddrs address))
                        state.be
                      ffi := newFfi }
                  (none, PanSemStateFiniteExact.ofExact nextState (by
                    change nextState.FiniteSupport
                    simpa [nextState, PanSemStateExact.FiniteSupport] using
                      state.toExact_finiteSupport))
          | _, _ => (some .error, state)
      | _, _, _, _ => (some .error, state) := by
  classical
  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
    evalPanSemRecursiveCallFiniteContext, evalPanSemNonrecursiveHOLFinite,
    evalPanSemNonrecursiveHOLExact, extCallStepHOLExact] <;>
    repeat' split <;> simp_all
  all_goals
    first
    | exact ofExact_emptyLocals_toExact state
    | exact ofExact_toExact (emptyLocalsHOLFinite state)
    | apply ofExact_toExact_any

/-- Flapjack-specific equation for the finite-carrier ShMemStore evaluator.
    This is not tagged as HOL `evaluate_def`: its right-hand side hides the
    explicit source branches behind `shMemStoreClauseHOLFiniteExact`. The
    HOL-shaped case is restated and tagged as
    `evaluateHOLFiniteState_shMemStore_total` below. -/
theorem evaluateHOLFiniteState_shMemStore {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (operator : OpSize)
    (address value : ExpHOL width) :
    let output := shMemStoreClauseHOLFiniteExact state operator address value
    evaluateHOLFiniteState state (.shMemStore operator address value : ProgHOL width) =
      (output.1, ofExact output.2
        (shMemStoreClauseHOLFiniteExact_finiteSupport state operator address value)) := by
  classical
  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
    evalPanSemRecursiveCallFiniteContext, shMemStoreClauseHOLFiniteExact]
  rfl

attribute [simp] evaluateHOLFiniteState_shMemStore

/-- Source-reviewed HOL `evaluate_def` ShMemStore conjunct
    (`panSemScript.sml:611-614`, theorem restatement at line 780). Both
    expressions are evaluated in the original state; only two word values call
    exact `shMemStoreHOLExact` with the source byte count, address and
    `nb_op`. Every other evaluation/value pair returns Error with the original
    state. The success state is rebuilt on the finite carrier using its
    kernel-checked finite-support result. The four named state maps use the
    same-module canonical finite-support witness. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_shMemStore_total {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (operator : OpSize)
    (address value : ExpHOL width) :
    evaluateHOLFiniteState state (.shMemStore operator address value : ProgHOL width) =
      (let hshmem : DecidablePred state.shMemaddrs :=
        fun key => Classical.propDecidable (state.shMemaddrs key)
       let evalAddress := @evalHOLExact width σ _ state.toExact
         (fun key => Classical.propDecidable (state.memaddrs key)) address
       let evalValue := @evalHOLExact width σ _ state.toExact
         (fun key => Classical.propDecidable (state.memaddrs key)) value
       match evalAddress, evalValue with
       | some (.val (.word addr)), some (.val (.word bytes)) =>
           let output := shMemStoreHOLExact state.toExact bytes addr (nbOpHOL operator)
           (output.1, ofExact output.2
             (@shMemStoreHOLExact_finiteSupport width σ _ state.toExact hshmem
               bytes addr (nbOpHOL operator) state.toExact_finiteSupport))
       | _, _ => (some .error, state)) := by
  classical
  let evalAddress := @evalHOLExact width σ _ state.toExact
    (fun key => Classical.propDecidable (state.memaddrs key)) address
  let evalValue := @evalHOLExact width σ _ state.toExact
    (fun key => Classical.propDecidable (state.memaddrs key)) value
  cases haddress : evalAddress with
  | none =>
      simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
        evalPanSemRecursiveCallFiniteContext, shMemStoreClauseHOLExact,
        evalAddress, haddress, ofExact_toExact]
  | some addressResult =>
      cases addressResult with
      | rStruct fields =>
          simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
            evalPanSemRecursiveCallFiniteContext, shMemStoreClauseHOLExact,
            evalAddress, haddress, ofExact_toExact]
      | nStruct structName fields =>
          simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
            evalPanSemRecursiveCallFiniteContext, shMemStoreClauseHOLExact,
            evalAddress, haddress, ofExact_toExact]
      | val addressWord =>
          cases addressWord with
          | word addr =>
              cases hvalue : evalValue with
              | none =>
                  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                    evalPanSemRecursiveCallFiniteContext, shMemStoreClauseHOLExact,
                    evalAddress, evalValue, haddress, hvalue, ofExact_toExact]
              | some valueResult =>
                  cases valueResult with
                  | rStruct fields =>
                      simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                        evalPanSemRecursiveCallFiniteContext, shMemStoreClauseHOLExact,
                        evalAddress, evalValue, haddress, hvalue, ofExact_toExact]
                  | nStruct structName fields =>
                      simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                        evalPanSemRecursiveCallFiniteContext, shMemStoreClauseHOLExact,
                        evalAddress, evalValue, haddress, hvalue, ofExact_toExact]
                  | val valueWord =>
                      cases valueWord with
                      | word bytes =>
                          simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                            evalPanSemRecursiveCallFiniteContext, evalAddress, evalValue,
                            haddress, hvalue, shMemStoreClauseHOLExact]

/-- Flapjack-specific finite-carrier rendering of HOL's `Dec` clause. The
    recursive body call and restoration step mirror `evaluate_def`; the
    `resVarEq` update is the canonical finite-map form of HOL `res_var`. The
    optional assembly marker makes its equation unsuitable as the HOL theorem
    statement, so it remains untagged infrastructure. -/
noncomputable def evaluateDecClauseHOLFiniteExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (name : MlS) (shape : ShapeHOL)
    (initializer : ExpHOL width) (body : ProgHOL width) :
    Option (PanSemResultExact width) × PanSemStateFiniteExact width σ := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  exact match evalHOLFinite state initializer with
    | none => (some .error, state)
    | some value =>
        if shapeEqHOL shape (shapeOfHOLExact value) then
          let bodyState := setVarHOLFinite name value state
          let bodyContext := context.withState bodyState rfl rfl
          match evalPanSemRecursiveCallFiniteContext body bodyContext with
          | none => (none, state)
          | some (result, postContext) =>
              let restored : PanSemStateFiniteExact width σ :=
                { postContext.state with
                  locals := HolFiniteMapExact.resVarEq postContext.state.locals
                    (name, state.locals.lookup name) }
              (result, (postContext.withState restored rfl rfl).state)
        else (some .error, state)

/-! Flapjack-specific finite-carrier `Dec` equation. This declaration is not
tagged as HOL `evaluate_def`: the internal optional assembly-marker result of
`evalPanSemRecursiveCallFiniteContext` leaves an extra unreachable `none`
branch in its statement. The HOL-shaped total pair case is restated and
tagged as `evaluateHOLFiniteState_dec_total` below; keep
`evaluateDecClauseHOLFiniteExact` as infrastructure. -/
theorem evaluateHOLFiniteState_dec {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (name : MlS) (shape : ShapeHOL)
    (initializer : ExpHOL width) (body : ProgHOL width) :
    evaluateHOLFiniteState state (.dec name shape initializer body : ProgHOL width) =
      (let context : FiniteEvalContext width σ :=
        ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
          fun address => Classical.propDecidable (state.shMemaddrs address)⟩
       match @evalHOLExact width σ _ state.toExact context.memaddrsDecidable initializer with
       | none => (some .error, state)
       | some value =>
           if shapeEqHOL shape (shapeOfHOLExact value) then
             let bodyState := setVarHOLFinite name value state
             let bodyContext := context.withState bodyState rfl rfl
             match evalPanSemRecursiveCallFiniteContext body bodyContext with
             | none => (none, state)
             | some (result, postContext) =>
                 let restored : PanSemStateFiniteExact width σ :=
                   { postContext.state with
                     locals := HolFiniteMapExact.resVarEq postContext.state.locals
                       (name, state.locals.lookup name) }
                 (result, (postContext.withState restored rfl rfl).state)
           else (some .error, state)) := by
  classical
  let hmem : DecidablePred state.memaddrs :=
    fun address => Classical.propDecidable (state.memaddrs address)
  let hshared : DecidablePred state.shMemaddrs :=
    fun address => Classical.propDecidable (state.shMemaddrs address)
  letI : DecidablePred state.memaddrs := hmem
  letI : DecidablePred state.shMemaddrs := hshared
  cases hinit : @evalHOLExact width σ _ state.toExact hmem initializer with
  | none =>
      simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
        evalPanSemRecursiveCallFiniteContext, hinit]
  | some value =>
      by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value) = true
      · cases hbody : evalPanSemRecursiveCallFiniteContext body
          (({ state := state,
              memaddrsDecidable := fun address => Classical.propDecidable (state.memaddrs address),
              shMemaddrsDecidable := fun address => Classical.propDecidable (state.shMemaddrs address) } :
            FiniteEvalContext width σ).withState (setVarHOLFinite name value state) rfl rfl) with
        | none =>
            simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
              evalPanSemRecursiveCallFiniteContext,
              hinit, hshape, hbody]
        | some pair =>
            simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
              evalPanSemRecursiveCallFiniteContext,
              hinit, hshape, hbody]
      · simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
          evalPanSemRecursiveCallFiniteContext,
          hinit, hshape]

attribute [simp] evaluateHOLFiniteState_dec

/-- Source-reviewed HOL `evaluate_def` Dec conjunct (`panSemScript.sml:558-565`,
    theorem restatement at line 780). It exposes initializer failure, the
    shape-equality check, the total recursive body pair, and restoration of the
    original binding with `res_var`; no recursive assembly-marker branch or
    semantic premise is present. HOL `FLOOKUP` and `FUPDATE` are represented by
    the finite map's `lookup` and `resVarEq`. The four named state maps use the
    same-module canonical finite-support witness. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_dec_total {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (name : MlS) (shape : ShapeHOL)
    (initializer : ExpHOL width) (body : ProgHOL width) :
    evaluateHOLFiniteState state (.dec name shape initializer body : ProgHOL width) =
      (let context : FiniteEvalContext width σ :=
        ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
          fun address => Classical.propDecidable (state.shMemaddrs address)⟩
       match @evalHOLExact width σ _ state.toExact context.memaddrsDecidable initializer with
       | none => (some .error, state)
       | some value =>
           if shapeEqHOL shape (shapeOfHOLExact value) then
             let bodyState := setVarHOLFinite name value state
             let bodyOutput := evaluateHOLFiniteState bodyState body
             (bodyOutput.1,
               { bodyOutput.2 with
                 locals := HolFiniteMapExact.resVarEq bodyOutput.2.locals
                   (name, state.locals.lookup name) })
           else (some .error, state)) := by
  classical
  let hmem : DecidablePred state.memaddrs :=
    fun address => Classical.propDecidable (state.memaddrs address)
  let hshared : DecidablePred state.shMemaddrs :=
    fun address => Classical.propDecidable (state.shMemaddrs address)
  let context : FiniteEvalContext width σ := ⟨state, hmem, hshared⟩
  cases hinit : @evalHOLExact width σ _ state.toExact hmem initializer with
  | none =>
      simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
        evalPanSemRecursiveCallFiniteContext, hinit, hmem]
  | some value =>
      by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value) = true
      · let bodyState := setVarHOLFinite name value state
        let bodyContext := context.withState bodyState rfl rfl
        obtain ⟨bodyPair, hbody⟩ :=
          evalPanSemRecursiveCallFiniteContext_total body bodyContext
        have hbodyContextClassical : bodyContext =
            (⟨bodyState,
              fun address => Classical.propDecidable (bodyState.memaddrs address),
              fun address => Classical.propDecidable (bodyState.shMemaddrs address)⟩ :
              FiniteEvalContext width σ) := by
          apply FiniteEvalContext.ext
          rfl
        have hbodyGlobal : evalPanSemRecursiveCallFiniteContext body
            (⟨bodyState,
              fun address => Classical.propDecidable (bodyState.memaddrs address),
              fun address => Classical.propDecidable (bodyState.shMemaddrs address)⟩ :
              FiniteEvalContext width σ) = some bodyPair := by
          rw [← hbodyContextClassical]
          exact hbody
        have hbodyExpr : evalPanSemRecursiveCallFiniteContext body
            (context.withState bodyState rfl rfl) = some bodyPair := by
          simpa [bodyContext, bodyState] using hbody
        have hbodyOutput : evaluateHOLFiniteState bodyState body =
            (bodyPair.1, bodyPair.2.state) := by
          simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
            hbodyGlobal]
        change (match evalPanSemRecursiveCallFiniteContext
          (.dec name shape initializer body) context with
          | some pair => (pair.1, pair.2.state)
          | none => (none, state)) = _
        rw [evalPanSemRecursiveCallFiniteContext.eq_def]
        simp only [evalHOLFinite, hinit, hshape, if_true, context, bodyState, hbodyExpr]
        rw [hbodyOutput]
        rfl
      · simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
          evalPanSemRecursiveCallFiniteContext, hinit, hshape,
          hmem]

/-- Flapjack-specific DecCall argument-failure helper for the HOL clause at
    `panSemScript.sml:694-714`. The `hargs` branch selector is an additional
    hypothesis absent from HOL's unconditional `evaluate_def` conjunct, so this
    helper is not tagged as a port of that declaration. -/
theorem evaluateHOLFiniteState_decCall_args_none {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = none) :
    evaluateHOLFiniteState state
        (.decCall resultName shape function arguments continuation : ProgHOL width) =
      (some .error, state) := by
  classical
  have hargsExact :
      @evalListHOLExact width σ _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) arguments = none := by
    simpa only [evalListHOLFinite_eq_toExact] using hargs
  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
    evalPanSemRecursiveCallFiniteContext.eq_6, hargsExact]

/-- Flapjack-specific DecCall lookup-failure helper for the HOL clause at
    `panSemScript.sml:694-714`. The `hargs` and `hlookup` branch selectors are
    additional hypotheses absent from HOL's unconditional `evaluate_def`
    conjunct, so this helper is not tagged as a port of that declaration. -/
theorem evaluateHOLFiniteState_decCall_lookup_none {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (values : List (ValueHOL width))
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values = none) :
    evaluateHOLFiniteState state
        (.decCall resultName shape function arguments continuation : ProgHOL width) =
      (some .error, state) := by
  classical
  have hargsExact :
      @evalListHOLExact width σ _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) arguments =
        some values := by
    simpa only [evalListHOLFinite_eq_toExact] using hargs
  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
    evalPanSemRecursiveCallFiniteContext.eq_6, hargsExact, hlookup]

/-- Flapjack-specific total-pair rendering of the DecCall clock-exhaustion
    branch from `panSemScript.sml:694-714`. With successful arguments and code
    lookup, zero caller clock returns `TimeOut` and clears caller locals. This
    stays untagged while the word-carrier qualifier for PanSemStateFiniteExact
    is pending review. -/
theorem evaluateHOLFiniteState_decCall_clock_zero {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (values : List (ValueHOL width)) (body : ProgHOL width)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : state.clock = 0) :
    evaluateHOLFiniteState state
        (.decCall resultName shape function arguments continuation : ProgHOL width) =
      (some .timeOut, emptyLocalsHOLFinite state) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have htimeout := evalPanSemRecursiveCallFiniteContext_decCall_timeout_branch
    resultName shape function arguments continuation context values body callee
    returnShape hargs hlookup hclock
  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders, context, htimeout]

/-- Flapjack-specific DecCall body-`NONE` helper for the HOL clause at
    `panSemScript.sml:694-714`. Its argument, lookup, and clock branch
    selectors are extra hypotheses absent from HOL's unconditional conjunct,
    so it is not tagged as a port. The body premise is a recursive-call
    induction hypothesis. The original Pancake probe
    `pan_sem_deccall_error_probe.out` observes `SOME Error` in this branch. -/
theorem evaluateHOLFiniteState_decCall_body_none {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (values : List (ValueHOL width)) (body : ProgHOL width)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
    (bodyPost : PanSemStateFiniteExact width σ)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : state.clock ≠ 0)
    (hbody : evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body =
        ((none : Option (PanSemResultExact width)), bodyPost)) :
    evaluateHOLFiniteState state
        (.decCall resultName shape function arguments continuation : ProgHOL width) =
      (some .error,
        (fixClockHOLFinite (callEntryStateHOLFinite state callee)
          ((none : Option (PanSemResultExact width)), bodyPost)).2) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have hargsContext : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values := by
    simpa [context] using hargs
  obtain ⟨bodyContext, hbodyContext, hbodyState⟩ :=
    evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body
      (callEntryContextHOLFinite context callee) rfl (none, bodyPost) hbody
  have hcase := evalPanSemRecursiveCallFiniteContext_decCall_body_none
    resultName shape function arguments continuation context values body callee
    returnShape bodyContext hargsContext hlookup hclock hbodyContext
  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders, context,
    hcase, callFixedContextHOLFinite, hbodyState]

/-- Flapjack-specific DecCall body-`Break` helper for the HOL clause at
    `panSemScript.sml:694-714`. Its argument, lookup, and clock branch
    selectors are extra hypotheses absent from HOL's unconditional conjunct,
    so this helper is not tagged as a port. The recursive body result is an
    induction hypothesis. -/
theorem evaluateHOLFiniteState_decCall_body_break {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (values : List (ValueHOL width)) (body : ProgHOL width)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
    (bodyPost : PanSemStateFiniteExact width σ)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : state.clock ≠ 0)
    (hbody : evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body =
        ((some .break : Option (PanSemResultExact width)), bodyPost)) :
    evaluateHOLFiniteState state
        (.decCall resultName shape function arguments continuation : ProgHOL width) =
      (some .error,
        (fixClockHOLFinite (callEntryStateHOLFinite state callee)
          ((some .break : Option (PanSemResultExact width)), bodyPost)).2) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have hargsContext : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values := by
    simpa [context] using hargs
  obtain ⟨bodyContext, hbodyContext, hbodyState⟩ :=
    evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body
      (callEntryContextHOLFinite context callee) rfl (some .break, bodyPost) hbody
  have hcase := evalPanSemRecursiveCallFiniteContext_decCall_body_break
    resultName shape function arguments continuation context values body callee
    returnShape bodyContext hargsContext hlookup hclock hbodyContext
  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders, context,
    hcase, callFixedContextHOLFinite, hbodyState]

/-- Flapjack-specific DecCall body-`Continue` helper for the HOL clause at
    `panSemScript.sml:694-714`. Its argument, lookup, and clock branch
    selectors are extra hypotheses absent from HOL's unconditional conjunct,
    so this helper is not tagged as a port. The recursive body result is an
    induction hypothesis. -/
theorem evaluateHOLFiniteState_decCall_body_continue {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (values : List (ValueHOL width)) (body : ProgHOL width)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
    (bodyPost : PanSemStateFiniteExact width σ)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values)
    (hlookup : lookupCodeHOLFinite state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : state.clock ≠ 0)
    (hbody : evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body =
        ((some .continue : Option (PanSemResultExact width)), bodyPost)) :
    evaluateHOLFiniteState state
        (.decCall resultName shape function arguments continuation : ProgHOL width) =
      (some .error,
        (fixClockHOLFinite (callEntryStateHOLFinite state callee)
          ((some .continue : Option (PanSemResultExact width)), bodyPost)).2) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  have hargsContext : evalListHOLFinite context.state
      (h := context.memaddrsDecidable) arguments = some values := by
    simpa [context] using hargs
  obtain ⟨bodyContext, hbodyContext, hbodyState⟩ :=
    evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
      (callEntryStateHOLFinite state callee) body
      (callEntryContextHOLFinite context callee) rfl (some .continue, bodyPost) hbody
  have hcase := evalPanSemRecursiveCallFiniteContext_decCall_body_continue
    resultName shape function arguments continuation context values body callee
    returnShape bodyContext hargsContext hlookup hclock hbodyContext
  simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders, context,
    hcase, callFixedContextHOLFinite, hbodyState]

/-- HOL `evaluate_def`'s original DecCall conjunct (`panSemScript.sml:694-714`,
    in the Definition beginning at line 556). It exposes argument/code lookup
    failure, timeout, all fixed callee result cases, both return-shape checks,
    continuation evaluation, caller-binding restoration, and the
    empty-locals fallback. Only constructor inputs are hypotheses;
    branch-selected helper theorems above remain untagged.

    Source review: `callEntryStateHOLFinite` decrements the caller clock and
    installs `newlocals`; `fixClockHOLFinite` preserves the recursive result
    and applies HOL `fix_clock` to the post-state. The return case checks
    `shape_of retv = shape` and `shape_of retv = return_sh`, sets `rt` in the
    fixed state with caller locals, evaluates `prog1`, then restores the old
    `rt` binding with `res_var`. Every other result uses the exact fixed state
    and the HOL empty-locals behavior where required. The statement has no
    branch selectors, result assumptions, or assembly-marker `none` case.
    `PanSemStateFiniteExact` has HOL's 13 state fields; the four map fields use
    the same-module `HolFiniteMapExact` roundtrip witness, and its width-indexed
    `BitVec` carrier is the reviewed positive HOL word translation. Because
    this RHS retains `fixClockHOLFinite`, it cites the original line-556
    Definition, not the line-780 theorem rewritten by `fix_clock_evaluate`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 556
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_decCall_total {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width) :
    evaluateHOLFiniteState state
        (.decCall resultName shape function arguments continuation : ProgHOL width) =
      (match evalListHOLFinite state
          (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
       | none => (some .error, state)
       | some values =>
           match lookupCodeHOLFinite state.code.lookup function values with
           | none => (some .error, state)
           | some (body, callee, returnShape) =>
               if state.clock = 0 then
                 (some .timeOut, emptyLocalsHOLFinite state)
               else
                 let entry := callEntryStateHOLFinite state callee
                 let bodyOutput := evaluateHOLFiniteState entry body
                 let fixed := fixClockHOLFinite entry bodyOutput
                 match bodyOutput.1 with
                 | none => (some .error, fixed.2)
                 | some .break => (some .error, fixed.2)
                 | some .continue => (some .error, fixed.2)
                 | some (.returned value) =>
                     if shapeEqHOL (shapeOfHOLExact value) shape &&
                         shapeEqHOL (shapeOfHOLExact value) returnShape then
                       let continuationState :=
                         setVarHOLFinite resultName value
                           { fixed.2 with locals := state.locals }
                       let continuationOutput :=
                         evaluateHOLFiniteState continuationState continuation
                       (continuationOutput.1,
                         { continuationOutput.2 with
                           locals := HolFiniteMapExact.resVarEq
                             continuationOutput.2.locals
                             (resultName, state.locals.lookup resultName) })
                     else (some .error, fixed.2)
                 | some other => (some other, emptyLocalsHOLFinite fixed.2)) := by
  classical
  let hmem : DecidablePred state.memaddrs :=
    fun address => Classical.propDecidable (state.memaddrs address)
  let hshared : DecidablePred state.shMemaddrs :=
    fun address => Classical.propDecidable (state.shMemaddrs address)
  let context : FiniteEvalContext width σ := ⟨state, hmem, hshared⟩
  change (match evalPanSemRecursiveCallFiniteContext
      (.decCall resultName shape function arguments continuation) context with
    | some pair => (pair.1, pair.2.state)
    | none => (none, state)) = _
  rw [evalPanSemRecursiveCallFiniteContext.eq_6]
  cases hargs : evalListHOLFinite state arguments with
  | none => simp [context]
  | some values =>
      have hargsContext : evalListHOLFinite context.state
          (h := context.memaddrsDecidable) arguments = some values := by
        simpa [context] using hargs
      cases hlookup : lookupCodeHOLFinite state.code.lookup function values with
      | none => simp [context, hlookup]
      | some entryData =>
          have hlookupContext : lookupCodeHOLFinite context.state.code.lookup
              function values = some entryData := by
            simpa [context] using hlookup
          obtain ⟨body, callee, returnShape⟩ := entryData
          by_cases hclock : state.clock = 0
          · simp [context, hlookup, hclock]
          · let entry := callEntryStateHOLFinite state callee
            have hclockContext : context.state.clock ≠ 0 := by
              simpa [context] using hclock
            let entryContext := callEntryContextHOLFinite context callee
            obtain ⟨bodyPair, hbody⟩ :=
              evalPanSemRecursiveCallFiniteContext_total body entryContext
            have hbodyGenerated :=
              evalPanSemRecursiveCallFiniteContext_callEntryContext_normalize
                body context callee rfl rfl
            have hbodyGenerated' : evalPanSemRecursiveCallFiniteContext body
                (context.withState entry rfl rfl) = some bodyPair := by
              rw [hbodyGenerated]
              exact hbody
            let entryClassical : FiniteEvalContext width σ :=
              ⟨entry,
                fun address => Classical.propDecidable (entry.memaddrs address),
                fun address => Classical.propDecidable (entry.shMemaddrs address)⟩
            have hbodyClassical :
                evalPanSemRecursiveCallFiniteContext body entryClassical =
                  some bodyPair := by
              rw [evalPanSemRecursiveCallFiniteContext_state_eq
                body entryClassical entryContext rfl]
              exact hbody
            have hbodyState : evaluateHOLFiniteState entry body =
                (bodyPair.1, bodyPair.2.state) := by
              simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                entryClassical, hbodyClassical]
            simp only [hlookupContext, if_neg hclockContext,
              hbodyGenerated, entryContext, hbody, hlookup, if_neg hclock]
            cases hresult : bodyPair.1 with
            | none => simp [hbodyState, hresult, context, entry,
                fixClockHOLFinite, callFixedContextHOLFinite]
            | some bodyResult =>
                cases bodyResult with
                | error => simp [hbodyState, hresult, context, entry,
                    fixClockHOLFinite, callFixedContextHOLFinite, emptyLocalsHOLFinite]
                | timeOut => simp [hbodyState, hresult, context, entry,
                    fixClockHOLFinite, callFixedContextHOLFinite, emptyLocalsHOLFinite]
                | «break» => simp [hbodyState, hresult, context, entry,
                    fixClockHOLFinite, callFixedContextHOLFinite]
                | «continue» => simp [hbodyState, hresult, context, entry,
                    fixClockHOLFinite, callFixedContextHOLFinite]
                | finalFfi event => simp [hbodyState, hresult, context, entry,
                    fixClockHOLFinite, callFixedContextHOLFinite, emptyLocalsHOLFinite]
                | exception exceptionId value => simp [hbodyState, hresult,
                    context, entry, fixClockHOLFinite, callFixedContextHOLFinite,
                    emptyLocalsHOLFinite]
                | returned value =>
                    by_cases hshape :
                        (shapeEqHOL (shapeOfHOLExact value) shape &&
                          shapeEqHOL (shapeOfHOLExact value) returnShape) = true
                    · let fixedContext := callFixedContextHOLFinite entry
                        (some (PanSemResultExact.returned value)) bodyPair.2
                      let continuationContext := callContinuationContextHOLFinite
                        context fixedContext resultName value
                      let continuationState := setVarHOLFinite resultName value
                        {(fixClockHOLFinite entry
                          (some (PanSemResultExact.returned value), bodyPair.2.state)).2 with
                          locals := state.locals}
                      simp only [hshape]
                      obtain ⟨continuationPair, hcontinuation⟩ :=
                        evalPanSemRecursiveCallFiniteContext_total continuation
                          continuationContext
                      have hcontinuationGenerated :
                          evalPanSemRecursiveCallFiniteContext continuation
                            (callContinuationContextHOLFinite context
                              (callFixedContextHOLFinite
                                (callEntryStateHOLFinite context.state callee)
                                (some (PanSemResultExact.returned value)) bodyPair.2)
                              resultName value) = some continuationPair := by
                        simpa [entry, fixedContext, continuationContext] using hcontinuation
                      let continuationClassical : FiniteEvalContext width σ :=
                        ⟨continuationState,
                          fun address => Classical.propDecidable
                            (continuationState.memaddrs address),
                          fun address => Classical.propDecidable
                            (continuationState.shMemaddrs address)⟩
                      have hcontinuationClassical :
                          evalPanSemRecursiveCallFiniteContext continuation
                              continuationClassical = some continuationPair := by
                        rw [evalPanSemRecursiveCallFiniteContext_state_eq
                          continuation continuationClassical continuationContext rfl]
                        exact hcontinuation
                      have hcontinuationState : evaluateHOLFiniteState
                          continuationState continuation =
                            (continuationPair.1, continuationPair.2.state) := by
                        simp [evaluateHOLFiniteState,
                          evaluateHOLFiniteStateWithDeciders,
                          continuationClassical, hcontinuationClassical]
                      have hreturnedResult : continuationPair.1 =
                          (evaluateHOLFiniteState continuationState continuation).1 :=
                        (congrArg Prod.fst hcontinuationState).symm
                      have hreturnedPost : continuationPair.2.state =
                          (evaluateHOLFiniteState continuationState continuation).2 :=
                        (congrArg Prod.snd hcontinuationState).symm
                      have hcontinuationStateEq : continuationState =
                          setVarHOLFinite resultName value
                            {(fixClockHOLFinite entry
                              (some (PanSemResultExact.returned value), bodyPair.2.state)).2 with
                              locals := state.locals} := by rfl
                      simp [hbodyState, hresult, hshape, hcontinuationGenerated,
                        hreturnedResult, hreturnedPost, hcontinuationStateEq,
                        context, entry,
                        fixClockHOLFinite, HolFiniteMapExact.resVarEq]
                    · simp [hbodyState, hresult, hshape, context, entry,
                        fixClockHOLFinite, callFixedContextHOLFinite]

/-- Source-reviewed HOL `evaluate_def` Seq conjunct (`panSemScript.sml:615`)
    from the source `Definition evaluate_def` at line 556. That definition
    explicitly applies `fix_clock` to the first evaluation pair; the theorem
    restatement at line 780 rewrites that call away using `fix_clock_evaluate`,
    so this case is tagged to line 556. The full 21-clause assembly is
    `evaluateHOLFiniteState_eq_evaluate_def` (`PanSem/EvaluateClock.lean`).
    It fixes the first pair's clock,
    evaluates the second program only when the first result is `NONE`, and
    otherwise returns the fixed pair. Both recursive calls use the total
    pair-shaped evaluator; the internal assembly marker is absent from the
    statement. `PanSemStateFiniteExact` owns the four named `HolFiniteMapExact`
    fields, with the canonical same-module roundtrip witness. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 556
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_seq {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (first second : ProgHOL width) :
    evaluateHOLFiniteState state (.seq first second : ProgHOL width) =
      (let firstOutput := evaluateHOLFiniteState state first
       let fixed := fixClockHOLFinite state firstOutput
       match fixed.1 with
       | none => evaluateHOLFiniteState fixed.2 second
       | some _ => fixed) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  obtain ⟨firstPair, hfirst⟩ := evalPanSemRecursiveCallFiniteContext_total first context
  have hfirstOutput : evaluateHOLFiniteState state first =
      (firstPair.1, firstPair.2.state) := by
    simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders, context, hfirst]
  let fixed := fixClockHOLFinite state (firstPair.1, firstPair.2.state)
  cases hresult : firstPair.1 with
  | none =>
      have hseq' : evalPanSemRecursiveCallFiniteContext (.seq first second) context =
          evalPanSemRecursiveCallFiniteContext second
            (firstPair.2.withState fixed.2 rfl rfl) := by
        rw [evalPanSemRecursiveCallFiniteContext.eq_def]
        simp only [hfirst, hresult]
        rfl
      have hctx : firstPair.2.withState fixed.2 rfl rfl =
          (⟨fixed.2, fun address => Classical.propDecidable (fixed.2.memaddrs address),
            fun address => Classical.propDecidable (fixed.2.shMemaddrs address)⟩ :
            FiniteEvalContext width σ) := by
        apply FiniteEvalContext.ext
        rfl
      let secondContext := firstPair.2.withState fixed.2 rfl rfl
      obtain ⟨secondPair, hsecond⟩ :=
        evalPanSemRecursiveCallFiniteContext_total second secondContext
      have hsecondGlobal : evalPanSemRecursiveCallFiniteContext second
          (⟨fixed.2, fun address => Classical.propDecidable (fixed.2.memaddrs address),
            fun address => Classical.propDecidable (fixed.2.shMemaddrs address)⟩ :
            FiniteEvalContext width σ) = some secondPair := by
        rw [← hctx]
        exact hsecond
      change (match evalPanSemRecursiveCallFiniteContext (.seq first second) context with
        | some pair => (pair.1, pair.2.state)
        | none => (none, state)) = _
      rw [hseq']
      rw [hfirstOutput]
      rw [hctx]
      rw [hresult]
      simp only [hsecondGlobal]
      have hsecondOutput : evaluateHOLFiniteState fixed.2 second =
          (secondPair.1, secondPair.2.state) := by
        simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders, hsecondGlobal]
      have hsecondOutput' : evaluateHOLFiniteState
          (fixClockHOLFinite state
            ((none : Option (PanSemResultExact width)), firstPair.2.state)).2 second =
            (secondPair.1, secondPair.2.state) := by
        simpa [fixed, hresult, fixClockHOLFinite] using hsecondOutput
      change (secondPair.1, secondPair.2.state) =
        evaluateHOLFiniteState
          (fixClockHOLFinite state
            ((none : Option (PanSemResultExact width)), firstPair.2.state)).2 second
      rw [hsecondOutput']
  | some result =>
      have hseq' : evalPanSemRecursiveCallFiniteContext (.seq first second) context =
          some (some result, firstPair.2.withState fixed.2 rfl rfl) := by
        rw [evalPanSemRecursiveCallFiniteContext.eq_def]
        simp only [hfirst, hresult]
        rfl
      change (match evalPanSemRecursiveCallFiniteContext (.seq first second) context with
        | some pair => (pair.1, pair.2.state)
        | none => (none, state)) = _
      rw [hseq']
      rw [hfirstOutput]
      rw [hresult]
      simp [fixed, fixClockHOLFinite, FiniteEvalContext.withState]

/-- The decider-taking helper is the pair-shaped rendering of the assembly-marker
    evaluator. This bridge is Flapjack-specific infrastructure. -/
theorem evaluateHOLFiniteStateWithDeciders_eq_getD {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width) :
    evaluateHOLFiniteStateWithDeciders state program =
      (evaluateHOLFinite state program).getD (none, state) := by
  unfold evaluateHOLFiniteStateWithDeciders evaluateHOLFinite
  cases evalPanSemRecursiveCallFiniteContext program ⟨state, h, hshared⟩ <;> rfl

/-- FLAPJACK-SPECIFIC compatibility name for the pair-shaped finite evaluator. -/
abbrev evaluateHOLFiniteResult := @evaluateHOLFiniteStateWithDeciders

/-- The result-shaped view is exactly the successful output of the finite
    evaluator, since its assembly marker cannot fail. -/
theorem evaluateHOLFiniteResult_eq_iff {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width)
    (pair : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) :
    evaluateHOLFinite state program = some pair ↔
      evaluateHOLFiniteResult state program = pair := by
  have hresult : evaluateHOLFiniteResult state program =
      (evaluateHOLFinite state program).getD (none, state) := by
    exact evaluateHOLFiniteStateWithDeciders_eq_getD state program
  rw [hresult]
  constructor
  · intro heval
    simp [heval]
  · intro heval
    cases h : evaluateHOLFinite state program with
    | none => exact (evaluateHOLFinite_ne_none state program h).elim
    | some actual =>
        have hpair : actual = pair := by simpa [h] using heval
        exact congrArg some hpair

/-- Source-reviewed HOL `evaluate_def` While conjunct (`panSemScript.sml:630`)
    from the source `Definition evaluate_def` at line 556. The Definition
    explicitly fixes the body result's clock before branching; line 780 is the
    separate rewrite-restated theorem. This is a staged case equation; the
    full 21-clause assembly is `evaluateHOLFiniteState_eq_evaluate_def`
    (`PanSem/EvaluateClock.lean`). -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 556
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_while_total {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (condition : ExpHOL width)
    (body : ProgHOL width) :
    evaluateHOLFiniteState state (.while condition body : ProgHOL width) =
    (match @evalHOLFinite width σ _ state
          (fun address => Classical.propDecidable (state.memaddrs address)) condition with
       | some (.val (.word word)) =>
           if word ≠ 0 then
             if state.clock = 0 then (some .timeOut, emptyLocalsHOLFinite state)
             else
               let entry := decClockHOLFinite state
               let bodyOutput := evaluateHOLFiniteState entry body
               let fixed := fixClockHOLFinite entry bodyOutput
               match bodyOutput.1 with
               | none => evaluateHOLFiniteState fixed.2 (.while condition body)
               | some .continue => evaluateHOLFiniteState fixed.2 (.while condition body)
               | some .break => (none, fixed.2)
               | some result => (some result, fixed.2)
           else (none, state)
       | _ => (some .error, state)) := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  change (match evalPanSemRecursiveCallFiniteContext
      (.while condition body : ProgHOL width) context with
    | some pair => (pair.1, pair.2.state)
    | none => (none, state)) = _
  rw [evalPanSemRecursiveCallFiniteContext.eq_4]
  rw [evalHOLFinite_eq_toExact context.state (h := context.memaddrsDecidable) condition]
  generalize hcond : @evalHOLExact width σ _ context.state.toExact
      context.memaddrsDecidable condition = conditionResult
  cases conditionResult with
  | none => rfl
  | some value =>
      cases value with
      | rStruct fields => rfl
      | nStruct name fields => rfl
      | val wordLab =>
          cases wordLab with
          | word word =>
              simp only []
              by_cases hword : word ≠ 0
              · rw [if_pos hword, if_pos hword]
                by_cases hclock : context.state.clock = 0
                · have hclock' : state.clock = 0 := hclock
                  rw [if_pos hclock, if_pos hclock']
                  simp [context]
                  rfl
                · have hclock' : ¬ state.clock = 0 := hclock
                  rw [if_neg hclock, if_neg hclock']
                  let entry := decClockHOLFinite context.state
                  let entryContext := context.withState entry rfl rfl
                  obtain ⟨bodyPair, hbody⟩ :=
                    evalPanSemRecursiveCallFiniteContext_total body entryContext
                  have hbodyOutput : evaluateHOLFiniteState
                      (decClockHOLFinite state) body =
                      (bodyPair.1, bodyPair.2.state) := by
                    have hcanonical : entryContext =
                        (⟨decClockHOLFinite state,
                          fun address => Classical.propDecidable
                            ((decClockHOLFinite state).memaddrs address),
                          fun address => Classical.propDecidable
                            ((decClockHOLFinite state).shMemaddrs address)⟩ :
                          FiniteEvalContext width σ) := by
                      apply FiniteEvalContext.ext
                      rfl
                    have hbodyCanonical : evalPanSemRecursiveCallFiniteContext body
                        (⟨decClockHOLFinite state,
                          fun address => Classical.propDecidable
                            ((decClockHOLFinite state).memaddrs address),
                          fun address => Classical.propDecidable
                            ((decClockHOLFinite state).shMemaddrs address)⟩ :
                          FiniteEvalContext width σ) = some bodyPair := by
                      rw [← hcanonical]
                      exact hbody
                    simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                      hbodyCanonical]
                  let fixed := fixClockHOLFinite (decClockHOLFinite state)
                    (bodyPair.1, bodyPair.2.state)
                  have hfixedMem : fixed.2.memaddrs = bodyPair.2.state.memaddrs := by
                    simp [fixed, fixClockHOLFinite]
                  have hfixedShared : fixed.2.shMemaddrs =
                      bodyPair.2.state.shMemaddrs := by
                    simp [fixed, fixClockHOLFinite]
                  let fixedContext := bodyPair.2.withState fixed.2
                    hfixedMem hfixedShared
                  have hgeneratedContext : bodyPair.2.withState fixed.2 rfl rfl =
                      fixedContext := by
                    apply FiniteEvalContext.withState_congr
                  obtain ⟨loopPair, hloop⟩ :=
                    evalPanSemRecursiveCallFiniteContext_total
                      (.while condition body) fixedContext
                  have hwhileOutput : evaluateHOLFiniteState fixed.2
                      (.while condition body) = (loopPair.1, loopPair.2.state) := by
                    have hcanonical : fixedContext =
                        (⟨fixed.2,
                          fun address => Classical.propDecidable (fixed.2.memaddrs address),
                          fun address => Classical.propDecidable (fixed.2.shMemaddrs address)⟩ :
                          FiniteEvalContext width σ) := by
                      apply FiniteEvalContext.ext
                      rfl
                    have hloopCanonical :
                        evalPanSemRecursiveCallFiniteContext (.while condition body)
                          (⟨fixed.2,
                            fun address => Classical.propDecidable (fixed.2.memaddrs address),
                            fun address => Classical.propDecidable (fixed.2.shMemaddrs address)⟩ :
                            FiniteEvalContext width σ) = some loopPair := by
                      rw [← hcanonical]
                      exact hloop
                    simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
                      hloopCanonical]
                  simp only [entry, entryContext, hbody]
                  rw [hgeneratedContext]
                  simp only [hloop]
                  rw [hbodyOutput, hwhileOutput]
                  cases hbodyResult : bodyPair.1 with
                  | none =>
                      simp
                  | some result =>
                      cases result <;>
                        simp [fixedContext, fixed, fixClockHOLFinite,
                          FiniteEvalContext.withState_state]
              · rw [if_neg hword, if_neg hword]

/-! ### Global-shape invariant core (flapjack-4ac.4.62.1)

HOL `panPropsScript.sml:1183 evaluate_global_shape_invariant` states that a
successful `evaluate` preserves the shape of every stored global value.  The
exact finite evaluator writes globals only through `setGlobalHOLFinite`
(`is_valid_value`-gated shape-preserving writes on the executed path), so the
invariant is the preservation of the shape map `globalsShapes`.  These untagged
lemmas are the shared core; the whole-program induction over the recursive
evaluator is the remaining step of `flapjack-4ac.4.62`. -/

/-- Shape map of the `globals` table: the shape of each stored value, or `none`
    for an unbound name. -/
def globalsShapes {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) : MlS → Option ShapeHOL :=
  fun name => (state.globals.lookup name).map shapeOfHOLExact

theorem globalsShapes_setVarHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateFiniteExact width σ) :
    globalsShapes (setVarHOLFinite name value state) = globalsShapes state := rfl

theorem globalsShapes_emptyLocalsHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    globalsShapes (emptyLocalsHOLFinite state) = globalsShapes state := rfl

theorem globalsShapes_setLocals {width : Nat} {σ : Type} [NeZero width]
    (map : HolFiniteMapExact MlS (ValueHOL width)) (state : PanSemStateFiniteExact width σ) :
    globalsShapes { state with locals := map } = globalsShapes state := rfl

theorem globalsShapes_decClockHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    globalsShapes (decClockHOLFinite state) = globalsShapes state := rfl

theorem globalsShapes_setGlobalHOLFinite_value {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateFiniteExact width σ) :
    globalsShapes (setGlobalHOLFinite name value state) =
      FUPDATE (globalsShapes state) (name, shapeOfHOLExact value) := by
  funext key
  by_cases h : name == key
  · simp only [globalsShapes, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h, if_true, Option.map_some]
  · simp only [globalsShapes, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h,
      Bool.false_eq_true, if_false]

/-- A `set_global` write whose value has the shape already stored at `name`
    (the `is_valid_value Global` condition) preserves the global shape map. -/
theorem globalsShapes_setGlobalHOLFinite_of_shape {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateFiniteExact width σ)
    (h : (state.globals.lookup name).map shapeOfHOLExact = some (shapeOfHOLExact value)) :
    globalsShapes (setGlobalHOLFinite name value state) = globalsShapes state := by
  rw [globalsShapes_setGlobalHOLFinite_value]
  funext key
  by_cases hk : name == key
  · have hnk : name = key := by simpa only [beq_iff_eq] using hk
    subst hnk
    simp only [FUPDATE, hk, if_true]
    simpa only [globalsShapes] using h.symm
  · simp only [FUPDATE, hk, Bool.false_eq_true, if_false]

theorem globalsShapes_setKvarHOLFinite_of_shape {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (value : ValueHOL width) (state : PanSemStateFiniteExact width σ)
    (h : (state.globals.lookup name).map shapeOfHOLExact = some (shapeOfHOLExact value)) :
    globalsShapes (setKvarHOLFinite kind name value state) = globalsShapes state := by
  cases kind
  · exact globalsShapes_setVarHOLFinite name value state
  · exact globalsShapes_setGlobalHOLFinite_of_shape name value state h

/-- Equality of shape maps yields HOL's existential shape-preservation
    conclusion for every initially bound global. -/
theorem globalsShapes_exists_shape {width : Nat} {σ : Type} [NeZero width]
    {source final : PanSemStateFiniteExact width σ}
    (h : globalsShapes final = globalsShapes source) {name : MlS} {value : ValueHOL width}
    (hv : source.globals.lookup name = some value) :
    ∃ value', final.globals.lookup name = some value' ∧
      shapeOfHOLExact value' = shapeOfHOLExact value := by
  have h' := congrFun h name
  simp only [globalsShapes] at h'
  rw [hv, Option.map_some] at h'
  cases hlook : final.globals.lookup name with
  | none => simp only [hlook] at h'; exact absurd h' (by simp)
  | some value' =>
      refine ⟨value', rfl, ?_⟩
      have h'' : some (shapeOfHOLExact value') = some (shapeOfHOLExact value) := by
        simpa only [hlook, Option.map_some] using h'
      exact Option.some.inj h''

/-- Broad/finite transport: the finite-carrier `globalsShapes` is the broad shape
projection along `toExact`. -/
theorem globalsShapes_eq_globalsShapesExact_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    globalsShapes state = globalsShapesExact state.toExact := rfl

/-- Broad/finite transport: `globalsShapes` on the broad state underlying the finite carrier
is `globalsShapesExact`. -/
theorem globalsShapes_ofExact_eq_globalsShapesExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (h : state.FiniteSupport) :
    globalsShapes (ofExact state h) = globalsShapesExact state := rfl

/-- Finite-carrier form of the shMemLoad globals-shape preservation: a
successful load installs the loaded word into a variable of the requested kind
and leaves `ffi`/`clock`/memory untouched, so under the same guard as the broad
step function the global shape map is unchanged. -/
theorem globalsShapes_shMemLoadHOLFiniteExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [DecidablePred state.shMemaddrs]
    (kind : VarKind) (name : MlS) (address : RiscV.Word width) (nb : Nat)
    (word : RiscV.Word width)
    (hlocal : lookupKvarHOLFinite kind name state = some (.val (.word word))) :
    globalsShapes (shMemLoadHOLFiniteExact state kind name address nb).2 =
      globalsShapes state := by
  have hb : ∀ (k : VarKind),
      lookupKvarHOLFinite k name state = lookupKvarHOLExact k name state.toExact := by
    intro k
    unfold lookupKvarHOLFinite lookupKvarHOLExact
    cases k <;> rfl
  have hguard : lookupKvarHOLExact kind name state.toExact = some (.val (.word word)) := by
    rw [← hb kind]; exact hlocal
  let loaded := shMemLoadHOLFiniteExact state kind name address nb
  have hto : loaded.2.toExact =
      (shMemLoadHOLExact state.toExact kind name address nb).2 :=
    congrArg Prod.snd
      (shMemLoadHOLFiniteExact_toExact state kind name address nb)
  calc globalsShapes loaded.2
      = globalsShapesExact loaded.2.toExact :=
        globalsShapes_eq_globalsShapesExact_toExact loaded.2
    _ = globalsShapesExact (shMemLoadHOLExact state.toExact kind name address nb).2 := by
        rw [hto]
    _ = globalsShapesExact state.toExact :=
        shMemLoadHOLExact_globalsShapesExact state.toExact kind name address nb word hguard
    _ = globalsShapes state :=
        (globalsShapes_eq_globalsShapesExact_toExact state).symm

/-- Finite-support rendering preserves `globalsShapes` in every nonrecursive
clause (Flapjack-specific untagged infrastructure for HOL
`panPropsScript.sml:1183` `evaluate_global_shape_invariant`). -/
theorem evalPanSemNonrecursiveHOLFinite_globalsShapes {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [DecidablePred state.memaddrs]
    [DecidablePred state.shMemaddrs] (program : ProgHOL width)
    (result : Option (PanSemResultExact width))
    (output : PanSemStateFiniteExact width σ)
    (heval : evalPanSemNonrecursiveHOLFinite state program = some (result, output)) :
    globalsShapes output = globalsShapes state := by
  unfold evalPanSemNonrecursiveHOLFinite at heval
  split at heval
  · simp at heval
  · rename_i pair hres
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    change globalsShapesExact pair.2 = globalsShapes state
    rw [globalsShapes_eq_globalsShapesExact_toExact]
    exact evalPanSemNonrecursiveHOLExact_globalsShapesExact program state.toExact pair.1 pair.2 hres

/-- Finite-carrier rendering of the executed ShMemStore route. There is no
dedicated `shMemStoreHOLFiniteExact` step helper: the executable store clause is
the finite wrapper `shMemStoreClauseHOLFiniteExact`, which is the broad
`shMemStoreClauseHOLExact` applied at `state.toExact`. This theorem records the
finite-carrier `globalsShapes` preservation for that actual route, with the
finite `ofExact` corollary below. Untagged Flapjack infrastructure for HOL
`panPropsScript.sml:1183` `evaluate_global_shape_invariant`. -/
theorem globalsShapes_shMemStoreClauseHOLFiniteExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (operator : OpSize) (address value : ExpHOL width) :
    globalsShapesExact (shMemStoreClauseHOLFiniteExact state operator address value).2 =
      globalsShapesExact state.toExact := by
  unfold shMemStoreClauseHOLFiniteExact
  letI : DecidablePred state.toExact.shMemaddrs :=
    fun address => Classical.propDecidable (state.shMemaddrs address)
  exact shMemStoreClauseHOLExact_globalsShapesExact state.toExact
    operator address value
    (fun (_ : PanSemStateExact width σ) (expression : ExpHOL width) =>
      @evalHOLExact width σ _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) expression)

/-- Finite-state corollary of `globalsShapes_shMemStoreClauseHOLFiniteExact`:
packing the broad store-route result back through `ofExact` preserves
`globalsShapes` on the finite carrier. Untagged Flapjack infrastructure. -/
theorem globalsShapes_ofExact_shMemStoreClauseHOLFiniteExact {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    (operator : OpSize) (address value : ExpHOL width)
    (h : (shMemStoreClauseHOLFiniteExact state operator address value).2.FiniteSupport) :
    globalsShapes
        (ofExact (shMemStoreClauseHOLFiniteExact state operator address value).2 h) =
      globalsShapes state := by
  rw [globalsShapes_ofExact_eq_globalsShapesExact,
    globalsShapes_eq_globalsShapesExact_toExact]
  exact globalsShapes_shMemStoreClauseHOLFiniteExact state operator address value

/-! ### Recursive-arm global-shape helpers (flapjack-4ac.4.62.2.3)

Context and step lemmas used by the recursive exact evaluator arms of
`evalPanSemRecursiveCallFiniteContext`.  Each is untagged Flapjack
infrastructure for HOL `panPropsScript.sml:1183
evaluate_global_shape_invariant`; the assembly is `flapjack-4ac.4.62.2.4`. -/

theorem isValidValueHOLExact_global_shape_finite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (name : MlS) (value : ValueHOL width)
    (h : isValidValueHOLExact state.toExact .global name value = true) :
    (state.globals.lookup name).map shapeOfHOLExact = some (shapeOfHOLExact value) := by
  have hb := isValidValueHOLExact_global_shape state.toExact name value h
  simpa only [PanSemStateFiniteExact.toExact] using hb

theorem globalsShapes_fixClockHOLFinite {width : Nat} {σ : Type} [NeZero width]
    {β : Type} (state : PanSemStateFiniteExact width σ)
    (step : β × PanSemStateFiniteExact width σ) :
    globalsShapes (fixClockHOLFinite state step).2 = globalsShapes step.2 := rfl

theorem globalsShapes_callEntryStateHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) :
    globalsShapes (callEntryStateHOLFinite state callee) = globalsShapes state := rfl

theorem globalsShapes_handlerStateHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (context fixedContext : FiniteEvalContext width σ) (name : MlS) (value : ValueHOL width) :
    globalsShapes (handlerStateHOLFinite context fixedContext name value) =
      globalsShapes fixedContext.state := rfl

theorem globalsShapes_callContinuationContextHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (context fixedContext : FiniteEvalContext width σ) (resultName : MlS) (value : ValueHOL width) :
    globalsShapes (callContinuationContextHOLFinite context fixedContext resultName value).state =
      globalsShapes fixedContext.state := rfl

/-- A validity-gated `set_kvar` write preserves the global shape map whenever the
    written-into state already has the source state's shape map.  This is the
    `Call`/`DecCall` return-value write condition. -/
theorem globalsShapes_setKvarHOLFinite_of_globalsShapes {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (kind : VarKind) (name : MlS)
    (value : ValueHOL width) (state : PanSemStateFiniteExact width σ)
    (hm : globalsShapes state = globalsShapes source)
    (hvalid : isValidValueHOLExact source.toExact kind name value = true) :
    globalsShapes (setKvarHOLFinite kind name value state) = globalsShapes state := by
  cases kind
  · exact globalsShapes_setVarHOLFinite name value state
  · apply globalsShapes_setKvarHOLFinite_of_shape
    have hsrc := isValidValueHOLExact_global_shape_finite source name value hvalid
    have hlook := congrFun hm name
    simp only [globalsShapes] at hlook
    rw [hsrc] at hlook
    exact hlook

theorem globalsShapes_dec_arm {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL width) (body : ProgHOL width)
    (context : FiniteEvalContext width σ) (value : ValueHOL width)
    (hinit : evalHOLFinite context.state (h := context.memaddrsDecidable) initializer =
      some value)
    (hshape : shapeEqHOL shape (shapeOfHOLExact value) = true)
    (hbodyInv : ∀ (result : Option (PanSemResultExact width)) (output : FiniteEvalContext width σ),
      evalPanSemRecursiveCallFiniteContext body
        (context.withState (setVarHOLFinite name value context.state) rfl rfl) =
          some (result, output) →
      globalsShapes output.state =
        globalsShapes (context.withState (setVarHOLFinite name value context.state) rfl rfl).state) :
    ∀ (result : Option (PanSemResultExact width)) (output : FiniteEvalContext width σ),
      evalPanSemRecursiveCallFiniteContext (.dec name shape initializer body) context =
        some (result, output) →
      globalsShapes output.state = globalsShapes context.state := by
  intro result output heval
  rw [evalPanSemRecursiveCallFiniteContext.eq_def] at heval
  dsimp only at heval
  rw [hinit] at heval
  dsimp only at heval
  rw [if_pos hshape] at heval
  cases hb : evalPanSemRecursiveCallFiniteContext body
      (context.withState (setVarHOLFinite name value context.state) rfl rfl) with
  | none => rw [hb] at heval; dsimp only at heval; simp at heval
  | some p =>
      obtain ⟨res, post⟩ := p
      rw [hb] at heval
      dsimp only at heval
      simp only [Option.some.injEq, Prod.mk.injEq] at heval
      rcases heval with ⟨rfl, rfl⟩
      show globalsShapes post.state = globalsShapes context.state
      rw [hbodyInv res post hb]
      show globalsShapes (setVarHOLFinite name value context.state) = globalsShapes context.state
      exact globalsShapes_setVarHOLFinite name value context.state

theorem globalsShapes_seq_none_arm {width : Nat} {σ : Type} [NeZero width]
    (first second : ProgHOL width) (context : FiniteEvalContext width σ)
    (hfirst : evalPanSemRecursiveCallFiniteContext first context = none) :
    ∀ (result : Option (PanSemResultExact width)) (output : FiniteEvalContext width σ),
      evalPanSemRecursiveCallFiniteContext (.seq first second) context = some (result, output) →
      globalsShapes output.state = globalsShapes context.state := by
  intro result output heval
  rw [evalPanSemRecursiveCallFiniteContext.eq_def] at heval
  dsimp only at heval
  rw [hfirst] at heval
  dsimp only at heval
  simp at heval

theorem globalsShapes_seq_some_none_arm {width : Nat} {σ : Type} [NeZero width]
    (first second : ProgHOL width) (context firstContext : FiniteEvalContext width σ)
    (hfirst : evalPanSemRecursiveCallFiniteContext first context = some (none, firstContext))
    (hfirstInv : globalsShapes firstContext.state = globalsShapes context.state)
    (hsecondInv : ∀ (result : Option (PanSemResultExact width)) (output : FiniteEvalContext width σ),
      evalPanSemRecursiveCallFiniteContext second
        (firstContext.withState
          (fixClockHOLFinite context.state
            ((none : Option (PanSemResultExact width)), firstContext.state)).2 rfl rfl) =
          some (result, output) →
      globalsShapes output.state =
        globalsShapes (firstContext.withState
          (fixClockHOLFinite context.state
            ((none : Option (PanSemResultExact width)), firstContext.state)).2 rfl rfl).state) :
    ∀ (result : Option (PanSemResultExact width)) (output : FiniteEvalContext width σ),
      evalPanSemRecursiveCallFiniteContext (.seq first second) context = some (result, output) →
      globalsShapes output.state = globalsShapes context.state := by
  intro result output heval
  rw [evalPanSemRecursiveCallFiniteContext.eq_def] at heval
  dsimp only at heval
  rw [hfirst] at heval
  dsimp only at heval
  rw [hsecondInv result output heval]
  show globalsShapes (fixClockHOLFinite context.state (none, firstContext.state)).2 =
    globalsShapes context.state
  rw [globalsShapes_fixClockHOLFinite]
  exact hfirstInv

theorem globalsShapes_seq_some_some_arm {width : Nat} {σ : Type} [NeZero width]
    (first second : ProgHOL width) (context firstContext : FiniteEvalContext width σ)
    (firstResult : PanSemResultExact width)
    (hfirst : evalPanSemRecursiveCallFiniteContext first context =
      some (some firstResult, firstContext))
    (hfirstInv : globalsShapes firstContext.state = globalsShapes context.state) :
    ∀ (result : Option (PanSemResultExact width)) (output : FiniteEvalContext width σ),
      evalPanSemRecursiveCallFiniteContext (.seq first second) context = some (result, output) →
      globalsShapes output.state = globalsShapes context.state := by
  intro result output heval
  rw [evalPanSemRecursiveCallFiniteContext.eq_def] at heval
  dsimp only at heval
  rw [hfirst] at heval
  dsimp only at heval
  simp only [Option.some.injEq, Prod.mk.injEq] at heval
  rcases heval with ⟨rfl, rfl⟩
  show globalsShapes (fixClockHOLFinite context.state (some firstResult, firstContext.state)).2 =
    globalsShapes context.state
  rw [globalsShapes_fixClockHOLFinite]
  exact hfirstInv

theorem globalsShapes_ite_then_arm {width : Nat} {σ : Type} [NeZero width]
    (condition : ExpHOL width) (thenBranch elseBranch : ProgHOL width)
    (context : FiniteEvalContext width σ) (value : BitVec width)
    (hcond : evalHOLFinite context.state (h := context.memaddrsDecidable) condition =
      some (ValueHOL.val (HolWordLab.word value)))
    (hne : (value != 0) = true)
    (hsubInv : ∀ (result : Option (PanSemResultExact width)) (output : FiniteEvalContext width σ),
      evalPanSemRecursiveCallFiniteContext thenBranch context = some (result, output) →
      globalsShapes output.state = globalsShapes context.state) :
    ∀ (result : Option (PanSemResultExact width)) (output : FiniteEvalContext width σ),
      evalPanSemRecursiveCallFiniteContext (.ite condition thenBranch elseBranch) context =
        some (result, output) →
      globalsShapes output.state = globalsShapes context.state := by
  intro result output heval
  rw [evalPanSemRecursiveCallFiniteContext.eq_def] at heval
  dsimp only at heval
  rw [hcond] at heval
  dsimp only at heval
  rw [if_pos hne] at heval
  exact hsubInv result output heval

theorem globalsShapes_ite_else_arm {width : Nat} {σ : Type} [NeZero width]
    (condition : ExpHOL width) (thenBranch elseBranch : ProgHOL width)
    (context : FiniteEvalContext width σ) (value : BitVec width)
    (hcond : evalHOLFinite context.state (h := context.memaddrsDecidable) condition =
      some (ValueHOL.val (HolWordLab.word value)))
    (hz : (value != 0) = false)
    (hsubInv : ∀ (result : Option (PanSemResultExact width)) (output : FiniteEvalContext width σ),
      evalPanSemRecursiveCallFiniteContext elseBranch context = some (result, output) →
      globalsShapes output.state = globalsShapes context.state) :
    ∀ (result : Option (PanSemResultExact width)) (output : FiniteEvalContext width σ),
      evalPanSemRecursiveCallFiniteContext (.ite condition thenBranch elseBranch) context =
        some (result, output) →
      globalsShapes output.state = globalsShapes context.state := by
  intro result output heval
  rw [evalPanSemRecursiveCallFiniteContext.eq_def] at heval
  dsimp only at heval
  rw [hcond] at heval
  dsimp only at heval
  rw [if_neg (by rw [hz]; decide)] at heval
  exact hsubInv result output heval

/-- While-arm helper for the recursive `globalsShapes` invariant (HOL
    `panPropsScript.sml:1183` `evaluate_global_shape_invariant`).  The While
    arm writes no global binding, so once the body recursion and the loop
    recursion preserve the global shapes the whole arm does. -/
theorem globalsShapes_while_arm {width : Nat} {σ : Type} [NeZero width]
    (condition : ExpHOL width) (body : ProgHOL width)
    (context : FiniteEvalContext width σ)
    (hbodyInv : ∀ (result : Option (PanSemResultExact width)) (output : FiniteEvalContext width σ),
      evalPanSemRecursiveCallFiniteContext body
          (context.withState (decClockHOLFinite context.state) rfl rfl) = some (result, output) →
        globalsShapes output.state = globalsShapes context.state)
    (hloopInv : ∀ (bodyResult : Option (PanSemResultExact width))
        (bodyContext : FiniteEvalContext width σ),
      evalPanSemRecursiveCallFiniteContext body
          (context.withState (decClockHOLFinite context.state) rfl rfl) = some (bodyResult, bodyContext) →
        (bodyResult = none ∨ bodyResult = some .continue) →
        ∀ (result : Option (PanSemResultExact width)) (output : FiniteEvalContext width σ),
          evalPanSemRecursiveCallFiniteContext (.while condition body)
            (bodyContext.withState
              (fixClockHOLFinite (decClockHOLFinite context.state)
                (bodyResult, bodyContext.state)).2 rfl rfl) = some (result, output) →
          globalsShapes output.state = globalsShapes context.state) :
    ∀ (result : Option (PanSemResultExact width)) (output : FiniteEvalContext width σ),
      evalPanSemRecursiveCallFiniteContext (.while condition body) context = some (result, output) →
      globalsShapes output.state = globalsShapes context.state := by
  intro result output heval
  rw [evalPanSemRecursiveCallFiniteContext.eq_def] at heval
  dsimp only at heval
  cases hcond : evalHOLFinite context.state (h := context.memaddrsDecidable) condition with
  | none =>
      rw [hcond] at heval; try simp only [] at heval
      simp only [Option.some.injEq, Prod.mk.injEq] at heval
      rcases heval with ⟨_, rfl⟩
      rfl
  | some v =>
      cases v with
      | rStruct fields =>
          rw [hcond] at heval; try simp only [] at heval
          simp only [Option.some.injEq, Prod.mk.injEq] at heval
          rcases heval with ⟨_, rfl⟩
          rfl
      | nStruct name fields =>
          rw [hcond] at heval; try simp only [] at heval
          simp only [Option.some.injEq, Prod.mk.injEq] at heval
          rcases heval with ⟨_, rfl⟩
          rfl
      | val w =>
          cases w with
          | word word =>
              rw [hcond] at heval; try simp only [] at heval
              by_cases hw : word ≠ 0
              · rw [if_pos hw] at heval; try simp only [] at heval
                by_cases hclock : context.state.clock = 0
                · rw [if_pos hclock] at heval; try simp only [] at heval
                  simp only [Option.some.injEq, Prod.mk.injEq] at heval
                  rcases heval with ⟨_, rfl⟩
                  exact globalsShapes_emptyLocalsHOLFinite context.state
                · rw [if_neg hclock] at heval; try simp only [] at heval
                  cases hbody : evalPanSemRecursiveCallFiniteContext body
                      (context.withState (decClockHOLFinite context.state) rfl rfl) with
                  | none => rw [hbody] at heval; simp at heval
                  | some p =>
                      obtain ⟨bodyResult, bodyContext⟩ := p
                      rw [hbody] at heval; try simp only [] at heval
                      have hbodyGlob : globalsShapes bodyContext.state = globalsShapes context.state :=
                        hbodyInv bodyResult bodyContext hbody
                      have hfixedGlob : ∀ (br : Option (PanSemResultExact width)),
                          globalsShapes (bodyContext.withState
                            (fixClockHOLFinite (decClockHOLFinite context.state)
                              (br, bodyContext.state)).2 rfl rfl).state =
                            globalsShapes context.state := by
                        intro br
                        show globalsShapes (fixClockHOLFinite (decClockHOLFinite context.state)
                          (br, bodyContext.state)).2 = globalsShapes context.state
                        rw [globalsShapes_fixClockHOLFinite]
                        exact hbodyGlob
                      cases bodyResult with
                      | none =>
                          exact hloopInv none bodyContext hbody (Or.inl rfl) result output heval
                      | some r =>
                          cases r with
                          | «continue» =>
                              exact hloopInv (some .continue) bodyContext hbody (Or.inr rfl) result output heval
                          | error =>
                              simp only [Option.some.injEq, Prod.mk.injEq] at heval
                              rcases heval with ⟨_, rfl⟩
                              exact hfixedGlob (some .error)
                          | timeOut =>
                              simp only [Option.some.injEq, Prod.mk.injEq] at heval
                              rcases heval with ⟨_, rfl⟩
                              exact hfixedGlob (some .timeOut)
                          | «break» =>
                              simp only [Option.some.injEq, Prod.mk.injEq] at heval
                              rcases heval with ⟨_, rfl⟩
                              exact hfixedGlob (some .break)
                          | returned value =>
                              simp only [Option.some.injEq, Prod.mk.injEq] at heval
                              rcases heval with ⟨_, rfl⟩
                              exact hfixedGlob (some (.returned value))
                          | exception exceptionId value =>
                              simp only [Option.some.injEq, Prod.mk.injEq] at heval
                              rcases heval with ⟨_, rfl⟩
                              exact hfixedGlob (some (.exception exceptionId value))
                          | finalFfi event =>
                              simp only [Option.some.injEq, Prod.mk.injEq] at heval
                              rcases heval with ⟨_, rfl⟩
                              exact hfixedGlob (some (.finalFfi event))
              · rw [if_neg hw] at heval; try simp only [] at heval
                simp only [Option.some.injEq, Prod.mk.injEq] at heval
                rcases heval with ⟨_, rfl⟩
                rfl


/-- Flapjack-specific infrastructure for HOL `panPropsScript.sml:1183`
`evaluate_global_shape_invariant`: the `Call` arm of the recursive exact evaluator
preserves `globalsShapes`, given the invariants for the callee-body recursion and the
exception-handler recursion. Untagged. -/
theorem globalsShapes_call_arm {width : Nat} {σ : Type} [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width))
    (context : FiniteEvalContext width σ)
    (values : List (ValueHOL width))
    (hargs : evalListHOLFinite context.state (h := context.memaddrsDecidable) arguments = some values)
    (hbodyInv : ∀ (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
        (returnShape : ShapeHOL) (bodyResult : Option (PanSemResultExact width))
        (bodyContext : FiniteEvalContext width σ),
        lookupCodeHOLFinite context.state.code.lookup function values =
          some (body, callee, returnShape) →
        evalPanSemRecursiveCallFiniteContext body
          (callEntryContextHOLFinite context callee) = some (bodyResult, bodyContext) →
        globalsShapes bodyContext.state = globalsShapes context.state)
    (hhandlerInv : ∀ (handlerVar : MlS) (value : ValueHOL width) (handlerProgram : ProgHOL width)
        (fixedContext : FiniteEvalContext width σ)
        (result : Option (PanSemResultExact width)) (output : FiniteEvalContext width σ),
        evalPanSemRecursiveCallFiniteContext handlerProgram
          (callContinuationContextHOLFinite context fixedContext handlerVar value) =
            some (result, output) →
        globalsShapes output.state = globalsShapes context.state) :
    ∀ result output,
      evalPanSemRecursiveCallFiniteContext (.call info function arguments) context =
        some (result, output) →
      globalsShapes output.state = globalsShapes context.state := by
  intro result output heval
  rw [evalPanSemRecursiveCallFiniteContext.eq_def] at heval
  dsimp only at heval
  rw [hargs] at heval
  try simp only [] at heval
  cases hcode : lookupCodeHOLFinite context.state.code.lookup function values with
  | none =>
      rw [hcode] at heval
      try simp only [] at heval
      simp only [Option.some.injEq, Prod.mk.injEq] at heval
      rcases heval with ⟨_, rfl⟩
      rfl
  | some triple =>
      obtain ⟨body, callee, returnShape⟩ := triple
      rw [hcode] at heval
      try simp only [] at heval
      by_cases hclock : context.state.clock = 0
      · rw [if_pos hclock] at heval
        try simp only [] at heval
        simp only [Option.some.injEq, Prod.mk.injEq] at heval
        rcases heval with ⟨_, rfl⟩
        show globalsShapes (emptyLocalsHOLFinite context.state) = globalsShapes context.state
        exact globalsShapes_emptyLocalsHOLFinite context.state
      · rw [if_neg hclock] at heval
        try simp only [] at heval
        cases hbody : evalPanSemRecursiveCallFiniteContext body
            (callEntryContextHOLFinite context callee) with
        | none =>
            rw [hbody] at heval
            simp at heval
        | some p =>
            obtain ⟨bodyResult, bodyContext⟩ := p
            rw [hbody] at heval
            try simp only [] at heval
            have hbodyGlob := hbodyInv body callee returnShape bodyResult bodyContext hcode hbody
            have hfixedGlob : ∀ br : Option (PanSemResultExact width),
                globalsShapes (fixClockHOLFinite (callEntryStateHOLFinite context.state callee)
                  (br, bodyContext.state)).2 = globalsShapes context.state := by
              intro br
              rw [globalsShapes_fixClockHOLFinite]
              exact hbodyGlob
            have hEmpty : ∀ br : Option (PanSemResultExact width),
                globalsShapes (emptyLocalsHOLFinite
                  (fixClockHOLFinite (callEntryStateHOLFinite context.state callee)
                    (br, bodyContext.state)).2) = globalsShapes context.state := by
              intro br
              rw [globalsShapes_emptyLocalsHOLFinite]
              exact hfixedGlob br
            have hLocals : ∀ br : Option (PanSemResultExact width),
                globalsShapes
                  { (fixClockHOLFinite (callEntryStateHOLFinite context.state callee)
                      (br, bodyContext.state)).2 with locals := context.state.locals } =
                  globalsShapes context.state := by
              intro br
              rw [globalsShapes_setLocals]
              exact hfixedGlob br
            cases bodyResult with
            | none =>
                try simp only [] at heval
                simp only [Option.some.injEq, Prod.mk.injEq] at heval
                rcases heval with ⟨_, rfl⟩
                exact hfixedGlob none
            | some r =>
                try simp only [] at heval
                cases r with
                | error =>
                    try simp only [] at heval
                    simp only [Option.some.injEq, Prod.mk.injEq] at heval
                    rcases heval with ⟨_, rfl⟩
                    exact hfixedGlob (some .error)
                | timeOut =>
                    try simp only [] at heval
                    simp only [Option.some.injEq, Prod.mk.injEq] at heval
                    rcases heval with ⟨_, rfl⟩
                    exact hEmpty (some .timeOut)
                | «break» =>
                    try simp only [] at heval
                    simp only [Option.some.injEq, Prod.mk.injEq] at heval
                    rcases heval with ⟨_, rfl⟩
                    exact hfixedGlob (some .break)
                | «continue» =>
                    try simp only [] at heval
                    simp only [Option.some.injEq, Prod.mk.injEq] at heval
                    rcases heval with ⟨_, rfl⟩
                    exact hfixedGlob (some .continue)
                | returned value =>
                    try simp only [] at heval
                    by_cases hshape : shapeEqHOL (shapeOfHOLExact value) returnShape = true
                    · rw [if_pos hshape] at heval
                      try simp only [] at heval
                      cases info with
                      | none =>
                          try simp only [] at heval
                          simp only [Option.some.injEq, Prod.mk.injEq] at heval
                          rcases heval with ⟨_, rfl⟩
                          exact hEmpty (some (.returned value))
                      | some pair =>
                          obtain ⟨varOpt, _rest⟩ := pair
                          cases varOpt with
                          | none =>
                              try simp only [] at heval
                              simp only [Option.some.injEq, Prod.mk.injEq] at heval
                              rcases heval with ⟨_, rfl⟩
                              exact hLocals (some (.returned value))
                          | some kv =>
                              obtain ⟨kind, name⟩ := kv
                              try simp only [] at heval
                              by_cases hvalid : isValidValueHOLExact context.state.toExact kind name value = true
                              · rw [if_pos hvalid] at heval
                                try simp only [] at heval
                                simp only [Option.some.injEq, Prod.mk.injEq] at heval
                                rcases heval with ⟨_, rfl⟩
                                have hm := hLocals (some (.returned value))
                                exact (globalsShapes_setKvarHOLFinite_of_globalsShapes
                                  (source := context.state) kind name value _ hm hvalid).trans hm
                              · rw [if_neg hvalid] at heval
                                try simp only [] at heval
                                simp only [Option.some.injEq, Prod.mk.injEq] at heval
                                rcases heval with ⟨_, rfl⟩
                                exact hfixedGlob (some (.returned value))
                    · rw [if_neg hshape] at heval
                      try simp only [] at heval
                      simp only [Option.some.injEq, Prod.mk.injEq] at heval
                      rcases heval with ⟨_, rfl⟩
                      exact hfixedGlob (some (.returned value))
                | exception exceptionId value =>
                    try simp only [] at heval
                    cases info with
                    | none =>
                        try simp only [] at heval
                        simp only [Option.some.injEq, Prod.mk.injEq] at heval
                        rcases heval with ⟨_, rfl⟩
                        exact hEmpty (some (.exception exceptionId value))
                    | some pair =>
                        obtain ⟨_varOpt, hopt⟩ := pair
                        cases hopt with
                        | none =>
                            try simp only [] at heval
                            simp only [Option.some.injEq, Prod.mk.injEq] at heval
                            rcases heval with ⟨_, rfl⟩
                            exact hEmpty (some (.exception exceptionId value))
                        | some triple =>
                            obtain ⟨handlerId, handlerVar, handlerProgram⟩ := triple
                            try simp only [] at heval
                            by_cases heq : exceptionId = handlerId
                            · rw [if_pos heq] at heval
                              try simp only [] at heval
                              cases hlookup : context.state.eshapes.lookup exceptionId with
                              | none =>
                                  rw [hlookup] at heval
                                  try simp only [] at heval
                                  try simp only [Option.some.injEq, Prod.mk.injEq] at heval
                                  rcases heval with ⟨_, rfl⟩
                                  exact hfixedGlob (some (.exception exceptionId value))
                              | some shape =>
                                  rw [hlookup] at heval
                                  try simp only [] at heval
                                  by_cases hguard :
                                      (shapeEqHOL (shapeOfHOLExact value) shape &&
                                        isValidValueHOLExact context.state.toExact .local handlerVar value) = true
                                  · rw [if_pos hguard] at heval
                                    try simp only [] at heval
                                    exact hhandlerInv handlerVar value handlerProgram
                                      (bodyContext.withState
                                        (fixClockHOLFinite (callEntryStateHOLFinite context.state callee)
                                          ((some (.exception exceptionId value) :
                                            Option (PanSemResultExact width)), bodyContext.state)).2
                                        rfl rfl)
                                      result output heval
                                  · rw [if_neg hguard] at heval
                                    try simp only [] at heval
                                    simp only [Option.some.injEq, Prod.mk.injEq] at heval
                                    rcases heval with ⟨_, rfl⟩
                                    exact hfixedGlob (some (.exception exceptionId value))
                            · rw [if_neg heq] at heval
                              try simp only [] at heval
                              simp only [Option.some.injEq, Prod.mk.injEq] at heval
                              rcases heval with ⟨_, rfl⟩
                              exact hEmpty (some (.exception exceptionId value))
                | finalFfi event =>
                    try simp only [] at heval
                    simp only [Option.some.injEq, Prod.mk.injEq] at heval
                    rcases heval with ⟨_, rfl⟩
                    exact hEmpty (some (.finalFfi event))

/-- FLAPJACK-SPECIFIC (not a HOL declaration): the `DecCall` arm of the
whole-program `globalsShapes` invariant used by HOL
`panPropsScript.sml:1183 evaluate_global_shape_invariant`. The callee-body and
named-continuation recursive invariants are supplied as hypotheses. -/
theorem globalsShapes_decCall_arm {width : Nat} {σ : Type} [NeZero width]
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (hargs : evalListHOLFinite context.state (h := context.memaddrsDecidable)
      arguments = some values)
    (hbodyInv : ∀ body callee returnShape bodyResult bodyContext,
      lookupCodeHOLFinite context.state.code.lookup function values =
        some (body, callee, returnShape) →
      evalPanSemRecursiveCallFiniteContext body
        (context.withState (callEntryStateHOLFinite context.state callee) rfl rfl) =
          some (bodyResult, bodyContext) →
      globalsShapes bodyContext.state = globalsShapes context.state)
    (hcontInv : ∀ (fixedContext : FiniteEvalContext width σ) (value : ValueHOL width)
      (continuationResult : Option (PanSemResultExact width))
      (continuationPost : FiniteEvalContext width σ),
      evalPanSemRecursiveCallFiniteContext continuation
        (callContinuationContextHOLFinite context fixedContext resultName value) =
          some (continuationResult, continuationPost) →
      globalsShapes continuationPost.state = globalsShapes context.state) :
    ∀ result output,
      evalPanSemRecursiveCallFiniteContext
        (.decCall resultName shape function arguments continuation) context =
          some (result, output) →
      globalsShapes output.state = globalsShapes context.state := by
  intro result output heval
  rw [evalPanSemRecursiveCallFiniteContext.eq_def] at heval
  dsimp only at heval
  rw [hargs] at heval
  try simp only [] at heval
  cases hcode : lookupCodeHOLFinite context.state.code.lookup function values with
  | none =>
      rw [hcode] at heval
      try simp only [] at heval
      simp only [Option.some.injEq, Prod.mk.injEq] at heval
      rcases heval with ⟨_, rfl⟩
      rfl
  | some triple =>
      obtain ⟨body, callee, returnShape⟩ := triple
      rw [hcode] at heval
      try simp only [] at heval
      by_cases hclock : context.state.clock = 0
      · rw [if_pos hclock] at heval
        try simp only [] at heval
        simp only [Option.some.injEq, Prod.mk.injEq] at heval
        rcases heval with ⟨_, rfl⟩
        show globalsShapes (emptyLocalsHOLFinite context.state) =
          globalsShapes context.state
        exact globalsShapes_emptyLocalsHOLFinite context.state
      · rw [if_neg hclock] at heval
        try simp only [] at heval
        cases hbody : evalPanSemRecursiveCallFiniteContext body
            (context.withState (callEntryStateHOLFinite context.state callee) rfl rfl) with
        | none =>
            rw [hbody] at heval
            simp at heval
        | some p =>
            obtain ⟨bodyResult, bodyContext⟩ := p
            rw [hbody] at heval
            try simp only [] at heval
            have hbodyGlob :=
              hbodyInv body callee returnShape bodyResult bodyContext hcode hbody
            have hfixedGlob : ∀ br : Option (PanSemResultExact width),
                globalsShapes (callFixedContextHOLFinite
                  (callEntryStateHOLFinite context.state callee) br bodyContext).state =
                    globalsShapes context.state := by
              intro br
              show globalsShapes (fixClockHOLFinite
                (callEntryStateHOLFinite context.state callee)
                (br, bodyContext.state)).2 = globalsShapes context.state
              rw [globalsShapes_fixClockHOLFinite]
              exact hbodyGlob
            have hEmpty : ∀ br : Option (PanSemResultExact width),
                globalsShapes (emptyLocalsHOLFinite (callFixedContextHOLFinite
                  (callEntryStateHOLFinite context.state callee) br bodyContext).state) =
                    globalsShapes context.state := by
              intro br
              rw [globalsShapes_emptyLocalsHOLFinite]
              exact hfixedGlob br
            cases bodyResult with
            | none =>
                try simp only [] at heval
                simp only [Option.some.injEq, Prod.mk.injEq] at heval
                rcases heval with ⟨_, rfl⟩
                exact hfixedGlob none
            | some r =>
                cases r with
                | «break» =>
                    try simp only [] at heval
                    simp only [Option.some.injEq, Prod.mk.injEq] at heval
                    rcases heval with ⟨_, rfl⟩
                    exact hfixedGlob (some .break)
                | «continue» =>
                    try simp only [] at heval
                    simp only [Option.some.injEq, Prod.mk.injEq] at heval
                    rcases heval with ⟨_, rfl⟩
                    exact hfixedGlob (some .continue)
                | returned value =>
                    try simp only [] at heval
                    by_cases hg : (shapeEqHOL (shapeOfHOLExact value) shape &&
                        shapeEqHOL (shapeOfHOLExact value) returnShape) = true
                    · rw [if_pos hg] at heval
                      try simp only [] at heval
                      cases hcont : evalPanSemRecursiveCallFiniteContext continuation
                          (callContinuationContextHOLFinite context
                            (callFixedContextHOLFinite
                              (callEntryStateHOLFinite context.state callee)
                              (some (.returned value)) bodyContext) resultName value) with
                      | none =>
                          rw [hcont] at heval
                          simp at heval
                      | some q =>
                          obtain ⟨contResult, contPost⟩ := q
                          rw [hcont] at heval
                          try simp only [] at heval
                          have hcontGlob :=
                            hcontInv (callFixedContextHOLFinite
                                (callEntryStateHOLFinite context.state callee)
                                (some (.returned value)) bodyContext)
                              value contResult contPost hcont
                          simp only [Option.some.injEq, Prod.mk.injEq] at heval
                          rcases heval with ⟨_, rfl⟩
                          rw [globalsShapes_setLocals]
                          exact hcontGlob
                    · rw [if_neg hg] at heval
                      try simp only [] at heval
                      simp only [Option.some.injEq, Prod.mk.injEq] at heval
                      rcases heval with ⟨_, rfl⟩
                      exact hfixedGlob (some (.returned value))
                | error =>
                    try simp only [] at heval
                    simp only [Option.some.injEq, Prod.mk.injEq] at heval
                    rcases heval with ⟨_, rfl⟩
                    exact hEmpty (some .error)
                | timeOut =>
                    try simp only [] at heval
                    simp only [Option.some.injEq, Prod.mk.injEq] at heval
                    rcases heval with ⟨_, rfl⟩
                    exact hEmpty (some .timeOut)
                | exception exceptionId value =>
                    try simp only [] at heval
                    simp only [Option.some.injEq, Prod.mk.injEq] at heval
                    rcases heval with ⟨_, rfl⟩
                    exact hEmpty (some (.exception exceptionId value) :
                      Option (PanSemResultExact width))
                | finalFfi event =>
                    try simp only [] at heval
                    simp only [Option.some.injEq, Prod.mk.injEq] at heval
                    rcases heval with ⟨_, rfl⟩
                    exact hEmpty (some (.finalFfi event) :
                      Option (PanSemResultExact width))

section GlobalsShapesInvariant

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- HOL `panPropsScript.sml:1183` `evaluate_global_shape_invariant` lifted to the exact
PanSem recursive evaluator: the full-program evaluation preserves the global shape map.
Flapjack-specific infrastructure; see `globalsShapes` and the per-arm lemmas in
`PanSem/GlobalsShapesExact.lean`. -/
theorem evalPanSemRecursiveCallFiniteContext_globalsShapesInvariant {width : Nat} {σ : Type}
    [NeZero width] (program : ProgHOL width) (sourceContext : FiniteEvalContext width σ) :
    ∀ result output, evalPanSemRecursiveCallFiniteContext program sourceContext = some (result, output) →
      globalsShapes output.state = globalsShapes sourceContext.state := by
  fun_induction evalPanSemRecursiveCallFiniteContext program sourceContext
  all_goals
    intro result output heval
    (try (simp only [Option.some.injEq, Prod.mk.injEq] at heval))
    (try (rcases heval with ⟨rfl, rfl⟩))
    (try (simp only [FiniteEvalContext.withState_state] at *))
    (try (rename_i ihA; simp only [ihA _ _ (by assumption)] at *))
    (try (rename_i ihB; simp only [ihB _ _ (by assumption)] at *))
    (try (simp only [globalsShapes_emptyLocalsHOLFinite,
      globalsShapes_decClockHOLFinite] at *))
    (try rfl)
    (try assumption)
    (try (dsimp (config := { zeta := true }) at *))
    (try assumption)
    (try (simp_all [globalsShapes_eq_globalsShapesExact_toExact]))
    (try (dsimp (config := { zeta := true }) at *))
    (try assumption)

  case case66 =>
    rename_i inst context state other pair a14 a13 a12 a11 a10 a9 a8 a7 a6 a5 a4 a3 a2 a1 a0 hres
    simpa only [globalsShapes_eq_globalsShapesExact_toExact] using
      @evalPanSemNonrecursiveHOLFinite_globalsShapes width σ _ state context.memaddrsDecidable
        context.shMemaddrsDecidable other pair.1 pair.2 hres
  case case63 =>
    rename_i inst context state size kind name address evalExpression output
    change globalsShapesExact output.snd = globalsShapesExact context.state.toExact
    exact @shMemLoadClauseHOLExact_globalsShapesExact width σ _ state.toExact
      context.shMemaddrsDecidable size kind name address
      (fun x expression => @evalHOLExact width σ _ state.toExact context.memaddrsDecidable expression)
  case case64 =>
    rename_i inst context state size address value evalExpression output
    change globalsShapesExact output.snd = globalsShapesExact context.state.toExact
    exact @shMemStoreClauseHOLExact_globalsShapesExact width σ _ state.toExact
      context.shMemaddrsDecidable size address value
      (fun x expression => @evalHOLExact width σ _ state.toExact context.memaddrsDecidable expression)
  case case46 =>
    rename_i inst context state resultName shape func arguments continuation values x3 body callee returnShape x2 hclock entry entryContext post1 value result post restored fixedContext continuationContext hshape x1 x ih2 ih1
    exact ih1.trans ih2
  case case28 =>
    rename_i inst context state func arguments values x2 body callee returnShape x1 hclock entry entryContext postContext value hshape kind name snd hvalid x fixedContext ih1
    cases kind
    · change globalsShapesExact postContext.state.toExact = globalsShapesExact context.state.toExact
      exact ih1
    · simp only [callSetKvarContextHOLFinite, FiniteEvalContext.withState_state,
        toExact_setKvarHOLFinite]
      funext key
      by_cases hk : key = name
      · have hshapeVal := isValidValueHOLExact_global_shape state.toExact name value hvalid
        simp only [globalsShapesExact, setKvarHOLExact, if_true, hk, Option.map_some]
        exact hshapeVal.symm
      · have hkey := congrFun ih1 key
        simp only [globalsShapesExact, setKvarHOLExact, if_neg hk]
        exact hkey

/-- Per-name globals shape preservation for the top-level finite PanSem evaluator.
HOL `panPropsScript.sml:1183 evaluate_global_shape_invariant` states
`evaluate (p,s) = (res,st) ∧ FLOOKUP s.globals n = SOME v ⇒
∃v'. FLOOKUP st.globals n = SOME v' ∧ shape_of v' = shape_of v`;
this is that statement (curried, `FLOOKUP` as `lookup`, `shape_of` as `shapeOfHOLExact`) under the
type-indexed `'a word` / `'ffi` translation, obtained by lifting the delivered recursive
`evalPanSemRecursiveCallFiniteContext_globalsShapesInvariant` through
`evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_global_shape_invariant"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_global_shape_invariant {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (program : ProgHOL width)
    (res : Option (PanSemResultExact width)) (st : PanSemStateFiniteExact width σ)
    (name : MlS) (value : ValueHOL width)
    (heval : evaluateHOLFiniteState state program = (res, st))
    (hlookup : state.globals.lookup name = some value) :
    ∃ value', st.globals.lookup name = some value' ∧
      shapeOfHOLExact value' = shapeOfHOLExact value := by
  classical
  let context : FiniteEvalContext width σ :=
    ⟨state, (fun address => Classical.propDecidable (state.memaddrs address)),
      (fun address => Classical.propDecidable (state.shMemaddrs address))⟩
  obtain ⟨postContext, hevalCtx, hstate⟩ :=
    evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState state program context rfl
      (res, st) heval
  have hglob :=
    evalPanSemRecursiveCallFiniteContext_globalsShapesInvariant program context res postContext
      hevalCtx
  rw [hstate] at hglob
  change globalsShapes st = globalsShapes state at hglob
  obtain ⟨w, hw⟩ : ∃ w : ValueHOL width, st.globals.lookup name = some w ∧
      shapeOfHOLExact w = shapeOfHOLExact value := by
    have hfun := congrFun hglob name
    simp only [globalsShapes] at hfun
    rw [hlookup] at hfun
    cases h : st.globals.lookup name with
    | none => rw [h] at hfun; simp at hfun
    | some w =>
        rw [h] at hfun
        simp only [Option.map_some] at hfun
        exact ⟨w, rfl, by simpa using hfun⟩
  exact ⟨w, hw.1, hw.2⟩

end GlobalsShapesInvariant

end PanSemStateFiniteExact

end Flapjack
