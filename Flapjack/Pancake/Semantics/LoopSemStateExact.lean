import Flapjack.Pancake.Semantics.LoopSemState
import Flapjack.Pancake.Semantics.LoopProps
import Flapjack.Pancake.LoopLang
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.FfiBridge

/-!
# Exact finite-support HOL `loopSem$state` carrier

Counterpart of the `state` datatype in
`cakeml/pancake/semantics/loopSemScript.sml:13-27`:

```
state =
  <| locals  : ('a word_loc) num_map
   ; globals : 5 word  |-> 'a word_loc
   ; memory  : 'a word -> 'a word_loc
   ; mdomain : ('a word) set
   ; sh_mdomain : ('a word) set
   ; clock   : num
   ; code    : (num list # ('a loopLang$prog)) num_map
   ; be      : bool
   ; ffi     : 'ffi ffi_state
   ; base_addr   : 'a word
   ; top_addr    : 'a word |>
```

`LoopSemStateFiniteExact` is the source-shaped carrier whose three HOL finite
maps (`locals`, `globals`, `code`) use the reviewed canonical
`HolFiniteMapExact` translation, whose `code` entries use the exact
`HolLoopProg` carrier, and whose `ffi` field uses the exact `HolFfiState`.  The
word dimension is the nonzero `BitVec width` model; `memory` is total and the
domains are Lean sets, both matching HOL.  The structure carries an exact
`@[hol]` `state` tag with the `fmap_as_finite_support` qualifier naming exactly
the three translated map fields.

The production `LoopMachineState` bridge and the `get_var_imm`/`get_vars`
carrier-level statements live in `LoopSemState.lean`; the bridge to the
production state over this exact carrier is tracked separately on
`flapjack-pxn.18.5.17.1`.
-/

namespace Flapjack

/-- Broad (unrestricted) counterpart of `LoopSemStateFiniteExact`: the three map
    fields are plain lookup functions, a strict superset of HOL's finite maps.
    It exists only to state the canonical finite-map translation witness
    `holFmapAsFiniteSupportWitness`; `FiniteSupport` cuts out the HOL-image
    subcarrier. -/
structure LoopSemStateBroad (width : Nat) [NeZero width] (F : Type) where
  locals : Nat → Option (WordLocW width)
  globals : BitVec 5 → Option (WordLocW width)
  memory : BitVec width → WordLocW width
  mdomain : BitVec width → Bool
  shMdomain : BitVec width → Bool
  clock : Nat
  code : Nat → Option (List Nat × HolLoopProg width)
  be : Bool
  ffi : HolFfiState F
  baseAddr : BitVec width
  topAddr : BitVec width

/-- Field-wise finite support of `LoopSemStateBroad`, matching HOL's `|->`
    and `num_map` fields. -/
def LoopSemStateBroad.FiniteSupport {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateBroad width F) : Prop :=
  (∃ keys : List Nat, ∀ key, state.locals key ≠ none → key ∈ keys) ∧
  (∃ keys : List (BitVec 5), ∀ key, state.globals key ≠ none → key ∈ keys) ∧
  (∃ keys : List Nat, ∀ key, state.code key ≠ none → key ∈ keys)

/-- Exact HOL `loopSem$state` (`loopSemScript.sml:13-27`) over the reviewed
    canonical finite-map, loop-program, and FFI carriers. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "state"
  (fmap_as_finite_support := [locals, globals, code])]
structure LoopSemStateFiniteExact (width : Nat) [NeZero width] (F : Type) where
  locals : HolFiniteMapExact Nat (WordLocW width)
  globals : HolFiniteMapExact (BitVec 5) (WordLocW width)
  memory : BitVec width → WordLocW width
  mdomain : BitVec width → Bool
  shMdomain : BitVec width → Bool
  clock : Nat
  code : HolFiniteMapExact Nat (List Nat × HolLoopProg width)
  be : Bool
  ffi : HolFfiState F
  baseAddr : BitVec width
  topAddr : BitVec width

/-- Forget the finite-support witnesses, reading every map through `.lookup`. -/
def LoopSemStateFiniteExact.toBroad {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateFiniteExact width F) : LoopSemStateBroad width F where
  locals := state.locals.lookup
  globals := state.globals.lookup
  memory := state.memory
  mdomain := state.mdomain
  shMdomain := state.shMdomain
  clock := state.clock
  code := state.code.lookup
  be := state.be
  ffi := state.ffi
  baseAddr := state.baseAddr
  topAddr := state.topAddr

/-- The projection lands in the finite-support subtype. -/
theorem LoopSemStateFiniteExact.toBroad_finiteSupport {width : Nat} [NeZero width]
    {F : Type} (state : LoopSemStateFiniteExact width F) :
    state.toBroad.FiniteSupport :=
  ⟨state.locals.finiteSupport, state.globals.finiteSupport, state.code.finiteSupport⟩

/-- Rebuild the finite-map carrier from a broad state together with a
    finite-support proof; the inverse of `toBroad` on the finite-support
    subtype. -/
def LoopSemStateBroad.ofBroad {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateBroad width F) (h : state.FiniteSupport) :
    LoopSemStateFiniteExact width F where
  locals := { lookup := state.locals, finiteSupport := h.1 }
  globals := { lookup := state.globals, finiteSupport := h.2.1 }
  memory := state.memory
  mdomain := state.mdomain
  shMdomain := state.shMdomain
  clock := state.clock
  code := { lookup := state.code, finiteSupport := h.2.2 }
  be := state.be
  ffi := state.ffi
  baseAddr := state.baseAddr
  topAddr := state.topAddr

/-- `toBroad` after `ofBroad` is the identity on a finite-support broad state. -/
theorem LoopSemStateBroad.toBroad_ofBroad {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateBroad width F) (h : state.FiniteSupport) :
    (ofBroad state h).toBroad = state := rfl

/-- `ofBroad` after `toBroad` is the identity on the finite-map carrier. -/
theorem LoopSemStateBroad.ofBroad_toBroad {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateFiniteExact width F) :
    ofBroad state.toBroad state.toBroad_finiteSupport = state := by
  cases state
  rfl

namespace LoopSemStateFiniteExact

/-- Canonical kernel witness for the `fmap_as_finite_support` `@[hol]`
    qualifier on `LoopSemStateFiniteExact`: the finite-map carrier is
    invertibly related to the broad one. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  ⟨fun state h => LoopSemStateBroad.toBroad_ofBroad state h,
    fun state => LoopSemStateBroad.ofBroad_toBroad state⟩

/-- Exact port of HOL `get_var_imm_def`
    (`cakeml/pancake/semantics/loopSemScript.sml:165-167`):

    ```
    (get_var_imm ((Reg n):'a reg_imm) ^s = sptree$lookup n s.locals) /\
    (get_var_imm (Imm w) s = SOME(Word w))
    ```

    The Lean statement is operand-first as in HOL, reads the `locals` field of
    the exact `LoopSemStateFiniteExact` state carrier (the reviewed canonical
    `HolFiniteMapExact` translation of HOL's `'a word_loc num_map`, hence the
    `(fmap_as_finite_support := [locals])` qualifier), and returns the exact
    `WordLocW` carrier (tagged `word_loc`). No extra hypotheses beyond
    `[NeZero width]`. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "get_var_imm_def"
  (fmap_as_finite_support := [locals])]
def getVarImm {width : Nat} [NeZero width] {F : Type}
    (operand : RegImm (BitVec width)) (state : LoopSemStateFiniteExact width F) :
    Option (WordLocW width) :=
  match operand with
  | .reg name => state.locals.lookup name
  | .imm value => some (.word value)

@[simp] theorem getVarImm_reg {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateFiniteExact width F) (name : Nat) :
    getVarImm (.reg name) state = state.locals.lookup name := rfl

@[simp] theorem getVarImm_imm {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateFiniteExact width F) (value : BitVec width) :
    getVarImm (.imm value) state = some (.word value) := rfl

/-- Exact `get_vars_def` (`loopSemScript.sml:98-107`), state second as in HOL. -/
def getVars {width : Nat} [NeZero width] {F : Type} :
    List Nat → LoopSemStateFiniteExact width F → Option (List (WordLocW width))
  | [], _ => some []
  | name :: names, state =>
      (state.locals.lookup name).bind
        (fun value => (getVars names state).map (fun values => value :: values))

@[simp] theorem getVars_nil {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateFiniteExact width F) :
    getVars [] state = some [] := rfl

theorem getVars_cons {width : Nat} [NeZero width] {F : Type}
    (name : Nat) (names : List Nat) (state : LoopSemStateFiniteExact width F) :
    getVars (name :: names) state =
      (state.locals.lookup name).bind
        (fun value => (getVars names state).map (fun values => value :: values)) :=
  rfl

end LoopSemStateFiniteExact

/-- Observational bridge from the exact `LoopSemStateFiniteExact` to the
    production `LoopMachineState`.  Word-location payloads compare through
    `loopValueOfWordLocW`; the total `memory` is option-valued on the production
    side (always present); the address sets are `Bool` predicates on both
    sides; the code table is related by the production association list
    enumerating entries of the exact finite map (`num_map` has no enumeration
    order), with the executable program the `loopProgExecRel` image of the
    faithful one; and the FFI state by `FfiStateRel`. -/
def LoopSemStateFiniteExact.prodRel {width : Nat} [NeZero width] {F : Type}
    (state : LoopSemStateFiniteExact width F)
    (machine : LoopMachineState (BitVec width) F) : Prop :=
  (∀ name, machine.locals name = (state.locals.lookup name).map loopValueOfWordLocW) ∧
  (∀ global, machine.globals global = (state.globals.lookup global).map loopValueOfWordLocW) ∧
  (∀ address, machine.memory address = some (loopValueOfWordLocW (state.memory address))) ∧
  machine.mdomain = state.mdomain ∧
  machine.shMdomain = state.shMdomain ∧
  machine.clock = state.clock ∧
  machine.be = state.be ∧
  FfiStateRel machine.ffi state.ffi ∧
  machine.baseAddr = state.baseAddr ∧
  machine.topAddr = state.topAddr ∧
  (∀ entry, entry ∈ machine.code →
    ∃ program, state.code.lookup entry.1 = some (entry.2.1, program) ∧
      loopProgExecRel entry.2.2 program)

/-- Register reads through `get_var_imm` on the production state agree with the
    exact carrier's local lookup under `prodRel`. -/
theorem LoopSemStateFiniteExact.getVarImm_map_eq_of_prodRel {width : Nat} [NeZero width]
    {F : Type} {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (h : state.prodRel machine) (operand : RegImm (BitVec width)) :
    (LoopSemStateFiniteExact.getVarImm operand state).map loopValueOfWordLocW =
      Flapjack.getVarImm machine operand := by
  cases operand with
  | reg name => exact (h.1 name).symm
  | imm value => rfl

/-- Variable reads through `get_vars` on the production state agree with the
    exact carrier's recursive read under `prodRel`. -/
theorem LoopSemStateFiniteExact.getVars_map_eq_of_prodRel {width : Nat} [NeZero width]
    {F : Type} {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (h : state.prodRel machine) (names : List Nat) :
    (LoopSemStateFiniteExact.getVars names state).map (List.map loopValueOfWordLocW) =
      Flapjack.getVars names machine := by
  induction names with
  | nil => rfl
  | cons name names ih =>
      rw [LoopSemStateFiniteExact.getVars_cons, Flapjack.getVars, h.1 name]
      cases hlookup : state.locals.lookup name with
      | none => rfl
      | some value =>
          simp only [Option.bind_some, Option.map_some, Option.map_map]
          rw [← ih]
          cases hg : LoopSemStateFiniteExact.getVars names state <;> rfl

end Flapjack
