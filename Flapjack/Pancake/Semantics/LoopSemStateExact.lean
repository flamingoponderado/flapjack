import Flapjack.Pancake.Semantics.LoopSemState
import Flapjack.Pancake.LoopLang
import Flapjack.Pancake.Semantics.CrepSem.HOLState

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

end LoopSemStateFiniteExact

end Flapjack
