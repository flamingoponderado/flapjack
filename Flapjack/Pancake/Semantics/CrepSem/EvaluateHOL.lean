import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Pancake.Semantics.CrepSem.Primop
import Flapjack.Pancake.Semantics.CrepSem.LookupCode
import Flapjack.Pancake.Semantics.CrepSem.TotalEval
import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Pancake.Semantics.PanSem.ExtCallExact
import Flapjack.Pancake.Semantics.LoopSem
import Flapjack.FfiHOL

/-!
# Total HOL-shaped `crepSem$evaluate` over the exact Crep carriers

`cakeml/pancake/semantics/crepSemScript.sml:240-390` defines the total,
clock-based program evaluator `evaluate : ('a crepLang$prog # ('a,'ffi) crepSem$state)
-> result option # ('a,'ffi) crepSem$state`, by constructor recursion on the
program with the well-founded measure `(clock, prog_size)`.

This module ports that recursion directly over the exact Flapjack carriers:

* program syntax: `CrepProgHOL width` (`crepLang$prog`);
* state: `CrepSemHOLState width σ` (the finite-support 11-field `crepSem$state`);
* result: `Option (CrepResultHOLExact width)`, where `none` is HOL `NONE`
  (ordinary completion), exactly as `evaluate` returns `result option`. HOL
  `FinalFFI` always carries a `final_event`, so the event type is fixed at
  `HolFinalEvent` and is not `'ffi`-dependent.

The evaluator `evalCrepSemHOLProg` is a single total function with **no fuel**,
**no `Option`-valued fuel adapter**, and **no dependence on
`evalCrepRuntimeResult`**. It is not a wrapper: every clause is a literal
translation of the corresponding `evaluate_def` disjunct, including the
`fix_clock`/`dec_clock` split, the `While` loop-control labels, the `Call`
handler path, and the FFI clauses.

## Declaration-local representation notes

Most declarations here are intentionally **untagged**: the whole-program
statement shape is not yet the reviewed exact HOL statement (the `RiscV.Word
width` fixed-width model of HOL's arbitrary finite word dimension and the
omission of a general agreement proof with the executed interpreter). They are
declaration-local infrastructure only. The result carrier is the exact
`CrepResultHOLExact width`, so the `Return`/`Call` clauses no longer project
through the production `PanWordLab`; the production-carrier bridge
`CrepResultHOLExact.toProd`/`CrepResultHOL.toExact` is available for callers that
need it.

The tagged exceptions are the exact ports: `exitLoopCrepResult`, an exact
`@[hol]` port of `crepSem$exit_loop_def`, and the shared-memory helper family
`crepShMemLoadExactHOL`/`crepShMemStoreExactHOL`/`crepShMemOpExactHOL`, exact
`@[hol]` ports of `sh_mem_load_def`/`sh_mem_store_def`/`sh_mem_op_def` with
HOL's free byte count `nb` (the `(fmap_as_finite_support := [locals, globals,
code])` qualifier records the finite-support state carrier). `exitLoopCrepResult`
is stated over the genuinely exact width-indexed result carrier
`CrepResultHOLExact` (the `@[hol]` port of HOL `Datatype result`) whose `Return`
payload is `List (HolWordLab width)`, matching HOL's `('a word_lab) list`, and
whose `Exception` payload is `BitVec width`. The operator-indexed
`crepShMemLoadHOL`/`crepShMemStoreHOL` helpers are Flapjack specializations that
call the exact ports with `crepShMemByteWidth operator`.

* The evaluator now returns `Option (CrepResultHOLExact width)`, whose `Return`
  payload is exactly HOL's `('a word_lab) list` via `HolWordLab`; the production
  `CrepResultHOL` (whose `return` carries `List (PanWordLab (BitVec width))`)
  is reachable only through the checked bridge `CrepResultHOLExact.toProd`.
  The evaluator's whole-program statement remains untagged pending the
  fixed-width/FFI/agreement audit tracked separately; `CrepResultHOLExact` is
  the exact carrier for tagged result-level definitions such as
  `exit_loop_def`.
* `CrepSemHOLState` is the finite-support `HolFiniteMapExact` translation of
  HOL's `|->` fields; the state helpers `setVar`/`setGlobals`/`updLocals`/
  `emptyLocals`/`resVarEq` implement the HOL updates with HOL `=` equality.
* `panMemStore32HOL` and `callFFIHOL` use their reviewed exact carriers. The
  Crep ExtCall path now uses exact `BitVec 8` helpers
  `readBytearrayWordHOL`/`panMemLoadByteWord8HOL`/
  `panWriteBytearrayWord8HOL`. Legacy `UInt8` helpers remain untagged for the
  other word-load and production-adapter paths; their byte-carrier bridge is
  not claimed as a HOL port. `crepClockWordToBytes`/`crepClockWordOfBytes` are
  likewise not cited here as exact HOL ports.
* `Skip` is fully faithful: `evalCrepSemHOLProg state .skip = (none, state)`,
  matching HOL `evaluate (Skip, s) = (NONE, s)`. The direct oracle row is
  `skip_eval=T` in `scripts/hol-probes/crep_inline_eval_probe.out`.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-- HOL `is_load` (`cakeml/pancake/loop_callScript.sml:10-15`): true for the
    four shared-memory load operations. Flapjack-specific helper for the `ShMem`
    clause; no separate HOL declaration is claimed. -/
def crepIsLoadMemOp : CrepMemOp → Bool
  | .load | .load8 | .load16 | .load32 => true
  | .store | .store8 | .store16 | .store32 => false

/-- HOL `sh_mem_op` byte width (`crepSemScript.sml:210-218`): `Load`/`Store`
    use `0`, the `8`/`16`/`32` variants use `1`/`2`/`4`. -/
def crepShMemByteWidth : CrepMemOp → Nat
  | .load | .store => 0
  | .load8 | .store8 => 1
  | .load16 | .store16 => 2
  | .load32 | .store32 => 4

/-- Flapjack-only normalization that restates a derived state's memory domains
    from a base state. `evaluate_def` never changes `memaddrs`/`sh_memaddrs`, so
    this is the identity on any state produced by `evalCrepSemHOLProg`; it is
    used only to let recursive calls reuse the base state's explicit domain
    decision procedures. Reducible so the domain fields unfold during
    elaboration. -/
@[reducible] def crepStampExactDomains {width : Nat} [NeZero width] {σ : Type}
    (base s : CrepSemHOLState width σ) : CrepSemHOLState width σ :=
  { s with memaddrs := base.memaddrs, shMemaddrs := base.shMemaddrs }

/-- Exact `eval` application with the domain-membership decision procedure
    supplied explicitly, so the recursive evaluator can thread it without
    typeclass search on derived states. -/
def crepExactEvalExp {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (value : CrepExpHOL width) : Option (HolWordLab width) := by
  haveI : DecidablePred state.memaddrs := memDec
  exact evalCrepSemHOLExp state value

/-- Exact HOL `mem_store_32` application with an explicit domain decision. -/
def crepExactMemStore32 {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (address : BitVec width) (value : BitVec 32) :
    Option (BitVec width → HolWordLab width) := by
  haveI : DecidablePred state.memaddrs := memDec
  exact panMemStore32HOL state.memory state.memaddrs state.be address value

/-- Exact HOL `mem_store_byte` application with an explicit domain decision. -/
def crepExactMemStoreByte {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (address : BitVec width) (byte : UInt8) :
    Option (BitVec width → HolWordLab width) := by
  haveI : DecidablePred state.memaddrs := memDec
  exact panMemStoreByteHOL state.memory state.memaddrs state.be address byte

/-- Exact HOL `mem_load_byte` function with an explicit domain decision. -/
def crepExactMemLoadByte {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a)) :
    BitVec width → Option UInt8 := by
  haveI : DecidablePred state.memaddrs := memDec
  exact panMemLoadByteHOL state.memory state.memaddrs state.be

/-- Exact HOL `mem_load_byte` with the source `word8` carrier, for evaluator
    clauses whose FFI interface consumes HOL byte lists. -/
def crepExactMemLoadByteWord8 {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a)) :
    BitVec width → Option (BitVec 8) := by
  haveI : DecidablePred state.memaddrs := memDec
  exact panMemLoadByteWord8HOL state.memory state.memaddrs state.be

/-- Exact HOL `write_bytearray` application with an explicit domain decision. -/
def crepExactWriteBytearray {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (address : BitVec width) (bytes : List UInt8) :
    BitVec width → HolWordLab width := by
  haveI : DecidablePred state.memaddrs := memDec
  exact panWriteBytearrayHOL address bytes state.memory state.memaddrs state.be

/-- Exact HOL `write_bytearray` over source `word8` values. -/
def crepExactWriteBytearrayWord8 {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (address : BitVec width) (bytes : List (BitVec 8)) :
    BitVec width → HolWordLab width := by
  haveI : DecidablePred state.memaddrs := memDec
  exact panWriteBytearrayWord8HOL address bytes state.memory state.memaddrs state.be

/-- The `UInt8`-carrier store-byte helper is kernel-equal to the exact source
    `word8` helper: it differs only by the byte carrier
    (`UInt8` vs `BitVec 8`), through `panMemStoreByteHOL_eq_word8`. -/
theorem crepExactMemStoreByte_eq_word8 {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (address : BitVec width) (byte : UInt8) :
    crepExactMemStoreByte state memDec address byte =
      @panMemStoreByteWord8HOL width _ state.memory state.memaddrs memDec state.be
        address byte.toBitVec := by
  unfold crepExactMemStoreByte
  exact @panMemStoreByteHOL_eq_word8 width _ state.memory state.memaddrs memDec state.be
    address byte

/-- The `UInt8`-carrier load-byte helper is kernel-equal (up to `UInt8.ofBitVec`
    on each result) to the exact source `word8` helper, through
    `panMemLoadByteHOL_eq_word8_projection`. -/
theorem crepExactMemLoadByte_eq_word8 {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a)) :
    crepExactMemLoadByte state memDec =
      fun address =>
        (@panMemLoadByteWord8HOL width _ state.memory state.memaddrs memDec state.be
          address).map UInt8.ofBitVec := by
  funext address
  unfold crepExactMemLoadByte
  exact @panMemLoadByteHOL_eq_word8_projection width _ state.memory state.memaddrs memDec
    state.be address

/-- The `UInt8`-carrier write-bytearray helper is kernel-equal to the exact
    source `word8` helper on the byte list mapped through `UInt8.toBitVec`,
    through `panWriteBytearrayHOL_eq_word8_projection`. -/
theorem crepExactWriteBytearray_eq_word8 {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (address : BitVec width) (bytes : List UInt8) :
    crepExactWriteBytearray state memDec address bytes =
      @panWriteBytearrayWord8HOL width _ address (bytes.map UInt8.toBitVec) state.memory
        state.memaddrs memDec state.be := by
  unfold crepExactWriteBytearray
  exact @panWriteBytearrayHOL_eq_word8_projection width _ address bytes state.memory
    state.memaddrs memDec state.be


/-- Exact port of HOL `Datatype result`
    (`cakeml/pancake/semantics/crepSemScript.sml:36-44`):
    `result = Error | TimeOut | Break num | Continue num
            | Return (('a word_lab) list) | Exception ('a word) | FinalFFI final_event`.
    Unlike the production `CrepResultHOL`, the `Return` payload is the exact
    `HolWordLab width` port of `'a word_lab` (not the production `PanWordLab`),
    and the `Exception` payload is `BitVec width` for `'a word`. The `finalFfi`
    payload is the monomorphic `HolFinalEvent` port of `final_event`. The width
    index is the canonical positive finite-word model, matching the tagged
    `HolWordLab` datatype port (`[NeZero width]` for HOL's positive `dimindex`). -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "result"]
inductive CrepResultHOLExact (width : Nat) [NeZero width] where
  | error
  | timeOut
  | break (label : Nat)
  | continue (label : Nat)
  | return (values : List (HolWordLab width))
  | exception (value : BitVec width)
  | finalFfi (event : HolFinalEvent)
  deriving Repr

/-- Exact port of HOL `exit_loop_def` (`crepSemScript.sml:234-238`):
    `exit_loop (SOME (Break n)) = SOME (Break (n - 1))`,
    `exit_loop (SOME (Continue n)) = SOME (Continue (n - 1))`, and
    `exit_loop res = res`. The carrier
    `Option (CrepResultHOLExact width)` is the exact `crepSem$result option`
    over the genuinely exact width-indexed result datatype port above, whose
    `Return` payload is the exact `HolWordLab` list (matching HOL's
    `('a word_lab) list`). `Nat` subtraction is HOL `num` subtraction. The
    `Return`/`Exception`/`FinalFFI` payloads are never inspected, so no payload
    projection is involved. -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "exit_loop_def"]
def exitLoopCrepResult {width : Nat} [NeZero width] :
    Option (CrepResultHOLExact width) →
      Option (CrepResultHOLExact width)
  | some (.break label) => some (.break (label - 1))
  | some (.continue label) => some (.continue (label - 1))
  | result => result

/-- Total coercion from the exact width-indexed result carrier
    `CrepResultHOLExact` to the production `CrepResultHOL`, transporting the
    `Return` payload through `HolWordLab.toPanWordLab`. Flapjack-specific
    infrastructure: the evaluator returns `CrepResultHOLExact` directly, and this
    bridge is only for callers that still need the production `PanWordLab`
    carrier. -/
def CrepResultHOLExact.toProd {width : Nat} [NeZero width] :
    CrepResultHOLExact width → CrepResultHOL (BitVec width) HolFinalEvent
  | .error => .error
  | .timeOut => .timeOut
  | .break label => .break label
  | .continue label => .continue label
  | .return values => .return (values.map HolWordLab.toPanWordLab)
  | .exception value => .exception value
  | .finalFfi event => .finalFfi event

/-- Total coercion from the production `CrepResultHOL` to the exact width-indexed
    result carrier `CrepResultHOLExact`, transporting the `Return` payload
    through `PanWordLab.toHolWordLab`. Flapjack-specific infrastructure; inverse
    of `CrepResultHOLExact.toProd`. -/
def CrepResultHOL.toExact {width : Nat} [NeZero width] :
    CrepResultHOL (BitVec width) HolFinalEvent → CrepResultHOLExact width
  | .error => .error
  | .timeOut => .timeOut
  | .break label => .break label
  | .continue label => .continue label
  | .return values => .return (values.map PanWordLab.toHolWordLab)
  | .exception value => .exception value
  | .finalFfi event => .finalFfi event

@[simp] theorem List.map_toHolWordLab_toPanWordLab {width : Nat} [NeZero width]
    (values : List (HolWordLab width)) :
    values.map (PanWordLab.toHolWordLab ∘ HolWordLab.toPanWordLab) = values :=
  (List.map_congr_left (fun value _ => HolWordLab.toPanWordLab_toHolWordLab value)).trans
    (List.map_id values)

@[simp] theorem List.map_toPanWordLab_toHolWordLab {width : Nat} [NeZero width]
    (values : List (PanWordLab (BitVec width))) :
    values.map (HolWordLab.toPanWordLab ∘ PanWordLab.toHolWordLab) = values :=
  (List.map_congr_left (fun value _ => PanWordLab.toHolWordLab_toPanWordLab value)).trans
    (List.map_id values)

@[simp] theorem CrepResultHOLExact.toProd_toExact {width : Nat} [NeZero width]
    (result : CrepResultHOLExact width) :
    result.toProd.toExact = result := by
  cases result <;> simp [CrepResultHOLExact.toProd, CrepResultHOL.toExact]

@[simp] theorem CrepResultHOL.toExact_toProd {width : Nat} [NeZero width]
    (result : CrepResultHOL (BitVec width) HolFinalEvent) :
    result.toExact.toProd = result := by
  cases result <;> simp [CrepResultHOLExact.toProd, CrepResultHOL.toExact]

namespace CrepSemShMemExact

/-- Canonical kernel witness for the `fmap_as_finite_support` `@[hol]`
    qualifier used by the tagged `crepSem` shared-memory helpers in this module.
    The finite-map fields of `CrepSemHOLState` are invertibly related to the
    broad function-backed `CrepSemBroadState`; the proof is the imported
    `CrepSemHOLState.holFmapAsFiniteSupportWitness`. The checker requires a
    same-module witness for every `fmap_as_finite_support`-qualified tag. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {ffiState : Type} :
    (∀ (state : CrepSemBroadState width ffiState) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width ffiState,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end CrepSemShMemExact

/-- Exact HOL `sh_mem_load_def` (`crepSemScript.sml:168-184`) over the exact
    finite-support `CrepSemHOLState`, with HOL's *free* byte count `nb` as an
    explicit argument (not fused into an operator): for `nb = 0` the original
    address is checked against `sh_memaddrs`, otherwise the byte-aligned address
    is; in both cases the FFI is called with the original address bytes
    (`word_to_bytes addr F`). A terminal result clears the locals; a returned
    result installs the decoded word (`word_of_bytes F 0w`) into `v` and the new
    FFI state. The `(fmap_as_finite_support := [locals, globals, code])`
    qualifier records that HOL's `|->` fields are represented by
    `HolFiniteMapExact`; the positive-width `BitVec width` model represents HOL's
    nonempty finite word dimension, recorded by the
    `(words_as_type_indexed_bitvec)` qualifier (HOL `'a word` with dimension
    `dimindex (:α)` translated to `BitVec width` with the `[NeZero width]`
    discharge). -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "sh_mem_load_def" (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
def crepShMemLoadExactHOL {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (address : BitVec width) (nb : Nat)
    (state : CrepSemHOLState width σ) [DecidablePred state.shMemaddrs] :
    Option (CrepResultHOLExact width) × CrepSemHOLState width σ :=
  if nb = 0 then
    if state.shMemaddrs address then
      match callFFIHOL state.ffi (.sharedMem .mappedRead)
          [BitVec.ofNat 8 nb]
          ((crepClockWordToBytes address).map UInt8.toBitVec) with
      | .final event => (some (.finalFfi event), CrepSemHOLState.emptyLocals state)
      | .ret newFfi newBytes =>
          (none, { CrepSemHOLState.setVar name
                      (.word (crepClockWordOfBytes (newBytes.map UInt8.ofBitVec)))
                      state with
                    ffi := newFfi })
    else (some .error, state)
  else
    if state.shMemaddrs (panByteAlignHOL address) then
      match callFFIHOL state.ffi (.sharedMem .mappedRead)
          [BitVec.ofNat 8 nb]
          ((crepClockWordToBytes address).map UInt8.toBitVec) with
      | .final event => (some (.finalFfi event), CrepSemHOLState.emptyLocals state)
      | .ret newFfi newBytes =>
          (none, { CrepSemHOLState.setVar name
                      (.word (crepClockWordOfBytes (newBytes.map UInt8.ofBitVec)))
                      state with
                    ffi := newFfi })
    else (some .error, state)

/-- Flapjack-specific operator-indexed specialization of the exact HOL
    `sh_mem_load_def` port: it supplies the byte count from the operator
    (`crepShMemByteWidth`) and threads an explicit domain decision procedure.
    This is the form the `ShMem` evaluator clause calls; it is not itself the
    exact HOL statement because HOL's `nb` is a free argument. -/
def crepShMemLoadHOL {width : Nat} [NeZero width] {σ : Type}
    (operator : CrepMemOp) (name : Nat) (address : BitVec width)
    (state : CrepSemHOLState width σ)
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) :
    Option (CrepResultHOLExact width) × CrepSemHOLState width σ :=
  letI : DecidablePred state.shMemaddrs := shMemDec
  crepShMemLoadExactHOL name address (crepShMemByteWidth operator) state

/-- Exact HOL `sh_mem_store_def` (`crepSemScript.sml:186-208`) over the exact
    finite-support `CrepSemHOLState`, with HOL's free byte count `nb`: the named
    local `v` must hold a word; for `nb = 0` the original address is checked,
    otherwise the byte-aligned address is; the FFI receives
    `word_to_bytes w F ++ word_to_bytes addr F` (or its `TAKE nb` prefix for
    `nb ≠ 0`). A terminal result keeps the state, a returned result installs the
    new FFI state. The `(fmap_as_finite_support := [locals, globals, code])`
    qualifier records the finite-map representation; the
    `(words_as_type_indexed_bitvec)` qualifier records the `'a word` /
    `dimindex (:α)` to `BitVec width` / `[NeZero width]` translation. -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "sh_mem_store_def" (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
def crepShMemStoreExactHOL {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (address : BitVec width) (nb : Nat)
    (state : CrepSemHOLState width σ) [DecidablePred state.shMemaddrs] :
    Option (CrepResultHOLExact width) × CrepSemHOLState width σ :=
  match state.locals.lookup name with
  | some (.word value) =>
      if nb = 0 then
        if state.shMemaddrs address then
          match callFFIHOL state.ffi (.sharedMem .mappedWrite)
              [BitVec.ofNat 8 nb]
              ((crepClockWordToBytes value ++ crepClockWordToBytes address).map
                UInt8.toBitVec) with
          | .final event => (some (.finalFfi event), state)
          | .ret newFfi _ => (none, { state with ffi := newFfi })
        else (some .error, state)
      else
        if state.shMemaddrs (panByteAlignHOL address) then
          match callFFIHOL state.ffi (.sharedMem .mappedWrite)
              [BitVec.ofNat 8 nb]
              (((crepClockWordToBytes value).take nb ++
                crepClockWordToBytes address).map UInt8.toBitVec) with
          | .final event => (some (.finalFfi event), state)
          | .ret newFfi _ => (none, { state with ffi := newFfi })
        else (some .error, state)
  | _ => (some .error, state)

/-- Exact HOL `sh_mem_op_def` (`crepSemScript.sml:210-218`): dispatch the eight
    shared-memory operators to `sh_mem_load`/`sh_mem_store` at the fixed byte
    counts `0` (`Load`/`Store`), `1` (`Load8`/`Store8`), `2`
    (`Load16`/`Store16`) and `4` (`Load32`/`Store32`), clause for clause. The
    `(fmap_as_finite_support := [locals, globals, code])` and
    `(words_as_type_indexed_bitvec)` qualifiers record the finite-map and
    word-dimension translations. -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "sh_mem_op_def" (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
def crepShMemOpExactHOL {width : Nat} [NeZero width] {σ : Type}
    (operator : CrepMemOp) (name : Nat) (address : BitVec width)
    (state : CrepSemHOLState width σ) [DecidablePred state.shMemaddrs] :
    Option (CrepResultHOLExact width) × CrepSemHOLState width σ :=
  match operator with
  | .load => crepShMemLoadExactHOL name address 0 state
  | .store => crepShMemStoreExactHOL name address 0 state
  | .load8 => crepShMemLoadExactHOL name address 1 state
  | .store8 => crepShMemStoreExactHOL name address 1 state
  | .load16 => crepShMemLoadExactHOL name address 2 state
  | .store16 => crepShMemStoreExactHOL name address 2 state
  | .load32 => crepShMemLoadExactHOL name address 4 state
  | .store32 => crepShMemStoreExactHOL name address 4 state

/-- Flapjack-specific operator-indexed specialization of the exact HOL
    `sh_mem_store_def` port: it supplies the byte count from the operator and
    threads an explicit domain decision procedure. This is the form the `ShMem`
    evaluator clause calls; it is not itself the exact HOL statement because
    HOL's `nb` is a free argument. -/
def crepShMemStoreHOL {width : Nat} [NeZero width] {σ : Type}
    (operator : CrepMemOp) (name : Nat) (address : BitVec width)
    (state : CrepSemHOLState width σ)
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) :
    Option (CrepResultHOLExact width) × CrepSemHOLState width σ :=
  letI : DecidablePred state.shMemaddrs := shMemDec
  crepShMemStoreExactHOL name address (crepShMemByteWidth operator) state

/-! ## Clock-invariance helpers

HOL `clock_eq_simp` (`crepSemScript.sml:392-398`) and the shared-memory clock
lemmas `sh_mem_load_clock`/`sh_mem_store_clock`/`sh_mem_op_clock`
(`crepSemScript.sml:400-419`). These are the exact source helper lemmas under
`evaluate_clock`/`fix_clock_evaluate`; they are stated over the exact
`crepShMemLoadExactHOL`/`crepShMemStoreExactHOL`/`crepShMemOpExactHOL` ports
and the tagged `CrepSemHOLState.setVar`/`emptyLocals`/`setGlobals` updates, all
of which leave the `clock` field unchanged. -/

/-- Exact port of HOL `clock_eq_simp` (`crepSemScript.sml:392-398`): the
    `set_var`, `empty_locals` and `set_globals` state updates do not change the
    clock component. The three conjuncts match HOL's `set_var`/`empty_locals`/
    `set_globals` clause order. -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "clock_eq_simp" (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSemClockEqSimp {width : Nat} [NeZero width] {ffiState : Type}
    (name : Nat) (value : HolWordLab width) (key : BitVec 5)
    (state : CrepSemHOLState width ffiState) :
    (CrepSemHOLState.setVar name value state).clock = state.clock ∧
      (CrepSemHOLState.emptyLocals state).clock = state.clock ∧
      (CrepSemHOLState.setGlobals key value state).clock = state.clock := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- Exact port of HOL `sh_mem_load_clock` (`crepSemScript.sml:400-403`):
    `sh_mem_load v addr nb s = (r, s') ⇒ s'.clock = s.clock`. -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "sh_mem_load_clock" (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepShMemLoadClock {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (address : BitVec width) (nb : Nat)
    (state : CrepSemHOLState width σ) [DecidablePred state.shMemaddrs]
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (h : crepShMemLoadExactHOL name address nb state = (r, s')) :
    s'.clock = state.clock := by
  have hs : s' = (crepShMemLoadExactHOL name address nb state).snd := by rw [h]
  subst hs
  simp only [crepShMemLoadExactHOL]
  split <;> (try split) <;> (try split)
  all_goals
    first
    | rfl
    | simp only [CrepSemHOLState.emptyLocals]
    | simp only [CrepSemHOLState.setVar]

/-- Exact port of HOL `sh_mem_store_clock` (`crepSemScript.sml:406-409`):
    `sh_mem_store v addr nb s = (r, s') ⇒ s'.clock = s.clock`. -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "sh_mem_store_clock" (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepShMemStoreClock {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (address : BitVec width) (nb : Nat)
    (state : CrepSemHOLState width σ) [DecidablePred state.shMemaddrs]
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (h : crepShMemStoreExactHOL name address nb state = (r, s')) :
    s'.clock = state.clock := by
  have hs : s' = (crepShMemStoreExactHOL name address nb state).snd := by rw [h]
  subst hs
  simp only [crepShMemStoreExactHOL]
  split <;> (try split) <;> (try split) <;> (try split)
  all_goals
    first
    | rfl
    | simp only [CrepSemHOLState.emptyLocals]
    | simp only [CrepSemHOLState.setVar]

/-- Exact port of HOL `sh_mem_op_clock` (`crepSemScript.sml:412-419`):
    `sh_mem_op op v addr s = (r, s') ⇒ s'.clock = s.clock`, by dispatching on
    the shared-memory operator to the tagged clock lemmas. -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "sh_mem_op_clock" (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepShMemOpClock {width : Nat} [NeZero width] {σ : Type}
    (operator : CrepMemOp) (name : Nat) (address : BitVec width)
    (state : CrepSemHOLState width σ) [DecidablePred state.shMemaddrs]
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (h : crepShMemOpExactHOL operator name address state = (r, s')) :
    s'.clock = state.clock := by
  cases operator <;>
    simp only [crepShMemOpExactHOL] at h <;>
    first
    | exact crepShMemLoadClock name address _ state _ _ h
    | exact crepShMemStoreClock name address _ state _ _ h

/-! ## FFI event-prefix preserved by the exact shared-memory helpers

For the `divergenceChain` obligation of the exact `semantics_def`, the exact
recursive evaluator must only ever extend the FFI event log.  Only the shared
memory (`sh_mem_load`/`sh_mem_store`) and external-call leaves can extend
`ffi.ioEvents` (through `callFFIHOL`); every other clause preserves `ffi`
exactly.  The lemmas below establish the event-prefix property for the exact
shared-memory leaves, mirroring the panSem per-step lemmas in
`Flapjack/Pancake/Semantics/PanSem/FiniteSupportStep.lean` (the analogue of HOL
`evaluate_io_events_mono`).  They are Flapjack-specific infrastructure lemmas
(no `@[hol]` tag); the full evaluator-level chain is tracked by bead
`flapjack-pxn.18.4.8.2`.
-/

/-- The exact HOL `sh_mem_load_def` port only extends the FFI event log. -/
theorem crepShMemLoadExactHOL_ioEvents_prefix {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (address : BitVec width) (nb : Nat)
    (state : CrepSemHOLState width σ) [DecidablePred state.shMemaddrs] :
    state.ffi.ioEvents <+:
      (crepShMemLoadExactHOL name address nb state).2.ffi.ioEvents := by
  unfold crepShMemLoadExactHOL
  split
  · split
    · split
      · exact List.prefix_refl _
      · exact callFFIHOL_return_ioEvents_prefix _ _ _ _ _ _ (by assumption)
    · exact List.prefix_refl _
  · split
    · split
      · exact List.prefix_refl _
      · exact callFFIHOL_return_ioEvents_prefix _ _ _ _ _ _ (by assumption)
    · exact List.prefix_refl _

/-- The exact HOL `sh_mem_store_def` port only extends the FFI event log. -/
theorem crepShMemStoreExactHOL_ioEvents_prefix {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (address : BitVec width) (nb : Nat)
    (state : CrepSemHOLState width σ) [DecidablePred state.shMemaddrs] :
    state.ffi.ioEvents <+:
      (crepShMemStoreExactHOL name address nb state).2.ffi.ioEvents := by
  unfold crepShMemStoreExactHOL
  split
  · split
    · split
      · split
        · exact List.prefix_refl _
        · exact callFFIHOL_return_ioEvents_prefix _ _ _ _ _ _ (by assumption)
      · exact List.prefix_refl _
    · split
      · split
        · exact List.prefix_refl _
        · exact callFFIHOL_return_ioEvents_prefix _ _ _ _ _ _ (by assumption)
      · exact List.prefix_refl _
  · exact List.prefix_refl _

/-- The exact HOL `sh_mem_op_def` dispatch only extends the FFI event log. -/
theorem crepShMemOpExactHOL_ioEvents_prefix {width : Nat} [NeZero width] {σ : Type}
    (operator : CrepMemOp) (name : Nat) (address : BitVec width)
    (state : CrepSemHOLState width σ) [DecidablePred state.shMemaddrs] :
    state.ffi.ioEvents <+:
      (crepShMemOpExactHOL operator name address state).2.ffi.ioEvents := by
  cases operator <;>
    simp only [crepShMemOpExactHOL] <;>
    first
      | exact crepShMemLoadExactHOL_ioEvents_prefix _ _ _ _
      | exact crepShMemStoreExactHOL_ioEvents_prefix _ _ _ _

/-- Operator-indexed exact load specialization only extends the FFI event log. -/
theorem crepShMemLoadHOL_ioEvents_prefix {width : Nat} [NeZero width] {σ : Type}
    (operator : CrepMemOp) (name : Nat) (address : BitVec width)
    (state : CrepSemHOLState width σ)
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) :
    state.ffi.ioEvents <+:
      (crepShMemLoadHOL operator name address state shMemDec).2.ffi.ioEvents := by
  simp only [crepShMemLoadHOL]
  exact crepShMemLoadExactHOL_ioEvents_prefix name address
    (crepShMemByteWidth operator) state

/-- Operator-indexed exact store specialization only extends the FFI event log. -/
theorem crepShMemStoreHOL_ioEvents_prefix {width : Nat} [NeZero width] {σ : Type}
    (operator : CrepMemOp) (name : Nat) (address : BitVec width)
    (state : CrepSemHOLState width σ)
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) :
    state.ffi.ioEvents <+:
      (crepShMemStoreHOL operator name address state shMemDec).2.ffi.ioEvents := by
  simp only [crepShMemStoreHOL]
  exact crepShMemStoreExactHOL_ioEvents_prefix name address
    (crepShMemByteWidth operator) state

/-!
## Carrier-boundary audit for the exact `crepSem$evaluate` port

Declaration-local record (bead `flapjack-4ac.5.16.5.16`) of how each
`crepSem$state` / `result` component of HOL
`cakeml/pancake/semantics/crepSemScript.sml:19-43` is translated and of the
exact residual mismatches that keep `evalCrepSemHOLProg` and its no-decider
twin `evalCrepSemHOLProgExact` untagged.

Component table (`HOL component` -> `Lean component`):

* `locals : varname |-> 'a word_lab` ->
  `locals : HolFiniteMapExact Nat (HolWordLab width)`. `varname = num`
  (`crepLangScript.sml:19`), `word_lab = Word ('a word)`
  (`panSemScript.sml:17`) with `HolWordLab` the `@[hol ... "word_lab"]` port,
  and the `|->` field is the reviewed canonical finite-support translation
  witnessed by `CrepSemHOLState.holFmapAsFiniteSupportWitness`
  (`CrepSem/HOLState.lean:384`). Exact.
* `globals : 5 word |-> 'a word_lab` ->
  `globals : HolFiniteMapExact (BitVec 5) (HolWordLab width)` (HOL `5 word`
  is `BitVec 5`). Exact.
* `code : funname |-> (varname list # 'a crepLang$prog)` ->
  `code : HolFiniteMapExact MlString (List Nat × CrepProgHOL width)`.
  `funname = mlstring` (`crepLangScript.sml:21`) with `MlString` the faithful
  carrier; `CrepProgHOL` is the `@[hol ... "prog"]` port. Exact.
* `memory : 'a word -> 'a word_lab` ->
  `memory : BitVec width → HolWordLab width`. Exact.
* `memaddrs : ('a word) set` and `sh_memaddrs : ('a word) set` ->
  `memaddrs`, `shMemaddrs : BitVec width → Prop`: the standard
  set-as-predicate translation; the classical `DecidablePred` instances are
  supplied explicitly by callers.
* `clock : num` -> `clock : Nat`; `be : bool` -> `be : Bool`. Exact.
* `ffi : 'ffi ffi_state` -> `ffi : HolFfiState σ`: `HolFfiState` is the
  `@[hol ... "ffi_state"]` port (`FfiHOL.lean:115`), built from the tagged
  `HolOracle` / `HolOracleResult` / `HolFfiName` / `HolIoEvent` ports. Exact.
* `base_addr`, `top_addr : 'a word` -> `baseAddr`, `topAddr : BitVec width`.
  Exact.
* `result = Error | TimeOut | Break num | Continue num
   | Return (('a word_lab) list) | Exception ('a word) | FinalFFI final_event`
  -> `CrepResultHOLExact width` (the `@[hol ... "result"]` port), whose
  `Return` payload `List (HolWordLab width)` matches HOL's `('a word_lab) list`
  and whose `FinalFFI` payload is the tagged `HolFinalEvent`. Exact.

Residual mismatches (not carrier-field differences):

1. **Word dimension and universe.** HOL's `'a word` is indexed by a type `'a`,
   whereas the Lean carrier fixes the dimension as the Nat `width` and requires
   `[NeZero width]` (needed by `HolWordLab width`); for the intended widths
   (8/32/64) this is the standard translation, but HOL quantifies over the
   dimension without the nonzero side condition. Likewise `{σ : Type}` pins the
   FFI host type to one universe, whereas HOL's `'ffi` is an arbitrary type
   variable.
2. **No general agreement theorem.** `evalCrepSemHOLProg` re-implements HOL's
   `evaluate` (whose exported rewrite is
   `evaluate_def[allow_rebind,compute] =
   REWRITE_RULE [fix_clock_evaluate] evaluate_def`,
   `crepSemScript.sml:443-444`); clause equations are verified
   declaration-locally, but no theorem yet states agreement with HOL `evaluate`
   for all programs and states.
3. **Legacy `UInt8` helpers** (`crepExactMemStoreByte`, `crepExactMemLoadByte`,
   `crepExactWriteBytearray`) keep the `UInt8` byte carrier used by the runtime
   FFI interface; they are kernel-equal to the exact source `word8` helpers by
   the bridges `crepExactMemStoreByte_eq_word8`,
   `crepExactMemLoadByte_eq_word8` and `crepExactWriteBytearray_eq_word8`
   (from `panMemStoreByteHOL_eq_word8` / `panMemLoadByteHOL_eq_word8_projection`
   / `panWriteBytearrayHOL_eq_word8_projection`, `PanSem/ExtCallExact.lean`),
   so the only residual deviation is the surface byte carrier
   (`UInt8` vs `BitVec 8`), not semantics. (`crepClockWordToBytes` /
   `crepClockWordOfBytes` remain untagged.)
4. **`Call` clause restatement** over the no-decider entry point is landed
   (`evalCrepSemHOLProgExact_call`, bead `flapjack-4ac.5.16.5.17`).

Tracking: tag bead `flapjack-4ac.5.16.5`, finite-map owner/witness placement
`flapjack-4ac.5.16.5.13.1`, this audit `flapjack-4ac.5.16.5.16`.
-/

/-- Total HOL-shaped `crepSem$evaluate` (`crepSemScript.sml:240-390`) by
    constructor recursion on the exact `CrepProgHOL` syntax over the exact
    finite-support `CrepSemHOLState`. The returned pair is
    `(result option, state)`, i.e. `none` is ordinary completion, exactly as in
    HOL. The recursion measure is HOL's `(clock, prog_size)`; no fuel and no
    dependency on `evalCrepRuntimeResult` is used. The two domain-membership
    decision procedures are explicit arguments so that the recursive calls on
    updated states reuse them definitionally.

    Untagged: see the module note for the representation differences. -/
def evalCrepSemHOLProg {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) :
    CrepProgHOL width →
      Option (CrepResultHOLExact width) × CrepSemHOLState width σ
  | .skip => (none, state)
  | .dec name value body =>
      match crepExactEvalExp state memDec value with
      | none => (some .error, state)
      | some value =>
          let boundState : CrepSemHOLState width σ :=
            CrepSemHOLState.setVar name value state
          let old := state.locals.lookup name
          let step := evalCrepSemHOLProg boundState memDec shMemDec body
          (step.1, { step.2 with locals := step.2.locals.resVarEq (name, old) })
  | .primitive names operator args =>
      match args.mapM state.locals.lookup with
      | some ws =>
          match crepPrimopHOLExact operator ws with
          | some results =>
              if names.length = results.length &&
                 names.all (fun v => (state.locals.lookup v).isSome) &&
                 names.Nodup then
                (none, { state with
                  locals := state.locals.updateListEq (names.zip results) })
              else (some .error, state)
          | none => (some .error, state)
      | none => (some .error, state)
  | .assign name src =>
      match crepExactEvalExp state memDec src with
      | none => (some .error, state)
      | some w =>
          match state.locals.lookup name with
          | some _ => (none, CrepSemHOLState.setVar name w state)
          | none => (some .error, state)
  | .store dst src =>
      match crepExactEvalExp state memDec dst,
            crepExactEvalExp state memDec src with
      | some (.word account), some w =>
          match memDec account with
          | .isTrue _ =>
              (none, { state with memory := fun current =>
                if current = account then w else state.memory current })
          | .isFalse _ => (some .error, state)
      | _, _ => (some .error, state)
  | .store32 dst src =>
      match crepExactEvalExp state memDec dst,
            crepExactEvalExp state memDec src with
      | some (.word address), some (.word w) =>
          match crepExactMemStore32 state memDec address (BitVec.ofNat 32 w.toNat) with
          | some memory => (none, { state with memory := memory })
          | none => (some .error, state)
      | _, _ => (some .error, state)
  | .storeByte dst src =>
      match crepExactEvalExp state memDec dst,
            crepExactEvalExp state memDec src with
      | some (.word address), some (.word w) =>
          match crepExactMemStoreByte state memDec address (UInt8.ofNat w.toNat) with
          | some memory => (none, { state with memory := memory })
          | none => (some .error, state)
      | _, _ => (some .error, state)
  | .storeGlob dst src =>
      match crepExactEvalExp state memDec src with
      | some w => (none, CrepSemHOLState.setGlobals dst w state)
      | none => (some .error, state)
  | .seq first second =>
      let step := fixClockCrepSemHOL state
        (evalCrepSemHOLProg state memDec shMemDec first)
      match hstep : step with
      | (none, stepState) =>
          have hclk : stepState.clock ≤ state.clock :=
            fixClockCrepSemHOL_IMP_LESS_EQ state
              (evalCrepSemHOLProg state memDec shMemDec first) none stepState
              (by simpa using hstep)
          evalCrepSemHOLProg (crepStampExactDomains state stepState) memDec shMemDec second
      | (some _, _) => step
  | .ite condition thenBranch elseBranch =>
      match crepExactEvalExp state memDec condition with
      | some (.word w) =>
          if w ≠ 0 then evalCrepSemHOLProg state memDec shMemDec thenBranch
          else evalCrepSemHOLProg state memDec shMemDec elseBranch
      | _ => (some .error, state)
  | .while condition body =>
      match crepExactEvalExp state memDec condition with
      | some (.word w) =>
          if w ≠ 0 then
            if hclock : state.clock = 0 then
              (some .timeOut, CrepSemHOLState.emptyLocals state)
            else
              let decState := decClockCrepSemHOL state
              let fixed := fixClockCrepSemHOL decState
                (evalCrepSemHOLProg decState memDec shMemDec body)
              match hfixed : fixed with
              | (none, loopState) =>
                  have hbound : loopState.clock ≤ decState.clock :=
                    fixClockCrepSemHOL_IMP_LESS_EQ decState
                      (evalCrepSemHOLProg decState memDec shMemDec body) none
                      loopState (by simpa [fixed] using hfixed)
                  have hlt : (crepStampExactDomains state loopState).clock < state.clock := by
                    simp [decState, decClockCrepSemHOL] at hbound
                    exact Nat.lt_of_le_of_lt hbound
                      (Nat.sub_lt (Nat.pos_of_ne_zero hclock) (by omega))
                  evalCrepSemHOLProg (crepStampExactDomains state loopState) memDec shMemDec
                    (.while condition body)
              | (some (.continue 0), loopState) =>
                  have hbound : loopState.clock ≤ decState.clock :=
                    fixClockCrepSemHOL_IMP_LESS_EQ decState
                      (evalCrepSemHOLProg decState memDec shMemDec body)
                      (some (.continue 0)) loopState (by simpa [fixed] using hfixed)
                  have hlt : (crepStampExactDomains state loopState).clock < state.clock := by
                    simp [decState, decClockCrepSemHOL] at hbound
                    exact Nat.lt_of_le_of_lt hbound
                      (Nat.sub_lt (Nat.pos_of_ne_zero hclock) (by omega))
                  evalCrepSemHOLProg (crepStampExactDomains state loopState) memDec shMemDec
                    (.while condition body)
              | (some (.break 0), loopState) => (none, loopState)
              | (result, loopState) => (exitLoopCrepResult result, loopState)
          else (none, state)
      | _ => (some .error, state)
  | .break label => (some (.break label), state)
  | .continue label => (some (.continue label), state)
  | .call returnInfo function arguments =>
      match arguments.mapM (@evalCrepSemHOLExp width ‹NeZero width› σ state memDec) with
      | none => (some .error, state)
      | some values =>
          match state.code.lookup function with
          | none => (some .error, state)
          | some (parameters, body) =>
              if parameters.length = values.length && parameters.Nodup then
                let proceed : Option (CrepResultHOLExact width) ×
                    CrepSemHOLState width σ :=
                  if hclock : state.clock = 0 then
                    (some .timeOut, CrepSemHOLState.emptyLocals state)
                  else
                    let calleeLocals :=
                      HolFiniteMapExact.empty.updateList (parameters.zip values)
                    let callee : CrepSemHOLState width σ :=
                      { state with locals := calleeLocals }
                    let decCallee := decClockCrepSemHOL callee
                    let fixed := fixClockCrepSemHOL decCallee
                      (evalCrepSemHOLProg decCallee memDec shMemDec body)
                    match hfixed : fixed with
                    | (none, bodyState) => (some .error, bodyState)
                    | (some (.break _), bodyState) => (some .error, bodyState)
                    | (some (.continue _), bodyState) => (some .error, bodyState)
                    | (some (.return retvs), bodyState) =>
                        match returnInfo with
                        | none => (some (.return retvs),
                            CrepSemHOLState.emptyLocals bodyState)
                        | some (rts, _) =>
                            if retvs.length ≠ rts.length then
                              (some .error, bodyState)
                            else
                              match rts.mapM state.locals.lookup with
                              | some _ => (none, { bodyState with
                                  locals := state.locals.updateListEq
                                    (rts.zip retvs) })
                              | none => (some .error, bodyState)
                    | (some (.exception eid), bodyState) =>
                        match returnInfo with
                        | none => (some (.exception eid),
                            CrepSemHOLState.emptyLocals bodyState)
                        | some (_, none) => (some (.exception eid),
                            CrepSemHOLState.emptyLocals bodyState)
                        | some (_, some (eid', handlerBody)) =>
                            let handlerState : CrepSemHOLState width σ :=
                              crepStampExactDomains state
                                { bodyState with locals := state.locals }
                            have hbound : bodyState.clock ≤ decCallee.clock :=
                              fixClockCrepSemHOL_IMP_LESS_EQ decCallee
                                (evalCrepSemHOLProg decCallee memDec shMemDec body)
                                (some (.exception eid)) bodyState
                                (by simpa [fixed] using hfixed)
                            have hlt : bodyState.clock < state.clock := by
                              simp [decCallee, callee, decClockCrepSemHOL] at hbound ⊢
                              omega
                            if eid = eid' then
                              evalCrepSemHOLProg handlerState memDec shMemDec handlerBody
                            else (some (.exception eid),
                              CrepSemHOLState.emptyLocals bodyState)
                    | (some result, bodyState) =>
                        (some result, CrepSemHOLState.emptyLocals bodyState)
                match returnInfo with
                | some (rts, _) => if rts.Nodup then proceed else (some .error, state)
                | none => proceed
              else (some .error, state)
  | .extCall function configuration configurationLength array arrayLength =>
      match state.locals.lookup configurationLength, state.locals.lookup configuration,
            state.locals.lookup arrayLength, state.locals.lookup array with
      | some (.word configLength), some (.word configAddress),
        some (.word arrayLengthValue), some (.word arrayAddress) =>
          match readBytearrayWordHOL (byteWidth := 8) configAddress configLength.toNat
                  (crepExactMemLoadByteWord8 state memDec),
                readBytearrayWordHOL (byteWidth := 8) arrayAddress arrayLengthValue.toNat
                  (crepExactMemLoadByteWord8 state memDec) with
          | some configBytes, some arrayBytes =>
              match callFFIHOL state.ffi (.extCall function)
                  configBytes arrayBytes with
              | .final event => (some (.finalFfi event), state)
              | .ret newFfi newBytes =>
                  (none, { state with
                    memory := crepExactWriteBytearrayWord8 state memDec arrayAddress
                      newBytes,
                    ffi := newFfi })
          | _, _ => (some .error, state)
      | _, _, _, _ => (some .error, state)
  | .raise exception =>
      (some (.exception exception), CrepSemHOLState.emptyLocals state)
  | .return values =>
      match values.mapM (@evalCrepSemHOLExp width ‹NeZero width› σ state memDec) with
      | some ws => (some (.return ws),
          CrepSemHOLState.emptyLocals state)
      | none => (some .error, state)
  | .shMem operator name address =>
      match crepExactEvalExp state memDec address with
      | some (.word addressValue) =>
          if crepIsLoadMemOp operator then
            match state.locals.lookup name with
            | some _ => crepShMemLoadHOL operator name addressValue state shMemDec
            | none => (some .error, state)
          else
            match state.locals.lookup name with
            | some (.word _) =>
                crepShMemStoreHOL operator name addressValue state shMemDec
            | _ => (some .error, state)
      | _ => (some .error, state)
  | .tick =>
      if state.clock = 0 then (some .timeOut, CrepSemHOLState.emptyLocals state)
      else (none, decClockCrepSemHOL state)
termination_by program => (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    first
    | decreasing_trivial
    | (simp only [Prod.lex_def, decClockCrepSemHOL,
        CrepSemHOLState.setVar] at *
       try simp only [true_and] at *
       omega)

/-- A public no-extra-decision-argument entry point for the finite-support
    evaluator. Classical decidability supplies the two domain tests required by
    the Lean recursive core; the proof-side behavior is independent of which
    decision procedures are chosen, as `evalCrepSemHOLProgExact_eq_core`
    records. This removes the explicit `memDec`/`shMemDec` arguments from the
    evaluator interface, but is not tagged as HOL `evaluate_def`: the full
    clause/carrier audit remains incomplete. -/
noncomputable def evalCrepSemHOLProgExact {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (program : CrepProgHOL width) :
    Option (CrepResultHOLExact width) × CrepSemHOLState width σ := by
  classical
  exact evalCrepSemHOLProg state
    (fun a => (inferInstance : Decidable (state.memaddrs a)))
    (fun a => (inferInstance : Decidable (state.shMemaddrs a))) program

/-- The no-extra-argument entry point agrees with the recursive core for any
    domain deciders. This kernel-checked equation makes its classical choice
    invisible in the evaluator result. -/
theorem evalCrepSemHOLProgExact_eq_core {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (program : CrepProgHOL width)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) :
    evalCrepSemHOLProgExact state program =
      evalCrepSemHOLProg state memDec shMemDec program := by
  classical
  have hmem : (fun a => Classical.propDecidable (state.memaddrs a)) = memDec := by
    funext address
    exact Subsingleton.elim _ _
  have hshMem : (fun a => Classical.propDecidable (state.shMemaddrs a)) = shMemDec := by
    funext address
    exact Subsingleton.elim _ _
  unfold evalCrepSemHOLProgExact
  congr 1

/-- Flapjack-only `Skip` equation matching the first conjunct of HOL's
    rewritten `evaluate_def` (`cakeml/pancake/semantics/crepSemScript.sml:443`,
    originating at line 241): `evaluate (Skip, s) = (NONE, s)`. Over the
    Flapjack total evaluator `evalCrepSemHOLProgExact`, evaluating `Skip`
    returns the state unchanged. This declaration is deliberately untagged:
    its local constructor equation is checked, but no source-reviewed theorem
    yet establishes that `evalCrepSemHOLProgExact` agrees with HOL `evaluate`
    across every constructor, including the FFI cases. The map and word
    qualifiers describe its carrier translations; they do not supply that
    evaluator-agreement result. Keep this useful local equation as
    Flapjack-specific infrastructure until that full evaluator gap is closed. -/
theorem evalCrepSemHOLProgExact_skip {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    evalCrepSemHOLProgExact state (.skip : CrepProgHOL width) = (none, state) := by
  calc
    evalCrepSemHOLProgExact state (.skip : CrepProgHOL width) =
        evalCrepSemHOLProg state
          (fun a => Classical.propDecidable (state.memaddrs a))
          (fun a => Classical.propDecidable (state.shMemaddrs a)) .skip :=
      evalCrepSemHOLProgExact_eq_core state .skip _ _
    _ = (none, state) := by simp [evalCrepSemHOLProg]

/-- Kernel-checked `Skip` constructor equation of the total HOL-shaped
    evaluator, matching HOL `crepSemScript.sml:241`
    `evaluate (Skip, s) = (NONE, s)`. -/
@[simp] theorem evalCrepSemHOLProg_skip {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) :
    evalCrepSemHOLProg state memDec shMemDec (.skip : CrepProgHOL width) =
      (none, state) := by
  simp [evalCrepSemHOLProg]

/-! ## Named constructor equations

These are UNTAGGED infrastructure: each theorem is a named, kernel-checked
equation for one `CrepProgHOL` constructor of `evalCrepSemHOLProg`, matching
the corresponding HOL `crepSemScript.sml:evaluate_def` clause (lines 240-390) as
closely as the Lean definition allows. The carrier is the finite-support
`CrepSemHOLState`; the raw `CrepHolState` is not used. No `@[hol]` tag is
attached. -/

/-- HOL `evaluate (Dec v e prog, s)` (`crepSemScript.sml:242-249`), source-reviewed
    as one clause only. `crepExactEvalExp` delegates to the tagged
    `eval_def` port (`crepSemScript.sml:90-137`): a failed initializer returns
    `(SOME Error, s)` unchanged. On success, tagged `set_var_def`
    (`crepSemScript.sml:55-57`) inserts `(v, value)` before recursively
    evaluating the body. The result state then uses tagged `res_var_def`
    (`crepSemScript.sml:163-167`) with the *pre-state*
    `FLOOKUP s.locals v`: `resVarEq` removes the newly bound key when the old
    lookup was `NONE`, or restores the old value when it was `SOME old`. Its
    `HolFiniteMapExact` lookup equations reduce to `FDOMSUB_HOL` and
    `FUPDATE_HOL`, so the finite-support representation preserves both cases.
    `name : Nat` matches HOL `varname = num`; only locals change, while the
    body's result and other post-state fields are forwarded. Direct HOL rows
    `dec_new_local_eval`, `dec_shadow_eval`, and `dec_error_eval` are tracked
    in `CrepSemTotalEvaluateHOLParity`. This is a local Dec-clause review; the
    enclosing evaluator remains untagged pending other clauses and whole-
    statement/carrier review. -/
@[simp] theorem evalCrepSemHOLProg_dec {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (name : Nat) (value : CrepExpHOL width) (body : CrepProgHOL width) :
    evalCrepSemHOLProg state memDec shMemDec (.dec name value body) =
      (match crepExactEvalExp state memDec value with
       | none => (some .error, state)
       | some v =>
           let boundState := CrepSemHOLState.setVar name v state
           let old := state.locals.lookup name
           let step := evalCrepSemHOLProg boundState memDec shMemDec body
           (step.1, { step.2 with locals := step.2.locals.resVarEq (name, old) })) := by
  rw [evalCrepSemHOLProg.eq_def] <;> rfl

/-- HOL `evaluate (Assign v src, s)` (`crepSemScript.sml:257-262`),
    source-reviewed as one clause only. `crepExactEvalExp state memDec src`
    delegates to the tagged exact `evalCrepSemHOLExp` port of `eval_def`
    (`crepSemScript.sml:90-137`); `memDec` supplies Lean's decidability
    evidence and does not change the evaluator's result. On `NONE`, this clause
    returns `Error` and the original state. On `SOME w`, it requires
    `state.locals.lookup name` to be defined, then `setVar` performs HOL's
    `set_var_def` update (`crepSemScript.sml:55-57`) with `FUPDATE` / `|+`;
    an absent local returns `Error` and leaves state unchanged. `name : Nat`
    matches HOL `varname = num`, values use the one-constructor `HolWordLab`
    `word_lab` carrier, and the state maps use the reviewed finite-support
    translation. This supports an exact Assign-clause disposition only; the
    enclosing evaluator remains untagged pending all other cases and whole-
    statement review. -/
@[simp] theorem evalCrepSemHOLProg_assign {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (name : Nat) (src : CrepExpHOL width) :
    evalCrepSemHOLProg state memDec shMemDec (.assign name src) =
      (match crepExactEvalExp state memDec src with
       | none => (some .error, state)
       | some w =>
           match state.locals.lookup name with
           | some _ => (none, CrepSemHOLState.setVar name w state)
           | none => (some .error, state)) := by
  rw [evalCrepSemHOLProg.eq_def] <;> rfl

/-- HOL `evaluate (Primitive lhss pop rhss, s)` (`crepSemScript.sml:250-262`),
    source-reviewed as a single clause, not as a whole-evaluator port. The
    `args.mapM state.locals.lookup` branch is HOL's `OPT_MMAP (FLOOKUP
    s.locals) rhss`; `crepPrimopHOLExact` is the cited `crep_primop_def`; and the
    success guard translates `LENGTH` equality, `EVERY IS_SOME`, and
    `ALL_DISTINCT` before applying the locals `|++ ZIP` update via
    `updateListEq`. Each failure returns `Error` with the original state.

    The state carrier's keys are `Nat` like HOL `varname`; its locals map uses
    `HolFiniteMapExact` with HOL equality/update helpers. HOL `word_lab` has
    only `Word word`, represented by `HolWordLab`; this clause calls the exact
    `crepPrimopHOLExact` directly with no carrier conversion, and the
    `BitVec width`/`[NeZero width]` carrier supplies the positive-width word
    parameter. This review covers only the Primitive equation. The enclosing
    evaluator remains untagged pending the other clauses and whole-statement
    review. -/
@[simp] theorem evalCrepSemHOLProg_primitive {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (names : List Nat) (operator : PrimOp) (args : List Nat) :
    evalCrepSemHOLProg state memDec shMemDec (.primitive names operator args) =
      (match args.mapM state.locals.lookup with
       | some ws =>
           match crepPrimopHOLExact operator ws with
           | some results =>
               if names.length = results.length &&
                  names.all (fun v => (state.locals.lookup v).isSome) &&
                  names.Nodup then
                 (none, { state with
                   locals := state.locals.updateListEq
                     (names.zip results) })
               else (some .error, state)
           | none => (some .error, state)
       | none => (some .error, state)) := by
  rw [evalCrepSemHOLProg.eq_def] <;> rfl

/-- HOL `evaluate (Store dst src, s)` (`crepSemScript.sml:263-269`),
    source-reviewed as one clause only. Both expressions use the tagged exact
    `eval_def` port `evalCrepSemHOLExp` (`crepSemScript.sml:90-137`), through
    `crepExactEvalExp`; its explicit `memDec` is Lean decidability evidence.
    HOL accepts only a `Word` address but any `word_lab` source value, exactly
    the patterns below. `memDec account` is HOL's `account IN s.memaddrs` test.
    Success updates only memory at that address and returns `NONE`; failure of
    either expression or the domain check returns `Error` with the original
    state. The pointwise memory function in this equation is HOL's `addr =+ w`
    update from `mem_store_def` (`panSemScript.sml:373-378`), also implemented
    by the tagged `panMemStoreHOL` helper in `PanSemStateEval.lean`. The state
    uses the reviewed positive-width `BitVec` / `HolWordLab` carriers. This
    establishes a local Store-clause disposition only; the enclosing evaluator
    remains untagged pending the other cases and whole-statement review. -/
@[simp] theorem evalCrepSemHOLProg_store {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (dst src : CrepExpHOL width) :
    evalCrepSemHOLProg state memDec shMemDec (.store dst src) =
      (match crepExactEvalExp state memDec dst,
             crepExactEvalExp state memDec src with
       | some (.word account), some w =>
           match memDec account with
           | .isTrue _ =>
               (none, { state with memory := fun current =>
                 if current = account then w else state.memory current })
           | .isFalse _ => (some .error, state)
       | _, _ => (some .error, state)) := by
  rw [evalCrepSemHOLProg.eq_def] <;> rfl

/-- HOL `evaluate (Store32 dst src, s)` (`crepSemScript.sml:274-280`),
    source-reviewed as one clause only. Both operands use the tagged exact
    `eval_def` port `evalCrepSemHOLExp` (`crepSemScript.sml:90-137`) through
    `crepExactEvalExp`; HOL and Lean both require each result to be a `Word`.
    Converting the source payload with `BitVec.ofNat 32 w.toNat` is HOL's
    `w2w w` to `word32`. `crepExactMemStore32` delegates to the tagged exact
    `mem_store_32_def` port `panMemStore32HOL` (`panSemScript.sml:327-342`):
    alignment, aligned-cell lookup, domain membership at `byte_align`, and the
    four endian-aware byte replacements match. On success only memory changes
    and the result is `NONE`; failed operands or store conditions return
    `Error` with the original state. This is only a local Store32-clause
    disposition; the enclosing evaluator remains untagged pending other cases
    and whole-statement/carrier review. -/
@[simp] theorem evalCrepSemHOLProg_store32 {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (dst src : CrepExpHOL width) :
    evalCrepSemHOLProg state memDec shMemDec (.store32 dst src) =
      (match crepExactEvalExp state memDec dst,
             crepExactEvalExp state memDec src with
       | some (.word address), some (.word w) =>
           match crepExactMemStore32 state memDec address (BitVec.ofNat 32 w.toNat) with
           | some memory => (none, { state with memory := memory })
           | none => (some .error, state)
       | _, _ => (some .error, state)) := by
  rw [evalCrepSemHOLProg.eq_def] <;> rfl

/-- HOL `evaluate (StoreByte dst src, s)` (`crepSemScript.sml:281-287`),
    source-reviewed as one clause only. Both operands use the tagged exact
    `eval_def` port `evalCrepSemHOLExp` (`crepSemScript.sml:90-137`), and both
    must return `Word`. `UInt8.ofNat w.toNat` is the projection of HOL's
    `w2w w` to word8: after `UInt8.toBitVec`, it is the same `BitVec 8` value.
    The untagged UInt8 helper `panMemStoreByteHOL` used by
    `crepExactMemStoreByte` is kernel-proved equal over the complete memory map
    to the exact tagged `panMemStoreByteWord8HOL` by
    `panMemStoreByteHOL_eq_word8` (`PanSem/ExtCallExact.lean`). The exact helper
    implements `mem_store_byte_def` (`panSemScript.sml:300-307`): read the
    aligned cell, require that aligned address in the domain, then replace that
    cell with the endian-aware `set_byte` result. Success changes only memory
    and returns `NONE`; expression/store failure yields `Error` with the
    original state. This is a local StoreByte disposition only; the enclosing
    evaluator remains untagged pending other cases and whole-statement review. -/
@[simp] theorem evalCrepSemHOLProg_storeByte {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (dst src : CrepExpHOL width) :
    evalCrepSemHOLProg state memDec shMemDec (.storeByte dst src) =
      (match crepExactEvalExp state memDec dst,
             crepExactEvalExp state memDec src with
       | some (.word address), some (.word w) =>
           match crepExactMemStoreByte state memDec address (UInt8.ofNat w.toNat) with
           | some memory => (none, { state with memory := memory })
           | none => (some .error, state)
       | _, _ => (some .error, state)) := by
  rw [evalCrepSemHOLProg.eq_def] <;> rfl

/-- HOL `evaluate (StoreGlob dst src, s)` (`crepSemScript.sml:288-291`),
    source-reviewed as one clause only. The source expression is evaluated by
    the tagged exact `eval_def` port `evalCrepSemHOLExp`
    (`crepSemScript.sml:90-137`) through `crepExactEvalExp`. HOL accepts any
    `word_lab` result and unconditionally updates `globals`; the Lean branch
    likewise has no prior-key-membership guard. `setGlobals` is the tagged
    `set_globals_def` port (`crepSemScript.sml:61-63`) using HOL-equality
    `FUPDATE` on the finite-support map, so an absent key is inserted. The
    destination is `BitVec 5`, matching HOL's fixed `5 word` global key, and
    values use `HolWordLab`. A failed expression returns `Error` and the
    original state; success changes only globals and returns `NONE`. This is
    a local StoreGlob disposition only; the enclosing evaluator remains
    untagged pending other cases and whole-statement review. -/
@[simp] theorem evalCrepSemHOLProg_storeGlob {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (dst : BitVec 5) (src : CrepExpHOL width) :
    evalCrepSemHOLProg state memDec shMemDec (.storeGlob dst src) =
      (match crepExactEvalExp state memDec src with
       | some w => (none, CrepSemHOLState.setGlobals dst w state)
       | none => (some .error, state)) := by
  rw [evalCrepSemHOLProg.eq_def] <;> rfl

/-- HOL `evaluate (Seq c1 c2, s)` (`crepSemScript.sml:300-303`): run `c1` under
    `fix_clock`; ordinary completion (`NONE`) runs `c2` on the clamped state,
    any terminal result is propagated. Finite-support `CrepSemHOLState`
    counterpart; untagged. -/
@[simp] theorem evalCrepSemHOLProg_seq {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (first second : CrepProgHOL width) :
    evalCrepSemHOLProg state memDec shMemDec (.seq first second) =
      (let step := fixClockCrepSemHOL state
         (evalCrepSemHOLProg state memDec shMemDec first)
       match _hstep : step with
       | (none, stepState) =>
           evalCrepSemHOLProg (crepStampExactDomains state stepState) memDec shMemDec second
       | (some _, _) => step) := by
  rw [evalCrepSemHOLProg.eq_def] <;> rfl

/-- HOL `evaluate (If e c1 c2, s)` (`crepSemScript.sml:304-308`): `Word 0` is
    false, every other `Word` is true. Finite-support `CrepSemHOLState`
    counterpart; untagged. -/
@[simp] theorem evalCrepSemHOLProg_ite {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (condition : CrepExpHOL width) (thenBranch elseBranch : CrepProgHOL width) :
    evalCrepSemHOLProg state memDec shMemDec (.ite condition thenBranch elseBranch) =
      (match crepExactEvalExp state memDec condition with
       | some (.word w) =>
           if w ≠ 0 then evalCrepSemHOLProg state memDec shMemDec thenBranch
           else evalCrepSemHOLProg state memDec shMemDec elseBranch
       | _ => (some .error, state)) := by
  rw [evalCrepSemHOLProg.eq_def] <;> rfl

/-- HOL `If` true branch: a nonzero `Word` condition evaluates the then-branch. -/
theorem evalCrepSemHOLProg_ite_true {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (condition : CrepExpHOL width) (thenBranch elseBranch : CrepProgHOL width)
    (w : BitVec width)
    (hcondition : crepExactEvalExp state memDec condition = some (.word w))
    (hw : w ≠ 0) :
    evalCrepSemHOLProg state memDec shMemDec (.ite condition thenBranch elseBranch) =
      evalCrepSemHOLProg state memDec shMemDec thenBranch := by
  rw [evalCrepSemHOLProg_ite, hcondition]
  exact if_pos hw

/-- HOL `If` false branch: a zero `Word` condition evaluates the else-branch. -/
theorem evalCrepSemHOLProg_ite_false {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (condition : CrepExpHOL width) (thenBranch elseBranch : CrepProgHOL width)
    (w : BitVec width)
    (hcondition : crepExactEvalExp state memDec condition = some (.word w))
    (hw : w = 0) :
    evalCrepSemHOLProg state memDec shMemDec (.ite condition thenBranch elseBranch) =
      evalCrepSemHOLProg state memDec shMemDec elseBranch := by
  rw [evalCrepSemHOLProg_ite, hcondition]
  exact if_neg (by simp [hw])

/-- HOL `evaluate (While e c, s)` (`crepSemScript.sml:311-323`): the loop-control
    `Continue 0`/`NONE` recurse on the clamped `dec_clock` state, `Break 0`
    completes, and other results pass through `exit_loop`. Finite-support
    `CrepSemHOLState` counterpart; untagged. -/
@[simp] theorem evalCrepSemHOLProg_while {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (condition : CrepExpHOL width) (body : CrepProgHOL width) :
    evalCrepSemHOLProg state memDec shMemDec (.while condition body) =
      (match crepExactEvalExp state memDec condition with
       | some (.word w) =>
           if w ≠ 0 then
             if _hclock : state.clock = 0 then
               (some .timeOut, CrepSemHOLState.emptyLocals state)
             else
               let decState := decClockCrepSemHOL state
               let fixed := fixClockCrepSemHOL decState
                 (evalCrepSemHOLProg decState memDec shMemDec body)
               match _hfixed : fixed with
               | (none, loopState) =>
                   evalCrepSemHOLProg (crepStampExactDomains state loopState) memDec shMemDec
                     (.while condition body)
               | (some (.continue 0), loopState) =>
                   evalCrepSemHOLProg (crepStampExactDomains state loopState) memDec shMemDec
                     (.while condition body)
               | (some (.break 0), loopState) => (none, loopState)
               | (result, loopState) => (exitLoopCrepResult result, loopState)
           else (none, state)
       | _ => (some .error, state)) := by
  rw [evalCrepSemHOLProg.eq_def] <;> rfl

/-- HOL `While` with a zero condition: the loop completes with `(NONE, s)`. -/
theorem evalCrepSemHOLProg_while_false {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (condition : CrepExpHOL width) (body : CrepProgHOL width) (w : BitVec width)
    (hcondition : crepExactEvalExp state memDec condition = some (.word w))
    (hw : w = 0) :
    evalCrepSemHOLProg state memDec shMemDec (.while condition body) = (none, state) := by
  rw [evalCrepSemHOLProg_while, hcondition]
  exact if_neg (by simp [hw])

/-- HOL `While` clock exhaustion (`s.clock = 0` with a nonzero condition):
    `(SOME TimeOut, empty_locals s)`. -/
theorem evalCrepSemHOLProg_while_timeout {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (condition : CrepExpHOL width) (body : CrepProgHOL width) (w : BitVec width)
    (hcondition : crepExactEvalExp state memDec condition = some (.word w))
    (hw : w ≠ 0) (hclock : state.clock = 0) :
    evalCrepSemHOLProg state memDec shMemDec (.while condition body) =
      (some .timeOut, CrepSemHOLState.emptyLocals state) := by
  rw [evalCrepSemHOLProg_while, hcondition]
  exact (if_pos hw).trans (dif_pos hclock)

/-- HOL `evaluate (Break n, s)` (`crepSemScript.sml:309`). -/
@[simp] theorem evalCrepSemHOLProg_break {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (label : Nat) :
    evalCrepSemHOLProg state memDec shMemDec (.break label : CrepProgHOL width) =
      (some (.break label), state) := by
  rw [evalCrepSemHOLProg.eq_def] <;> rfl

/-- HOL `evaluate (Continue n, s)` (`crepSemScript.sml:310`). -/
@[simp] theorem evalCrepSemHOLProg_continue {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (label : Nat) :
    evalCrepSemHOLProg state memDec shMemDec (.continue label : CrepProgHOL width) =
      (some (.continue label), state) := by
  rw [evalCrepSemHOLProg.eq_def] <;> rfl

/-- HOL `evaluate (Raise eid, s)` (`crepSemScript.sml:326`): raise propagates the
    exception and clears the locals. -/
@[simp] theorem evalCrepSemHOLProg_raise {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (exception : BitVec width) :
    evalCrepSemHOLProg state memDec shMemDec (.raise exception) =
      (some (.exception exception), CrepSemHOLState.emptyLocals state) := by
  rw [evalCrepSemHOLProg.eq_def] <;> rfl

/-- HOL `evaluate (Return es, s)` (`crepSemScript.sml:324-325`): evaluate every
    expression into `word_lab` values and clear the locals. -/
@[simp] theorem evalCrepSemHOLProg_return {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (values : List (CrepExpHOL width)) :
    evalCrepSemHOLProg state memDec shMemDec (.return values) =
      (match values.mapM (@evalCrepSemHOLExp width ‹NeZero width› σ state memDec) with
       | some ws => (some (.return ws),
           CrepSemHOLState.emptyLocals state)
       | none => (some .error, state)) := by
  rw [evalCrepSemHOLProg.eq_def] <;> rfl

/-- HOL `evaluate (ShMem op v ad, s)` (`crepSemScript.sml:292-303`),
    source-reviewed as one clause only. The address uses the tagged exact
    `eval_def` port `evalCrepSemHOLExp` (`crepSemScript.sml:90-137`) and both
    HOL and Lean require a `Word` result. `CrepMemOp` is the width-independent
    eight-constructor mirror of `asm$memop` used by the HOL Crep/loop syntax.
    `crepIsLoadMemOp`'s four load cases and four false cases reproduce HOL
    `is_load_def` (`cakeml/pancake/loop_callScript.sml:10-15`). Loads require
    the named local to exist; stores require it to contain a word. Since
    `HolWordLab` is the
    one-constructor `word_lab = Word word` carrier, both local guards match
    HOL's `FLOOKUP` patterns.

    The load/store adapters dispatch each of the eight `CrepMemOp` constructors
    with the same byte count as tagged `crepShMemOpExactHOL` for HOL
    `sh_mem_op_def` (`crepSemScript.sml:210-218`): `Load`/`Store` 0, `8` 1,
    `16` 2, `32` 4. They delegate to the tagged exact `sh_mem_load_def` and
    `sh_mem_store_def` helpers. Outer address/local failures return `Error`
    with the original state; helper results and post-states are forwarded,
    including FFI final/return effects. This is a local ShMem-clause review;
    the enclosing evaluator remains untagged pending all other cases and
    whole-statement/carrier review. -/
@[simp] theorem evalCrepSemHOLProg_shMem {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (operator : CrepMemOp) (name : Nat) (address : CrepExpHOL width) :
    evalCrepSemHOLProg state memDec shMemDec (.shMem operator name address) =
      (match crepExactEvalExp state memDec address with
       | some (.word addressValue) =>
           if crepIsLoadMemOp operator then
             match state.locals.lookup name with
             | some _ => crepShMemLoadHOL operator name addressValue state shMemDec
             | none => (some .error, state)
           else
             match state.locals.lookup name with
             | some (.word _) =>
                 crepShMemStoreHOL operator name addressValue state shMemDec
             | _ => (some .error, state)
       | _ => (some .error, state)) := by
  rw [evalCrepSemHOLProg.eq_def] <;> rfl

/-- HOL `evaluate (ExtCall ffi_index ptr1 len1 ptr2 len2, s)`
    (`crepSemScript.sml:367-379`): read both byte arrays in
    `(len1,ptr1,len2,ptr2)` lookup order, dispatch `call_FFI (ExtCall ffi_index)`,
    preserve the input state on final/error, and on return write the returned
    bytes at `ptr2` and install the new FFI state. The branch uses exact
    `BitVec 8` byte helpers matching HOL `word8`. It remains untagged because
    this core evaluator exposes explicit domain-decision arguments and the
    whole evaluator clause/carrier audit is tracked by
    `flapjack-4ac.5.16.5.2`. The public no-extra-argument wrapper and its core
    equality are `evalCrepSemHOLProgExact` and `evalCrepSemHOLProgExact_eq_core`
    (`flapjack-4ac.5.16.5.2`). -/
@[simp] theorem evalCrepSemHOLProg_extCall {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (function : MlString) (configuration configurationLength array arrayLength : Nat) :
    evalCrepSemHOLProg state memDec shMemDec
        (.extCall function configuration configurationLength array arrayLength) =
      (match state.locals.lookup configurationLength, state.locals.lookup configuration,
             state.locals.lookup arrayLength, state.locals.lookup array with
       | some (.word configLength), some (.word configAddress),
         some (.word arrayLengthValue), some (.word arrayAddress) =>
           match readBytearrayWordHOL (byteWidth := 8) configAddress configLength.toNat
                   (crepExactMemLoadByteWord8 state memDec),
                 readBytearrayWordHOL (byteWidth := 8) arrayAddress arrayLengthValue.toNat
                   (crepExactMemLoadByteWord8 state memDec) with
           | some configBytes, some arrayBytes =>
               match callFFIHOL state.ffi (.extCall function)
                   configBytes arrayBytes with
               | .final event => (some (.finalFfi event), state)
               | .ret newFfi newBytes =>
                   (none, { state with
                     memory := crepExactWriteBytearrayWord8 state memDec arrayAddress
                       newBytes,
                     ffi := newFfi })
           | _, _ => (some .error, state)
       | _, _, _, _ => (some .error, state)) := by
  rw [evalCrepSemHOLProg.eq_def] <;> rfl

/-- HOL `evaluate (Tick, s)` (`crepSemScript.sml:327-329`): decrement the clock,
    or time out at zero with cleared locals. -/
@[simp] theorem evalCrepSemHOLProg_tick {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) :
    evalCrepSemHOLProg state memDec shMemDec (.tick : CrepProgHOL width) =
      (if state.clock = 0 then (some .timeOut, CrepSemHOLState.emptyLocals state)
       else (none, decClockCrepSemHOL state)) := by
  rw [evalCrepSemHOLProg.eq_def] <;> rfl

/-! ## FFI preservation for the non-recursive exact clauses

The exact evaluator clauses for `Skip`, `Assign`, `Primitive`, `Store`,
`Store32`, `StoreByte`, `StoreGlob`, `Break`, `Continue`, `Raise`, `Return` and
`Tick` never touch `state.ffi`, so each returns a pair whose `.ffi` field is
`state.ffi` (hence whose `ioEvents` is unchanged).  Only the shared-memory and
external-call leaves append events.  These equations are the base cases of the
clock-indexed event-prefix chain (HOL `crepPropsScript.sml:1020`
`evaluate_add_clock_io_events_mono`) tracked by `flapjack-pxn.18.4.8.2`.
`Dec` is recursive (it runs its body) and is handled separately. -/

@[simp] theorem evalCrepSemHOLProg_skip_ffi {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) :
    (evalCrepSemHOLProg state memDec shMemDec (.skip : CrepProgHOL width)).2.ffi = state.ffi := by
  simp

@[simp] theorem evalCrepSemHOLProg_assign_ffi {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (name : Nat) (src : CrepExpHOL width) :
    (evalCrepSemHOLProg state memDec shMemDec (.assign name src)).2.ffi = state.ffi := by
  rw [evalCrepSemHOLProg_assign]
  split
  · rfl
  · split <;> rfl

@[simp] theorem evalCrepSemHOLProg_primitive_ffi {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (names : List Nat) (operator : PrimOp) (args : List Nat) :
    (evalCrepSemHOLProg state memDec shMemDec (.primitive names operator args)).2.ffi =
      state.ffi := by
  rw [evalCrepSemHOLProg_primitive]
  split <;> try rfl
  all_goals split <;> try rfl
  all_goals split <;> rfl

@[simp] theorem evalCrepSemHOLProg_store_ffi {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (dst src : CrepExpHOL width) :
    (evalCrepSemHOLProg state memDec shMemDec (.store dst src)).2.ffi = state.ffi := by
  rw [evalCrepSemHOLProg_store]
  split <;> try rfl
  all_goals split <;> try rfl
  all_goals split <;> try rfl

@[simp] theorem evalCrepSemHOLProg_store32_ffi {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (dst src : CrepExpHOL width) :
    (evalCrepSemHOLProg state memDec shMemDec (.store32 dst src)).2.ffi = state.ffi := by
  rw [evalCrepSemHOLProg_store32]
  split <;> try rfl
  all_goals split <;> try rfl
  all_goals split <;> try rfl

@[simp] theorem evalCrepSemHOLProg_storeByte_ffi {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (dst src : CrepExpHOL width) :
    (evalCrepSemHOLProg state memDec shMemDec (.storeByte dst src)).2.ffi = state.ffi := by
  rw [evalCrepSemHOLProg_storeByte]
  split <;> try rfl
  all_goals split <;> try rfl
  all_goals split <;> try rfl

@[simp] theorem evalCrepSemHOLProg_storeGlob_ffi {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (dst : BitVec 5) (src : CrepExpHOL width) :
    (evalCrepSemHOLProg state memDec shMemDec (.storeGlob dst src)).2.ffi = state.ffi := by
  rw [evalCrepSemHOLProg_storeGlob]
  split <;> try rfl
  all_goals split <;> try rfl

@[simp] theorem evalCrepSemHOLProg_break_ffi {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (label : Nat) :
    (evalCrepSemHOLProg state memDec shMemDec (.break label : CrepProgHOL width)).2.ffi =
      state.ffi := by
  rw [evalCrepSemHOLProg_break]

@[simp] theorem evalCrepSemHOLProg_continue_ffi {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (label : Nat) :
    (evalCrepSemHOLProg state memDec shMemDec (.continue label : CrepProgHOL width)).2.ffi =
      state.ffi := by
  rw [evalCrepSemHOLProg_continue]

@[simp] theorem evalCrepSemHOLProg_raise_ffi {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (exception : BitVec width) :
    (evalCrepSemHOLProg state memDec shMemDec (.raise exception)).2.ffi = state.ffi := by
  rw [evalCrepSemHOLProg_raise]
  rfl

@[simp] theorem evalCrepSemHOLProg_return_ffi {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (values : List (CrepExpHOL width)) :
    (evalCrepSemHOLProg state memDec shMemDec (.return values)).2.ffi = state.ffi := by
  rw [evalCrepSemHOLProg_return]
  split <;> rfl

@[simp] theorem evalCrepSemHOLProg_tick_ffi {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) :
    (evalCrepSemHOLProg state memDec shMemDec (.tick : CrepProgHOL width)).2.ffi = state.ffi := by
  rw [evalCrepSemHOLProg_tick]
  split <;> rfl

/-! ## FFI reduction for the recursive non-FFI clauses

The base FFI-preservation lemmas above cover the non-recursive clauses. These
helpers and equations factor the remaining non-FFI control flow so that the
event-preservation argument can be lifted clause by clause: the two derived
states (`crepStampExactDomains`, `fixClockCrepSemHOL`) preserve `ffi`, and each
recursive clause's result `ffi` is exactly the `ffi` of its sub-evaluation (on a
state with the same `ffi`). Flapjack infrastructure for the clock-indexed
`ioEvents` chain tracked by `flapjack-pxn.18.4.8.2`; untagged. `while`, `call`,
and the FFI-calling `shMem`/`extCall` clauses remain for later children. -/

/-- Domain stamping only rewrites the membership predicates, so it preserves the
    FFI component of the state. -/
@[simp] theorem crepStampExactDomains_ffi {width : Nat} [NeZero width] {σ : Type}
    (base state : CrepSemHOLState width σ) :
    (crepStampExactDomains base state).ffi = state.ffi := rfl

/-- `fix_clock` only lowers the clock, so it preserves the FFI component of the
    result state. -/
@[simp] theorem fixClockCrepSemHOL_ffi {width : Nat} [NeZero width] {σ : Type}
    {β : Type} (oldState : CrepSemHOLState width σ) (step : β × CrepSemHOLState width σ) :
    (fixClockCrepSemHOL oldState step).2.ffi = step.2.ffi := rfl

/-- FFI reduction for the `dec` clause: the result `ffi` is the sub-evaluation's
    `ffi` on the bound state, or the input `ffi` on the failure branch. -/
theorem evalCrepSemHOLProg_dec_ffi {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (name : Nat) (value : CrepExpHOL width) (body : CrepProgHOL width) :
    (evalCrepSemHOLProg state memDec shMemDec (.dec name value body)).2.ffi =
      (match crepExactEvalExp state memDec value with
       | none => state.ffi
       | some v =>
           (evalCrepSemHOLProg (CrepSemHOLState.setVar name v state) memDec shMemDec body).2.ffi) := by
  rw [evalCrepSemHOLProg_dec]
  cases h : crepExactEvalExp state memDec value with
  | none => rfl
  | some v => rfl

/-- FFI reduction for the `seq` clause: the result `ffi` is the first program's
    `ffi` when it returns a result, otherwise the second program's `ffi`. -/
theorem evalCrepSemHOLProg_seq_ffi {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (first second : CrepProgHOL width) :
    (evalCrepSemHOLProg state memDec shMemDec (.seq first second)).2.ffi =
      (match fixClockCrepSemHOL state (evalCrepSemHOLProg state memDec shMemDec first) with
       | (none, stepState) =>
           (evalCrepSemHOLProg (crepStampExactDomains state stepState) memDec shMemDec second).2.ffi
       | (some _, stepState) => stepState.ffi) := by
  rw [evalCrepSemHOLProg_seq]
  cases h : fixClockCrepSemHOL state (evalCrepSemHOLProg state memDec shMemDec first) with
  | mk result stepState =>
      cases result with
      | none => rfl
      | some res => rfl

/-- FFI reduction for the `ite` clause: the result `ffi` is the taken branch's
    `ffi`, or the input `ffi` when the condition is not a `word`. -/
theorem evalCrepSemHOLProg_ite_ffi {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (condition : CrepExpHOL width) (thenBranch elseBranch : CrepProgHOL width) :
    (evalCrepSemHOLProg state memDec shMemDec (.ite condition thenBranch elseBranch)).2.ffi =
      (match crepExactEvalExp state memDec condition with
       | some (.word w) =>
           if w ≠ 0 then (evalCrepSemHOLProg state memDec shMemDec thenBranch).2.ffi
           else (evalCrepSemHOLProg state memDec shMemDec elseBranch).2.ffi
       | _ => state.ffi) := by
  rw [evalCrepSemHOLProg_ite]
  cases h : crepExactEvalExp state memDec condition with
  | none => rfl
  | some value =>
      cases value with
      | word w =>
          simp only []
          by_cases hw : w = 0
          · simp [hw]
          · rw [if_pos hw, if_pos hw]

/-- HOL `evaluate (Call caltyp fname argexps, s)` (`crepSemScript.sml:330-363`):
    evaluate the arguments, look up the code, require distinct formals, install
    the callee locals under `dec_clock`, run the body under `fix_clock`, then
    handle ordinary completion/`Break`/`Continue` as `Error`, and `Return`/
    `Exception` including the handler path and `empty_locals` cleanup.

    Source review against `evaluate_def` lines 335-364 and `lookup_code_def`
    lines 76-83 found the Call branches and side conditions aligned: `mapM`
    evaluates the arguments, the direct code-map case is the expanded
    `lookup_code` formal-count/distinctness check and zipped local installation,
    the return-info distinctness check precedes timeout, and the recursive
    body/handler and cleanup cases follow the HOL cases. The handler's
    `crepStampExactDomains` restores the original
    domain fields, which the evaluator clauses do not update, so the explicit
    domain decisions remain valid across that state update.

    This equation intentionally has no `@[hol]` tag. Its evaluator application
    takes explicit `memDec` and `shMemDec` arguments; HOL's `evaluate` has only
    the program and state arguments. That evaluator-interface mismatch remains
    even though the Call case body was source-reviewed. The faithful public
    evaluator interface is tracked by `flapjack-4ac.5.16.5.2`; this case audit
    is `flapjack-4ac.5.16.5.1`. -/
@[simp] theorem evalCrepSemHOLProg_call {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (returnInfo : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (function : MlString) (arguments : List (CrepExpHOL width)) :
    evalCrepSemHOLProg state memDec shMemDec (.call returnInfo function arguments) =
      (match arguments.mapM (@evalCrepSemHOLExp width ‹NeZero width› σ state memDec) with
       | none => (some .error, state)
       | some values =>
           match state.code.lookup function with
           | none => (some .error, state)
           | some (parameters, body) =>
               if parameters.length = values.length && parameters.Nodup then
                 let proceed : Option (CrepResultHOLExact width) ×
                     CrepSemHOLState width σ :=
                   if _hclock : state.clock = 0 then
                     (some .timeOut, CrepSemHOLState.emptyLocals state)
                   else
                     let calleeLocals :=
                       HolFiniteMapExact.empty.updateList (parameters.zip values)
                     let callee : CrepSemHOLState width σ :=
                       { state with locals := calleeLocals }
                     let decCallee := decClockCrepSemHOL callee
                     let fixed := fixClockCrepSemHOL decCallee
                       (evalCrepSemHOLProg decCallee memDec shMemDec body)
                     match _hfixed : fixed with
                     | (none, bodyState) => (some .error, bodyState)
                     | (some (.break _), bodyState) => (some .error, bodyState)
                     | (some (.continue _), bodyState) => (some .error, bodyState)
                     | (some (.return retvs), bodyState) =>
                         match returnInfo with
                         | none => (some (.return retvs),
                             CrepSemHOLState.emptyLocals bodyState)
                         | some (rts, _) =>
                             if retvs.length ≠ rts.length then
                               (some .error, bodyState)
                             else
                              match rts.mapM state.locals.lookup with
                              | some _ => (none, { bodyState with
                                  locals := state.locals.updateListEq
                                    (rts.zip retvs) })
                              | none => (some .error, bodyState)
                     | (some (.exception eid), bodyState) =>
                         match returnInfo with
                         | none => (some (.exception eid),
                             CrepSemHOLState.emptyLocals bodyState)
                         | some (_, none) => (some (.exception eid),
                             CrepSemHOLState.emptyLocals bodyState)
                         | some (_, some (eid', handlerBody)) =>
                             let handlerState : CrepSemHOLState width σ :=
                               crepStampExactDomains state
                                 { bodyState with locals := state.locals }
                             if eid = eid' then
                               evalCrepSemHOLProg handlerState memDec shMemDec handlerBody
                             else (some (.exception eid),
                               CrepSemHOLState.emptyLocals bodyState)
                     | (some result, bodyState) =>
                         (some result, CrepSemHOLState.emptyLocals bodyState)
                 match returnInfo with
                 | some (rts, _) => if rts.Nodup then proceed else (some .error, state)
                 | none => proceed
               else (some .error, state)) := by
  rw [evalCrepSemHOLProg.eq_def] <;> rfl

/-- HOL `Call` argument evaluation failure: `(SOME Error, s)`. -/
theorem evalCrepSemHOLProg_call_args_error {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (returnInfo : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (function : MlString) (arguments : List (CrepExpHOL width))
    (hargs : arguments.mapM (@evalCrepSemHOLExp width ‹NeZero width› σ state memDec) = none) :
    evalCrepSemHOLProg state memDec shMemDec (.call returnInfo function arguments) =
      (some .error, state) := by
  rw [evalCrepSemHOLProg_call, hargs] <;> rfl

/-- HOL `Call` clock exhaustion with `caltyp = NONE` and a successful argument
    evaluation: `(SOME TimeOut, empty_locals s)`. -/
theorem evalCrepSemHOLProg_call_none_timeout {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (function : MlString) (arguments : List (CrepExpHOL width))
    (values : List (HolWordLab width)) (parameters : List Nat) (body : CrepProgHOL width)
    (hargs : arguments.mapM (@evalCrepSemHOLExp width ‹NeZero width› σ state memDec) =
      some values)
    (hcode : state.code.lookup function = some (parameters, body))
    (hlen : parameters.length = values.length) (hnodup : parameters.Nodup)
    (hclock : state.clock = 0) :
    evalCrepSemHOLProg state memDec shMemDec (.call none function arguments) =
      (some .timeOut, CrepSemHOLState.emptyLocals state) := by
  rw [evalCrepSemHOLProg_call, hargs, hcode]
  simp only [hlen, hnodup, decide_true, Bool.true_and, if_true, dif_pos hclock]


/-! ## FFI reduction for the FFI-producing clauses

Only `ShMem` and `ExtCall` extend `state.ffi` among the exact evaluator clauses.
These equations present each clause's resulting `ffi` as the shared-memory
helper's `ffi` (`ShMem`) or as `state.ffi`/the FFI-returned state (`ExtCall`).
Untagged Flapjack infrastructure; base cases of the clock-indexed event-prefix
chain (HOL `crepPropsScript.sml:1020`) tracked by `flapjack-pxn.18.4.8.2`. -/

theorem evalCrepSemHOLProg_shMem_ffi {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (operator : CrepMemOp) (name : Nat) (address : CrepExpHOL width) :
    (evalCrepSemHOLProg state memDec shMemDec (.shMem operator name address)).2.ffi =
      (match crepExactEvalExp state memDec address with
       | some (.word addressValue) =>
           if crepIsLoadMemOp operator then
             match state.locals.lookup name with
             | some _ => (crepShMemLoadHOL operator name addressValue state shMemDec).2.ffi
             | none => state.ffi
           else
             match state.locals.lookup name with
             | some (.word _) => (crepShMemStoreHOL operator name addressValue state shMemDec).2.ffi
             | _ => state.ffi
       | _ => state.ffi) := by
  rw [evalCrepSemHOLProg_shMem]
  cases hcond : crepExactEvalExp state memDec address with
  | none => rfl
  | some value =>
      cases value with
      | word addressValue =>
          simp only []
          cases hb : crepIsLoadMemOp operator with
          | true =>
              cases hlook : state.locals.lookup name with
              | none => rfl
              | some v => rfl
          | false =>
              cases hlook : state.locals.lookup name with
              | none => rfl
              | some v => cases v with | word w => rfl

theorem evalCrepSemHOLProg_extCall_ffi {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (function : MlString) (configuration configurationLength array arrayLength : Nat) :
    (evalCrepSemHOLProg state memDec shMemDec
        (.extCall function configuration configurationLength array arrayLength)).2.ffi =
      (match state.locals.lookup configurationLength, state.locals.lookup configuration,
             state.locals.lookup arrayLength, state.locals.lookup array with
       | some (.word configLength), some (.word configAddress),
         some (.word arrayLengthValue), some (.word arrayAddress) =>
           match readBytearrayWordHOL (byteWidth := 8) configAddress configLength.toNat
                   (crepExactMemLoadByteWord8 state memDec),
                 readBytearrayWordHOL (byteWidth := 8) arrayAddress arrayLengthValue.toNat
                   (crepExactMemLoadByteWord8 state memDec) with
           | some configBytes, some arrayBytes =>
               match callFFIHOL state.ffi (.extCall function)
                   configBytes arrayBytes with
               | .final _event => state.ffi
               | .ret newFfi _newBytes => newFfi
           | _, _ => state.ffi
       | _, _, _, _ => state.ffi) := by
  rw [evalCrepSemHOLProg_extCall]
  cases h1 : state.locals.lookup configurationLength with
  | none => simp
  | some v1 =>
      cases v1 with
      | word configLength =>
          cases h2 : state.locals.lookup configuration with
          | none => simp
          | some v2 =>
              cases v2 with
              | word configAddress =>
                  cases h3 : state.locals.lookup arrayLength with
                  | none => simp
                  | some v3 =>
                      cases v3 with
                      | word arrayLengthValue =>
                          cases h4 : state.locals.lookup array with
                          | none => simp
                          | some v4 =>
                              cases v4 with
                              | word arrayAddress =>
                                  cases hr1 : readBytearrayWordHOL (byteWidth := 8) configAddress
                                      configLength.toNat (crepExactMemLoadByteWord8 state memDec) with
                                  | none => simp [hr1]
                                  | some configBytes =>
                                      cases hr2 : readBytearrayWordHOL (byteWidth := 8) arrayAddress
                                          arrayLengthValue.toNat (crepExactMemLoadByteWord8 state memDec) with
                                      | none => simp [hr1, hr2]
                                      | some arrayBytes =>
                                          cases hc : callFFIHOL state.ffi (.extCall function)
                                              configBytes arrayBytes with
                                          | final _event => simp [hr1, hr2, hc]
                                          | ret newFfi _newBytes => simp [hr1, hr2, hc]

/-! ## Domain-field projection and preservation infrastructure

The total evaluator threads the caller's `memDec`/`shMemDec` decision procedures
into its recursive calls and uses `crepStampExactDomains` to restate a derived
state's `memaddrs`/`shMemaddrs` as the base state's. The declarations below
establish the coordinator-HOLD domain-preservation invariant (bead
`flapjack-pxn.18.5.5.7.7.13`): the projection equations show every state update
leaves both domain fields untouched, `crepStampExactDomains_eq_self` shows the
stamp is the identity once the domains agree, and
`evalCrepSemHOLProg_preserves_domains` proves by clock/program-size well-founded
induction that the total evaluator never changes either domain field. The
recursive-state equality `crepStampExactDomains_evalCrepSemHOLProg` is then the
explicit identity used by the `Seq`/`While`/`Call` clauses. All declarations
here are untagged Flapjack infrastructure. -/

/-- Projection equations: the state helpers never change the `memaddrs` field. -/
@[simp] theorem CrepSemHOLState.setVar_memaddrs {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (value : HolWordLab width) (state : CrepSemHOLState width σ) :
    (CrepSemHOLState.setVar name value state).memaddrs = state.memaddrs := rfl

@[simp] theorem CrepSemHOLState.setVar_shMemaddrs {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (value : HolWordLab width) (state : CrepSemHOLState width σ) :
    (CrepSemHOLState.setVar name value state).shMemaddrs = state.shMemaddrs := rfl

@[simp] theorem CrepSemHOLState.setGlobals_memaddrs {width : Nat} [NeZero width] {σ : Type}
    (key : BitVec 5) (value : HolWordLab width) (state : CrepSemHOLState width σ) :
    (CrepSemHOLState.setGlobals key value state).memaddrs = state.memaddrs := rfl

@[simp] theorem CrepSemHOLState.setGlobals_shMemaddrs {width : Nat} [NeZero width] {σ : Type}
    (key : BitVec 5) (value : HolWordLab width) (state : CrepSemHOLState width σ) :
    (CrepSemHOLState.setGlobals key value state).shMemaddrs = state.shMemaddrs := rfl

@[simp] theorem CrepSemHOLState.emptyLocals_memaddrs {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    (CrepSemHOLState.emptyLocals state).memaddrs = state.memaddrs := rfl

@[simp] theorem CrepSemHOLState.emptyLocals_shMemaddrs {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    (CrepSemHOLState.emptyLocals state).shMemaddrs = state.shMemaddrs := rfl

@[simp] theorem decClockCrepSemHOL_memaddrs {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    (decClockCrepSemHOL state).memaddrs = state.memaddrs := rfl

@[simp] theorem decClockCrepSemHOL_shMemaddrs {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    (decClockCrepSemHOL state).shMemaddrs = state.shMemaddrs := rfl

@[simp] theorem fixClockCrepSemHOL_memaddrs {width : Nat} [NeZero width] {σ : Type} {β : Type}
    (state : CrepSemHOLState width σ) (step : β × CrepSemHOLState width σ) :
    (fixClockCrepSemHOL state step).2.memaddrs = step.2.memaddrs := rfl

@[simp] theorem fixClockCrepSemHOL_shMemaddrs {width : Nat} [NeZero width] {σ : Type} {β : Type}
    (state : CrepSemHOLState width σ) (step : β × CrepSemHOLState width σ) :
    (fixClockCrepSemHOL state step).2.shMemaddrs = step.2.shMemaddrs := rfl

@[simp] theorem crepStampExactDomains_memaddrs {width : Nat} [NeZero width] {σ : Type}
    (base s : CrepSemHOLState width σ) :
    (crepStampExactDomains base s).memaddrs = base.memaddrs := rfl

@[simp] theorem crepStampExactDomains_shMemaddrs {width : Nat} [NeZero width] {σ : Type}
    (base s : CrepSemHOLState width σ) :
    (crepStampExactDomains base s).shMemaddrs = base.shMemaddrs := rfl

@[simp] theorem crepStampExactDomains_clock {width : Nat} [NeZero width] {σ : Type}
    (base s : CrepSemHOLState width σ) :
    (crepStampExactDomains base s).clock = s.clock := rfl

/-- `crepStampExactDomains` is the identity on any state whose domain fields
    already agree with the base state. This is the projection identity the
    evaluator's `Seq`/`While`/`Call` recursive-state equalities need. -/
theorem crepStampExactDomains_eq_self {width : Nat} [NeZero width] {σ : Type}
    (base s : CrepSemHOLState width σ)
    (hmem : s.memaddrs = base.memaddrs)
    (hsh : s.shMemaddrs = base.shMemaddrs) :
    crepStampExactDomains base s = s := by
  rw [crepStampExactDomains, ← hmem, ← hsh]

/-- `fix_clock` only clamps the clock, so it preserves both domain fields of the
    step's state component. -/
theorem fixClock_result_domains {width : Nat} [NeZero width] {σ : Type} {β : Type}
    (state : CrepSemHOLState width σ) (step : β × CrepSemHOLState width σ)
    (res : β) (s1 : CrepSemHOLState width σ)
    (h : fixClockCrepSemHOL state step = (res, s1)) :
    s1.memaddrs = step.2.memaddrs ∧ s1.shMemaddrs = step.2.shMemaddrs := by
  have h1 := congrArg (fun p : β × CrepSemHOLState width σ => p.2.memaddrs) h
  have h2 := congrArg (fun p : β × CrepSemHOLState width σ => p.2.shMemaddrs) h
  simp only [fixClockCrepSemHOL_memaddrs, fixClockCrepSemHOL_shMemaddrs] at h1 h2
  exact ⟨h1.symm, h2.symm⟩

/-- The exact HOL `sh_mem_load` port preserves both domain fields. -/
theorem crepShMemLoadExactHOL_preserves_domains {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (address : BitVec width) (nb : Nat)
    (state : CrepSemHOLState width σ) [DecidablePred state.shMemaddrs] :
    (crepShMemLoadExactHOL name address nb state).2.memaddrs = state.memaddrs ∧
    (crepShMemLoadExactHOL name address nb state).2.shMemaddrs =
      state.shMemaddrs := by
  simp only [crepShMemLoadExactHOL]
  repeat' split
  all_goals simp [CrepSemHOLState.emptyLocals, CrepSemHOLState.setVar]

/-- The exact HOL `sh_mem_store` port preserves both domain fields. -/
theorem crepShMemStoreExactHOL_preserves_domains {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (address : BitVec width) (nb : Nat)
    (state : CrepSemHOLState width σ) [DecidablePred state.shMemaddrs] :
    (crepShMemStoreExactHOL name address nb state).2.memaddrs = state.memaddrs ∧
    (crepShMemStoreExactHOL name address nb state).2.shMemaddrs =
      state.shMemaddrs := by
  simp only [crepShMemStoreExactHOL]
  repeat' split
  all_goals simp

/-- The ShMem-load helper preserves both domain fields. -/
theorem crepShMemLoadHOL_preserves_domains {width : Nat} [NeZero width] {σ : Type}
    (operator : CrepMemOp) (name : Nat) (address : BitVec width)
    (state : CrepSemHOLState width σ)
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) :
    (crepShMemLoadHOL operator name address state shMemDec).2.memaddrs = state.memaddrs ∧
    (crepShMemLoadHOL operator name address state shMemDec).2.shMemaddrs =
      state.shMemaddrs := by
  simp only [crepShMemLoadHOL]
  exact crepShMemLoadExactHOL_preserves_domains name address (crepShMemByteWidth operator)
    state

/-- The ShMem-store helper preserves both domain fields. -/
theorem crepShMemStoreHOL_preserves_domains {width : Nat} [NeZero width] {σ : Type}
    (operator : CrepMemOp) (name : Nat) (address : BitVec width)
    (state : CrepSemHOLState width σ)
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) :
    (crepShMemStoreHOL operator name address state shMemDec).2.memaddrs = state.memaddrs ∧
    (crepShMemStoreHOL operator name address state shMemDec).2.shMemaddrs =
      state.shMemaddrs := by
  simp only [crepShMemStoreHOL]
  exact crepShMemStoreExactHOL_preserves_domains name address (crepShMemByteWidth operator)
    state

set_option linter.unusedVariables false in
/-- Domain preservation of the `Call` callee-result case split. `hfix` records
    that the `fix_clock` result state carries the input state's domain fields,
    and `hhandler` records the exception-handler call's preservation. -/
theorem crepCallFixed_domains {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (returnInfo : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fixed : Option (CrepResultHOLExact width) ×
      CrepSemHOLState width σ)
    (hfix : fixed.2.memaddrs = state.memaddrs ∧
      fixed.2.shMemaddrs = state.shMemaddrs)
    (hhandler : ∀ (handlerBody : CrepProgHOL width),
        (evalCrepSemHOLProg
          (crepStampExactDomains state { fixed.2 with locals := state.locals })
          memDec shMemDec handlerBody).2.memaddrs = state.memaddrs ∧
        (evalCrepSemHOLProg
          (crepStampExactDomains state { fixed.2 with locals := state.locals })
          memDec shMemDec handlerBody).2.shMemaddrs = state.shMemaddrs) :
    (match hfixed : fixed with
     | (none, bodyState) => (some CrepResultHOLExact.error, bodyState)
     | (some (CrepResultHOLExact.break _), bodyState) => (some CrepResultHOLExact.error, bodyState)
     | (some (CrepResultHOLExact.continue _), bodyState) => (some CrepResultHOLExact.error, bodyState)
     | (some (CrepResultHOLExact.return retvs), bodyState) =>
         match returnInfo with
         | none => (some (CrepResultHOLExact.return retvs), CrepSemHOLState.emptyLocals bodyState)
         | some (rts, _) =>
             if retvs.length ≠ rts.length then (some CrepResultHOLExact.error, bodyState)
             else match rts.mapM state.locals.lookup with
               | some _ => (none, { bodyState with
                   locals := state.locals.updateListEq
                     (rts.zip retvs) })
               | none => (some CrepResultHOLExact.error, bodyState)
     | (some (CrepResultHOLExact.exception eid), bodyState) =>
         match returnInfo with
         | none =>
             (some (CrepResultHOLExact.exception eid), CrepSemHOLState.emptyLocals bodyState)
         | some (_, none) =>
             (some (CrepResultHOLExact.exception eid), CrepSemHOLState.emptyLocals bodyState)
         | some (_, some (eid', handlerBody)) =>
             if eid = eid' then
               evalCrepSemHOLProg
                 (crepStampExactDomains state { bodyState with locals := state.locals })
                 memDec shMemDec handlerBody
             else (some (CrepResultHOLExact.exception eid), CrepSemHOLState.emptyLocals bodyState)
     | (some result, bodyState) =>
         (some result, CrepSemHOLState.emptyLocals bodyState)).2.memaddrs =
        state.memaddrs ∧
    (match hfixed : fixed with
     | (none, bodyState) => (some CrepResultHOLExact.error, bodyState)
     | (some (CrepResultHOLExact.break _), bodyState) => (some CrepResultHOLExact.error, bodyState)
     | (some (CrepResultHOLExact.continue _), bodyState) => (some CrepResultHOLExact.error, bodyState)
     | (some (CrepResultHOLExact.return retvs), bodyState) =>
         match returnInfo with
         | none => (some (CrepResultHOLExact.return retvs), CrepSemHOLState.emptyLocals bodyState)
         | some (rts, _) =>
             if retvs.length ≠ rts.length then (some CrepResultHOLExact.error, bodyState)
             else match rts.mapM state.locals.lookup with
               | some _ => (none, { bodyState with
                   locals := state.locals.updateListEq
                     (rts.zip retvs) })
               | none => (some CrepResultHOLExact.error, bodyState)
     | (some (CrepResultHOLExact.exception eid), bodyState) =>
         match returnInfo with
         | none =>
             (some (CrepResultHOLExact.exception eid), CrepSemHOLState.emptyLocals bodyState)
         | some (_, none) =>
             (some (CrepResultHOLExact.exception eid), CrepSemHOLState.emptyLocals bodyState)
         | some (_, some (eid', handlerBody)) =>
             if eid = eid' then
               evalCrepSemHOLProg
                 (crepStampExactDomains state { bodyState with locals := state.locals })
                 memDec shMemDec handlerBody
             else (some (CrepResultHOLExact.exception eid), CrepSemHOLState.emptyLocals bodyState)
     | (some result, bodyState) =>
         (some result, CrepSemHOLState.emptyLocals bodyState)).2.shMemaddrs =
        state.shMemaddrs := by
  split
  · exact hfix
  · exact hfix
  · exact hfix
  · split
    · simp only [CrepSemHOLState.emptyLocals_memaddrs,
        CrepSemHOLState.emptyLocals_shMemaddrs]
      exact hfix
    · split
      · exact hfix
      · split
        · exact hfix
        · exact hfix
  · split
    · simp only [CrepSemHOLState.emptyLocals_memaddrs,
        CrepSemHOLState.emptyLocals_shMemaddrs]
      exact hfix
    · simp only [CrepSemHOLState.emptyLocals_memaddrs,
        CrepSemHOLState.emptyLocals_shMemaddrs]
      exact hfix
    · split
      · exact hhandler _
      · simp only [CrepSemHOLState.emptyLocals_memaddrs,
          CrepSemHOLState.emptyLocals_shMemaddrs]
        exact hfix
  · simp only [CrepSemHOLState.emptyLocals_memaddrs,
      CrepSemHOLState.emptyLocals_shMemaddrs]
    exact hfix

set_option linter.unusedVariables false in
/-- Domain preservation of the `While` loop-control case split. `hstep` records
    that the state component of the `fix_clock` result carries the input state's
    domain fields, and `hrec` records the recursive `While` call's preservation
    for that state. -/
theorem crepWhileStep_domains {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (condition : CrepExpHOL width) (body : CrepProgHOL width)
    (loopStep : Option (CrepResultHOLExact width) ×
      CrepSemHOLState width σ)
    (hstep : loopStep.2.memaddrs = state.memaddrs ∧
      loopStep.2.shMemaddrs = state.shMemaddrs)
    (hrec : (evalCrepSemHOLProg (crepStampExactDomains state loopStep.2)
        memDec shMemDec (.while condition body)).2.memaddrs = state.memaddrs ∧
      (evalCrepSemHOLProg (crepStampExactDomains state loopStep.2)
        memDec shMemDec (.while condition body)).2.shMemaddrs = state.shMemaddrs) :
    (match hfixed : loopStep with
     | (none, loopState) =>
         evalCrepSemHOLProg (crepStampExactDomains state loopState) memDec shMemDec
           (.while condition body)
     | (some (.continue 0), loopState) =>
         evalCrepSemHOLProg (crepStampExactDomains state loopState) memDec shMemDec
           (.while condition body)
     | (some (.break 0), loopState) => (none, loopState)
     | (result, loopState) => (exitLoopCrepResult result, loopState)).2.memaddrs =
        state.memaddrs ∧
    (match hfixed : loopStep with
     | (none, loopState) =>
         evalCrepSemHOLProg (crepStampExactDomains state loopState) memDec shMemDec
           (.while condition body)
     | (some (.continue 0), loopState) =>
         evalCrepSemHOLProg (crepStampExactDomains state loopState) memDec shMemDec
           (.while condition body)
     | (some (.break 0), loopState) => (none, loopState)
     | (result, loopState) => (exitLoopCrepResult result, loopState)).2.shMemaddrs =
        state.shMemaddrs := by
  split <;> (first | exact hrec | exact hstep)


/-- Domain preservation predicate for a single evaluator call. -/
@[reducible] def CrepDomainsPreserved {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (program : CrepProgHOL width) : Prop :=
  (evalCrepSemHOLProg state memDec shMemDec program).2.memaddrs = state.memaddrs ∧
  (evalCrepSemHOLProg state memDec shMemDec program).2.shMemaddrs = state.shMemaddrs

/-- The total evaluator preserves both memory-domain fields: for every input
    state and program, the result state carries the input state's `memaddrs` and
    `shMemaddrs` unchanged. This is the shape/projection invariant the
    coordinator HOLD requested; it justifies the recursive-state equality of the
    `crepStampExactDomains` calls in the `Seq`/`While`/`Call` clauses. -/
theorem evalCrepSemHOLProg_preserves_domains {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (program : CrepProgHOL width) :
    CrepDomainsPreserved state memDec shMemDec program := by
  have hmain : ∀ (c : Nat) (state : CrepSemHOLState width σ), state.clock ≤ c →
      ∀ (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
        (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
        (program : CrepProgHOL width),
        CrepDomainsPreserved state memDec shMemDec program := by
    intro c
    induction c using Nat.strongRecOn with
    | ind c ihClock =>
      intro state hclk memDec shMemDec program
      have inner : ∀ (n : Nat) (program : CrepProgHOL width), sizeOf program ≤ n →
          ∀ (state : CrepSemHOLState width σ), state.clock ≤ c →
          ∀ (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
            (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)),
            CrepDomainsPreserved state memDec shMemDec program := by
        intro n
        induction n using Nat.strongRecOn with
        | ind n ihSize =>
          intro program hsize state hclk memDec shMemDec
          cases program with
          | skip =>
              simp [CrepDomainsPreserved, evalCrepSemHOLProg_skip]
          | dec name value body =>
              have hsub : sizeOf body < n := by
                have h1 : sizeOf body < sizeOf (CrepProgHOL.dec name value body) := by
                  decreasing_trivial
                omega
              have ihBody := ihSize (sizeOf body) hsub body (by omega)
              unfold CrepDomainsPreserved
              rw [evalCrepSemHOLProg_dec]
              split
              · simp
              · rename_i v _
                dsimp only
                have hb := ihBody (CrepSemHOLState.setVar name v state)
                  (by simp only [CrepSemHOLState.setVar]; exact hclk) memDec shMemDec
                unfold CrepDomainsPreserved at hb
                rw [hb.1, hb.2]
                simp
          | assign name src =>
              unfold CrepDomainsPreserved
              rw [evalCrepSemHOLProg_assign]
              repeat' (first | split | simp_all)
          | primitive names operator args =>
              unfold CrepDomainsPreserved
              rw [evalCrepSemHOLProg_primitive]
              repeat' (first | split | simp_all)
          | store dst src =>
              unfold CrepDomainsPreserved
              rw [evalCrepSemHOLProg_store]
              repeat' (first | split | simp_all)
          | store32 dst src =>
              unfold CrepDomainsPreserved
              rw [evalCrepSemHOLProg_store32]
              repeat' (first | split | simp_all)
          | storeByte dst src =>
              unfold CrepDomainsPreserved
              rw [evalCrepSemHOLProg_storeByte]
              repeat' (first | split | simp_all)
          | storeGlob dst src =>
              unfold CrepDomainsPreserved
              rw [evalCrepSemHOLProg_storeGlob]
              repeat' (first | split | simp_all)
          | seq first second =>
              have hsubF : sizeOf first < n := by
                have h1 : sizeOf first < sizeOf (CrepProgHOL.seq first second) := by
                  decreasing_trivial
                omega
              have hsubS : sizeOf second < n := by
                have h1 : sizeOf second < sizeOf (CrepProgHOL.seq first second) := by
                  decreasing_trivial
                omega
              have ihFirst := ihSize (sizeOf first) hsubF first (by omega)
              have ihSecond := ihSize (sizeOf second) hsubS second (by omega)
              unfold CrepDomainsPreserved
              simp only [evalCrepSemHOLProg_seq]
              split
              · rename_i stepState hstep
                have hSecond := ihSecond (crepStampExactDomains state stepState)
                  (by
                    have hb := fixClockCrepSemHOL_IMP_LESS_EQ state
                      (evalCrepSemHOLProg state memDec shMemDec first) none stepState
                      (by simpa using hstep)
                    change stepState.clock ≤ c
                    omega)
                  memDec shMemDec
                unfold CrepDomainsPreserved at hSecond
                rw [hSecond.1, hSecond.2]
                simp
              · have hFirst := ihFirst state hclk memDec shMemDec
                unfold CrepDomainsPreserved at hFirst
                exact hFirst
          | ite condition thenBranch elseBranch =>
              have hsubT : sizeOf thenBranch < n := by
                have h1 : sizeOf thenBranch <
                    sizeOf (CrepProgHOL.ite condition thenBranch elseBranch) := by
                  decreasing_trivial
                omega
              have hsubE : sizeOf elseBranch < n := by
                have h1 : sizeOf elseBranch <
                    sizeOf (CrepProgHOL.ite condition thenBranch elseBranch) := by
                  decreasing_trivial
                omega
              have ihThen := ihSize (sizeOf thenBranch) hsubT thenBranch (by omega)
              have ihElse := ihSize (sizeOf elseBranch) hsubE elseBranch (by omega)
              unfold CrepDomainsPreserved
              rw [evalCrepSemHOLProg_ite]
              split
              · rename_i w
                split
                · exact ihThen state hclk memDec shMemDec
                · exact ihElse state hclk memDec shMemDec
              · simp
          | «while» condition body =>
              unfold CrepDomainsPreserved
              rw [evalCrepSemHOLProg_while]
              split
              · rename_i w
                split
                · split
                  · simp
                  · have hBody := ihClock (decClockCrepSemHOL state).clock
                      (by simp only [decClockCrepSemHOL]; omega) (decClockCrepSemHOL state)
                      (by simp only [decClockCrepSemHOL]; omega) memDec shMemDec body
                    unfold CrepDomainsPreserved at hBody
                    dsimp only
                    refine crepWhileStep_domains state memDec shMemDec condition body
                      (fixClockCrepSemHOL (decClockCrepSemHOL state)
                        (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec
                          body)) ?_ ?_
                    · have hloop := fixClock_result_domains (decClockCrepSemHOL state)
                        (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec body)
                        _ _ rfl
                      exact ⟨hloop.1.trans hBody.1, hloop.2.trans hBody.2⟩
                    · have hclock : (fixClockCrepSemHOL (decClockCrepSemHOL state)
                          (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec
                            body)).2.clock < c := by
                        have hb : (fixClockCrepSemHOL (decClockCrepSemHOL state)
                            (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec
                              body)).2.clock ≤ (decClockCrepSemHOL state).clock :=
                          fixClockCrepSemHOL_IMP_LESS_EQ (decClockCrepSemHOL state)
                            (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec
                              body) _ _ rfl
                        have hb2 : (decClockCrepSemHOL state).clock < c := by
                          simp only [decClockCrepSemHOL]
                          omega
                        omega
                      have h := ihClock
                        (fixClockCrepSemHOL (decClockCrepSemHOL state)
                          (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec
                            body)).2.clock hclock
                        (crepStampExactDomains state
                          (fixClockCrepSemHOL (decClockCrepSemHOL state)
                            (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec
                              body)).2)
                        (by
                          change (fixClockCrepSemHOL (decClockCrepSemHOL state)
                            (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec
                              body)).2.clock ≤
                            (fixClockCrepSemHOL (decClockCrepSemHOL state)
                              (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec
                                body)).2.clock
                          omega) memDec shMemDec
                        (.while condition body)
                      unfold CrepDomainsPreserved at h
                      exact h
                · simp
              · simp
          | «break» label =>
              simp [CrepDomainsPreserved, evalCrepSemHOLProg_break]
          | «continue» label =>
              simp [CrepDomainsPreserved, evalCrepSemHOLProg_continue]
          | call calleeInfo function arguments =>
              unfold CrepDomainsPreserved
              rw [evalCrepSemHOLProg_call]
              split
              · simp
              · rename_i values _
                split
                · simp
                · rename_i parameters body _
                  split
                  · -- arity ok
                    dsimp only
                    split
                    · -- calleeInfo = some (rts, _)
                      rename_i rts snd
                      split
                      · -- rts.Nodup
                        dsimp only
                        split
                        · simp
                        · have hBody := ihClock
                            (decClockCrepSemHOL
                              { state with locals :=
                                HolFiniteMapExact.empty.updateList (parameters.zip values) }).clock
                            (by simp only [decClockCrepSemHOL]; omega)
                            (decClockCrepSemHOL
                              { state with locals :=
                                HolFiniteMapExact.empty.updateList (parameters.zip values) })
                            (by simp only [decClockCrepSemHOL]; omega) memDec shMemDec body
                          unfold CrepDomainsPreserved at hBody
                          refine crepCallFixed_domains state memDec shMemDec (some (rts, snd))
                            (fixClockCrepSemHOL
                              (decClockCrepSemHOL
                                { state with locals :=
                                  HolFiniteMapExact.empty.updateList (parameters.zip values) })
                              (evalCrepSemHOLProg
                                (decClockCrepSemHOL
                                  { state with locals :=
                                    HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                memDec shMemDec body)) ?_ ?_
                          · have hloop := fixClock_result_domains
                              (decClockCrepSemHOL
                                { state with locals :=
                                  HolFiniteMapExact.empty.updateList (parameters.zip values) })
                              (evalCrepSemHOLProg
                                (decClockCrepSemHOL
                                  { state with locals :=
                                    HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                memDec shMemDec body) _ _ rfl
                            exact ⟨hloop.1.trans hBody.1, hloop.2.trans hBody.2⟩
                          · intro handlerBody
                            have hclock : (crepStampExactDomains state
                                  { (fixClockCrepSemHOL
                                      (decClockCrepSemHOL
                                        { state with locals :=
                                          HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                      (evalCrepSemHOLProg
                                        (decClockCrepSemHOL
                                          { state with locals :=
                                            HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                        memDec shMemDec body)).2 with
                                    locals := state.locals }).clock < c := by
                              change (fixClockCrepSemHOL
                                  (decClockCrepSemHOL
                                    { state with locals :=
                                      HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                  (evalCrepSemHOLProg
                                    (decClockCrepSemHOL
                                      { state with locals :=
                                        HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                    memDec shMemDec body)).2.clock < c
                              have hb : (fixClockCrepSemHOL
                                  (decClockCrepSemHOL
                                    { state with locals :=
                                      HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                  (evalCrepSemHOLProg
                                    (decClockCrepSemHOL
                                      { state with locals :=
                                        HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                    memDec shMemDec body)).2.clock ≤
                                  (decClockCrepSemHOL
                                    { state with locals :=
                                      HolFiniteMapExact.empty.updateList (parameters.zip values) }).clock :=
                                fixClockCrepSemHOL_IMP_LESS_EQ
                                  (decClockCrepSemHOL
                                    { state with locals :=
                                      HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                  (evalCrepSemHOLProg
                                    (decClockCrepSemHOL
                                      { state with locals :=
                                        HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                    memDec shMemDec body) _ _ rfl
                              have hb2 : (decClockCrepSemHOL
                                  { state with locals :=
                                    HolFiniteMapExact.empty.updateList (parameters.zip values) }).clock < c := by
                                simp only [decClockCrepSemHOL]
                                omega
                              omega
                            have h := ihClock
                              (crepStampExactDomains state
                                { (fixClockCrepSemHOL
                                    (decClockCrepSemHOL
                                      { state with locals :=
                                        HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                    (evalCrepSemHOLProg
                                      (decClockCrepSemHOL
                                        { state with locals :=
                                          HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                      memDec shMemDec body)).2 with
                                  locals := state.locals }).clock hclock
                              (crepStampExactDomains state
                                { (fixClockCrepSemHOL
                                    (decClockCrepSemHOL
                                      { state with locals :=
                                        HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                    (evalCrepSemHOLProg
                                      (decClockCrepSemHOL
                                        { state with locals :=
                                          HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                      memDec shMemDec body)).2 with
                                  locals := state.locals })
                              (by omega) memDec shMemDec
                              handlerBody
                            unfold CrepDomainsPreserved at h
                            exact h
                      · simp
                    · -- calleeInfo = none
                      dsimp only
                      split
                      · simp
                      · have hBody := ihClock
                          (decClockCrepSemHOL
                            { state with locals :=
                              HolFiniteMapExact.empty.updateList (parameters.zip values) }).clock
                          (by simp only [decClockCrepSemHOL]; omega)
                          (decClockCrepSemHOL
                            { state with locals :=
                              HolFiniteMapExact.empty.updateList (parameters.zip values) })
                          (by simp only [decClockCrepSemHOL]; omega) memDec shMemDec body
                        unfold CrepDomainsPreserved at hBody
                        refine crepCallFixed_domains state memDec shMemDec none
                          (fixClockCrepSemHOL
                            (decClockCrepSemHOL
                              { state with locals :=
                                HolFiniteMapExact.empty.updateList (parameters.zip values) })
                            (evalCrepSemHOLProg
                              (decClockCrepSemHOL
                                { state with locals :=
                                  HolFiniteMapExact.empty.updateList (parameters.zip values) })
                              memDec shMemDec body)) ?_ ?_
                        · have hloop := fixClock_result_domains
                            (decClockCrepSemHOL
                              { state with locals :=
                                HolFiniteMapExact.empty.updateList (parameters.zip values) })
                            (evalCrepSemHOLProg
                              (decClockCrepSemHOL
                                { state with locals :=
                                  HolFiniteMapExact.empty.updateList (parameters.zip values) })
                              memDec shMemDec body) _ _ rfl
                          exact ⟨hloop.1.trans hBody.1, hloop.2.trans hBody.2⟩
                        · intro handlerBody
                          have hclock : (crepStampExactDomains state
                                { (fixClockCrepSemHOL
                                    (decClockCrepSemHOL
                                      { state with locals :=
                                        HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                    (evalCrepSemHOLProg
                                      (decClockCrepSemHOL
                                        { state with locals :=
                                          HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                      memDec shMemDec body)).2 with
                                  locals := state.locals }).clock < c := by
                            change (fixClockCrepSemHOL
                                (decClockCrepSemHOL
                                  { state with locals :=
                                    HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                (evalCrepSemHOLProg
                                  (decClockCrepSemHOL
                                    { state with locals :=
                                      HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                  memDec shMemDec body)).2.clock < c
                            have hb : (fixClockCrepSemHOL
                                (decClockCrepSemHOL
                                  { state with locals :=
                                    HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                (evalCrepSemHOLProg
                                  (decClockCrepSemHOL
                                    { state with locals :=
                                      HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                  memDec shMemDec body)).2.clock ≤
                                (decClockCrepSemHOL
                                  { state with locals :=
                                    HolFiniteMapExact.empty.updateList (parameters.zip values) }).clock :=
                              fixClockCrepSemHOL_IMP_LESS_EQ
                                (decClockCrepSemHOL
                                  { state with locals :=
                                    HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                (evalCrepSemHOLProg
                                  (decClockCrepSemHOL
                                    { state with locals :=
                                      HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                  memDec shMemDec body) _ _ rfl
                            have hb2 : (decClockCrepSemHOL
                                { state with locals :=
                                  HolFiniteMapExact.empty.updateList (parameters.zip values) }).clock < c := by
                              simp only [decClockCrepSemHOL]
                              omega
                            omega
                          have h := ihClock
                            (crepStampExactDomains state
                              { (fixClockCrepSemHOL
                                  (decClockCrepSemHOL
                                    { state with locals :=
                                      HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                  (evalCrepSemHOLProg
                                    (decClockCrepSemHOL
                                      { state with locals :=
                                        HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                    memDec shMemDec body)).2 with
                                locals := state.locals }).clock hclock
                            (crepStampExactDomains state
                              { (fixClockCrepSemHOL
                                  (decClockCrepSemHOL
                                    { state with locals :=
                                      HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                  (evalCrepSemHOLProg
                                    (decClockCrepSemHOL
                                      { state with locals :=
                                        HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                    memDec shMemDec body)).2 with
                                locals := state.locals })
                            (by omega) memDec shMemDec
                            handlerBody
                          unfold CrepDomainsPreserved at h
                          exact h
                  · simp
          | extCall function configuration configurationLength array arrayLength =>
              unfold CrepDomainsPreserved
              rw [evalCrepSemHOLProg_extCall]
              repeat' (first | split | simp_all)
          | raise exception =>
              simp [CrepDomainsPreserved, evalCrepSemHOLProg_raise]
          | «return» values =>
              unfold CrepDomainsPreserved
              rw [evalCrepSemHOLProg_return]
              split <;> simp
          | shMem operator name address =>
              unfold CrepDomainsPreserved
              rw [evalCrepSemHOLProg_shMem]
              split
              · split
                · split
                  · exact crepShMemLoadHOL_preserves_domains _ _ _ _ _
                  · simp
                · split
                  · exact crepShMemStoreHOL_preserves_domains _ _ _ _ _
                  · simp
              · simp
          | tick =>
              unfold CrepDomainsPreserved
              rw [evalCrepSemHOLProg_tick]
              split <;> simp
      exact inner (sizeOf program) program (by omega) state hclk memDec shMemDec
  exact hmain state.clock state (by omega) memDec shMemDec program

/-- The total evaluator preserves `memaddrs`. -/
theorem evalCrepSemHOLProg_preserves_memaddrs {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (program : CrepProgHOL width) :
    (evalCrepSemHOLProg state memDec shMemDec program).2.memaddrs = state.memaddrs :=
  (evalCrepSemHOLProg_preserves_domains state memDec shMemDec program).1

/-- The total evaluator preserves `shMemaddrs`. -/
theorem evalCrepSemHOLProg_preserves_shMemaddrs {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (program : CrepProgHOL width) :
    (evalCrepSemHOLProg state memDec shMemDec program).2.shMemaddrs = state.shMemaddrs :=
  (evalCrepSemHOLProg_preserves_domains state memDec shMemDec program).2

/-- Recursive-state equality: the `crepStampExactDomains` call the evaluator
    performs before a recursive step is the identity on the produced state,
    because the evaluator already preserves both domain fields. This is the
    invariant that makes threading the base state's decision procedures sound. -/
theorem crepStampExactDomains_evalCrepSemHOLProg {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (program : CrepProgHOL width) :
    crepStampExactDomains state (evalCrepSemHOLProg state memDec shMemDec program).2 =
      (evalCrepSemHOLProg state memDec shMemDec program).2 :=
  crepStampExactDomains_eq_self state _
    (evalCrepSemHOLProg_preserves_memaddrs state memDec shMemDec program)
    (evalCrepSemHOLProg_preserves_shMemaddrs state memDec shMemDec program)

/-- Flapjack-only transport of an explicit memory-domain decision procedure
    across a proved equality of exact state projections. This keeps the
    evaluator's membership decider explicit instead of introducing classical
    typeclass search for a derived state. There is no separate HOL declaration
    for this Lean equality-elimination helper. -/
def crepMemDecTransport {width : Nat} [NeZero width] {σ : Type}
    {base updated : CrepSemHOLState width σ}
    (hdom : base.memaddrs = updated.memaddrs)
    (memDec : (address : BitVec width) → Decidable (base.memaddrs address)) :
    (address : BitVec width) → Decidable (updated.memaddrs address) :=
  fun address => hdom ▸ memDec address

/-- Shared-memory counterpart of `crepMemDecTransport`; Flapjack-only, with no
    separate HOL declaration. -/
def crepShMemDecTransport {width : Nat} [NeZero width] {σ : Type}
    {base updated : CrepSemHOLState width σ}
    (hdom : base.shMemaddrs = updated.shMemaddrs)
    (shMemDec : (address : BitVec width) → Decidable (base.shMemaddrs address)) :
    (address : BitVec width) → Decidable (updated.shMemaddrs address) :=
  fun address => hdom ▸ shMemDec address

/-- Transport the explicit deciders across HOL `set_var`, whose exact-carrier
    update changes only `locals`. The projection equalities are kernel-checked
    by the corresponding state-update lemmas. This transport helper has no
    separate HOL declaration. -/
def crepSetVarMemDec {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (address : BitVec width) → Decidable (state.memaddrs address))
    (name : Nat) (value : HolWordLab width) :
    (address : BitVec width) →
      Decidable ((CrepSemHOLState.setVar name value state).memaddrs address) :=
  crepMemDecTransport (base := state) (updated := CrepSemHOLState.setVar name value state)
    (by simp) memDec

/-- Shared-memory decider transport across HOL `set_var`; Flapjack-only, with
    no separate HOL declaration. -/
def crepSetVarShMemDec {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (shMemDec : (address : BitVec width) → Decidable (state.shMemaddrs address))
    (name : Nat) (value : HolWordLab width) :
    (address : BitVec width) →
      Decidable ((CrepSemHOLState.setVar name value state).shMemaddrs address) :=
  crepShMemDecTransport
    (base := state) (updated := CrepSemHOLState.setVar name value state) (by simp) shMemDec

/-- Flapjack-only typed bridge exercising the exact recursive evaluator after
    HOL `set_var`, with both explicit domain deciders transported to the updated
    local state. It is infrastructure only and has no separate HOL declaration. -/
def evalCrepSemHOLProgAfterSetVar {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (address : BitVec width) → Decidable (state.memaddrs address))
    (shMemDec : (address : BitVec width) → Decidable (state.shMemaddrs address))
    (name : Nat) (value : HolWordLab width) (program : CrepProgHOL width) :=
  evalCrepSemHOLProg (CrepSemHOLState.setVar name value state)
    (crepSetVarMemDec state memDec name value)
    (crepSetVarShMemDec state shMemDec name value) program

/-- Transport an explicit decider across `fix_clock`; this helper exposes the
    projection equality even when the step state itself came from evaluation.
    This Flapjack helper has no separate HOL declaration. -/
def crepFixClockMemDec {width : Nat} [NeZero width] {σ : Type} {β : Type}
    (state : CrepSemHOLState width σ) (step : β × CrepSemHOLState width σ)
    (memDec : (address : BitVec width) → Decidable (step.2.memaddrs address)) :
    (address : BitVec width) →
      Decidable ((fixClockCrepSemHOL state step).2.memaddrs address) :=
  crepMemDecTransport (base := step.2)
    (updated := (fixClockCrepSemHOL state step).2) (by simp) memDec

/-- Shared-memory decider transport across `fix_clock`; Flapjack-only, with no
    separate HOL declaration. -/
def crepFixClockShMemDec {width : Nat} [NeZero width] {σ : Type} {β : Type}
    (state : CrepSemHOLState width σ) (step : β × CrepSemHOLState width σ)
    (shMemDec : (address : BitVec width) → Decidable (step.2.shMemaddrs address)) :
    (address : BitVec width) →
      Decidable ((fixClockCrepSemHOL state step).2.shMemaddrs address) :=
  crepShMemDecTransport (base := step.2)
    (updated := (fixClockCrepSemHOL state step).2) (by simp) shMemDec

/-- Flapjack-only typed bridge exercising exact recursive evaluation after a
    `fix_clock` result state, reusing explicit deciders from the step state. It
    has no separate HOL declaration. -/
def evalCrepSemHOLProgAfterFixClock {width : Nat} [NeZero width] {σ : Type} {β : Type}
    (state : CrepSemHOLState width σ) (step : β × CrepSemHOLState width σ)
    (memDec : (address : BitVec width) → Decidable (step.2.memaddrs address))
    (shMemDec : (address : BitVec width) → Decidable (step.2.shMemaddrs address))
    (program : CrepProgHOL width) :=
  evalCrepSemHOLProg (fixClockCrepSemHOL state step).2
    (crepFixClockMemDec state step memDec)
    (crepFixClockShMemDec state step shMemDec) program

/-- Transport the input-state deciders to the exact result state of a `Seq`
    first command after `fix_clock`. This composes the evaluator's domain
    preservation with the clock projection equation and type-locks the exact
    dependent `DecidablePred` required by a recursive evaluation. Flapjack-only,
    with no separate HOL declaration. -/
def crepSeqStepMemDec {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (address : BitVec width) → Decidable (state.memaddrs address))
    (shMemDec : (address : BitVec width) → Decidable (state.shMemaddrs address))
    (first : CrepProgHOL width) :
    (address : BitVec width) →
      Decidable ((fixClockCrepSemHOL state
        (evalCrepSemHOLProg state memDec shMemDec first)).2.memaddrs address) :=
  crepMemDecTransport (base := state)
    (updated := (fixClockCrepSemHOL state
      (evalCrepSemHOLProg state memDec shMemDec first)).2)
    (by
      simp only [fixClockCrepSemHOL_memaddrs]
      exact (evalCrepSemHOLProg_preserves_memaddrs state memDec shMemDec first).symm) memDec

/-- Shared-memory decider transport for the `Seq` first-command step;
    Flapjack-only, with no separate HOL declaration. -/
def crepSeqStepShMemDec {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (address : BitVec width) → Decidable (state.memaddrs address))
    (shMemDec : (address : BitVec width) → Decidable (state.shMemaddrs address))
    (first : CrepProgHOL width) :
    (address : BitVec width) →
      Decidable ((fixClockCrepSemHOL state
        (evalCrepSemHOLProg state memDec shMemDec first)).2.shMemaddrs address) :=
  crepShMemDecTransport (base := state)
    (updated := (fixClockCrepSemHOL state
      (evalCrepSemHOLProg state memDec shMemDec first)).2)
    (by
      simp only [fixClockCrepSemHOL_shMemaddrs]
      exact (evalCrepSemHOLProg_preserves_shMemaddrs state memDec shMemDec first).symm) shMemDec

/-- Flapjack-only typed `Seq` recursive-call bridge. The state is precisely
    the clamped result of the first command, while each membership procedure
    is the input-state decider transported via the evaluator/fix_clock domain
    equalities above. It has no separate HOL declaration. -/
def evalCrepSemHOLProgAfterSeqStep {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (address : BitVec width) → Decidable (state.memaddrs address))
    (shMemDec : (address : BitVec width) → Decidable (state.shMemaddrs address))
    (first second : CrepProgHOL width) :=
  evalCrepSemHOLProg
    (fixClockCrepSemHOL state (evalCrepSemHOLProg state memDec shMemDec first)).2
    (crepSeqStepMemDec state memDec shMemDec first)
    (crepSeqStepShMemDec state memDec shMemDec first) second

/-- Flapjack-only normal-branch equation for the exact HOL `Seq` evaluator.
Given an explicit ordinary first-step result, this exposes the recursive
call on precisely the clock-clamped, domain-stamped state used by
`crepSem$evaluate` (`crepSemScript.sml:300-303`). The dependent match in
`evalCrepSemHOLProg_seq` otherwise obscures this rewrite during list
induction. This equation is evaluator infrastructure, not a separate HOL
declaration. -/
theorem evalCrepSemHOLProg_seq_normal_of_eval_eq {width : Nat} [NeZero width]
    {σ : Type} (state : CrepSemHOLState width σ)
    (memDec : (address : BitVec width) → Decidable (state.memaddrs address))
    (shMemDec : (address : BitVec width) → Decidable (state.shMemaddrs address))
    (first second : CrepProgHOL width) (stepState : CrepSemHOLState width σ)
    (hfirst : evalCrepSemHOLProg state memDec shMemDec first = (none, stepState)) :
    evalCrepSemHOLProg state memDec shMemDec (.seq first second) =
      evalCrepSemHOLProg
        (crepStampExactDomains state
          (fixClockCrepSemHOL state
            ((none : Option (CrepResultHOLExact width)), stepState)).2)
    memDec shMemDec second := by
  rw [evalCrepSemHOLProg_seq]
  rw [hfirst]
  simp [fixClockCrepSemHOL]

/-! ## No-decider clause equations for the non-recursive fragment

These restate the named `evaluate_def` clause equations over the public
no-extra-argument entry point `evalCrepSemHOLProgExact`, whose classical
`DecidablePred` instances are invisible in the result
(`evalCrepSemHOLProgExact_eq_core`). Each equation therefore has HOL's
state/program-only interface. They are declaration-local, UNTAGGED
infrastructure: the whole `evaluate_def` tag still awaits the recursive-clause
disposition (the recursive calls thread the base-state decision procedures
through derived/stamped states); tags are HOLD pending source review of the
clause set and carriers. -/

/-- HOL `evaluate (Break n, s)` (`crepSemScript.sml:309`) over the no-decider
    interface. -/
theorem evalCrepSemHOLProgExact_break {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (label : Nat) :
    evalCrepSemHOLProgExact state (.break label : CrepProgHOL width) =
      (some (.break label), state) := by
  simp only [evalCrepSemHOLProgExact]
  exact evalCrepSemHOLProg_break state _ _ label

/-- HOL `evaluate (Continue n, s)` (`crepSemScript.sml:310`) over the no-decider
    interface. -/
theorem evalCrepSemHOLProgExact_continue {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (label : Nat) :
    evalCrepSemHOLProgExact state (.continue label : CrepProgHOL width) =
      (some (.continue label), state) := by
  simp only [evalCrepSemHOLProgExact]
  exact evalCrepSemHOLProg_continue state _ _ label

/-- HOL `evaluate (Raise eid, s)` (`crepSemScript.sml:326`) over the no-decider
    interface. -/
theorem evalCrepSemHOLProgExact_raise {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (exception : BitVec width) :
    evalCrepSemHOLProgExact state (.raise exception : CrepProgHOL width) =
      (some (.exception exception), CrepSemHOLState.emptyLocals state) := by
  simp only [evalCrepSemHOLProgExact]
  exact evalCrepSemHOLProg_raise state _ _ exception

/-- HOL `evaluate (Tick, s)` (`crepSemScript.sml:327-329`) over the no-decider
    interface. -/
theorem evalCrepSemHOLProgExact_tick {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    evalCrepSemHOLProgExact state (.tick : CrepProgHOL width) =
      (if state.clock = 0 then (some .timeOut, CrepSemHOLState.emptyLocals state)
       else (none, decClockCrepSemHOL state)) := by
  simp only [evalCrepSemHOLProgExact]
  exact evalCrepSemHOLProg_tick state _ _

/-- HOL `evaluate (Primitive lhss pop rhss, s)` (`crepSemScript.sml:250-262`)
    over the no-decider interface. -/
theorem evalCrepSemHOLProgExact_primitive {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (names : List Nat) (operator : PrimOp)
    (args : List Nat) :
    evalCrepSemHOLProgExact state
        (.primitive names operator args : CrepProgHOL width) =
      (match args.mapM state.locals.lookup with
       | some ws =>
           match crepPrimopHOLExact operator ws with
           | some results =>
               if names.length = results.length &&
                  names.all (fun v => (state.locals.lookup v).isSome) &&
                  names.Nodup then
                 (none, { state with
                   locals := state.locals.updateListEq (names.zip results) })
               else (some .error, state)
           | none => (some .error, state)
       | none => (some .error, state)) := by
  simp only [evalCrepSemHOLProgExact]
  exact evalCrepSemHOLProg_primitive state _ _ names operator args

/-- HOL `evaluate (Assign v src, s)` (`crepSemScript.sml:257-262`) over the
    no-decider interface. -/
theorem evalCrepSemHOLProgExact_assign {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (name : Nat) (src : CrepExpHOL width) :
    evalCrepSemHOLProgExact state (.assign name src : CrepProgHOL width) =
      (match crepExactEvalExp state
               (fun a => Classical.propDecidable (state.memaddrs a)) src with
       | none => (some .error, state)
       | some w =>
           match state.locals.lookup name with
           | some _ => (none, CrepSemHOLState.setVar name w state)
           | none => (some .error, state)) := by
  rw [evalCrepSemHOLProgExact_eq_core state (.assign name src)
    (fun a => Classical.propDecidable (state.memaddrs a))
    (fun a => Classical.propDecidable (state.shMemaddrs a))]
  exact evalCrepSemHOLProg_assign state _ _ name src

/-- HOL `evaluate (Store dst src, s)` (`crepSemScript.sml:263-269`) over the
    no-decider interface. -/
theorem evalCrepSemHOLProgExact_store {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (dst src : CrepExpHOL width) :
    evalCrepSemHOLProgExact state (.store dst src : CrepProgHOL width) =
      (match crepExactEvalExp state
               (fun a => Classical.propDecidable (state.memaddrs a)) dst,
             crepExactEvalExp state
               (fun a => Classical.propDecidable (state.memaddrs a)) src with
       | some (.word account), some w =>
           match (fun a => Classical.propDecidable (state.memaddrs a)) account with
           | .isTrue _ =>
               (none, { state with memory := fun current =>
                 if current = account then w else state.memory current })
           | .isFalse _ => (some .error, state)
       | _, _ => (some .error, state)) := by
  rw [evalCrepSemHOLProgExact_eq_core state (.store dst src)
    (fun a => Classical.propDecidable (state.memaddrs a))
    (fun a => Classical.propDecidable (state.shMemaddrs a))]
  exact evalCrepSemHOLProg_store state _ _ dst src

/-- HOL `evaluate (Store32 dst src, s)` (`crepSemScript.sml:274-280`) over the
    no-decider interface. -/
theorem evalCrepSemHOLProgExact_store32 {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (dst src : CrepExpHOL width) :
    evalCrepSemHOLProgExact state (.store32 dst src : CrepProgHOL width) =
      (match crepExactEvalExp state
               (fun a => Classical.propDecidable (state.memaddrs a)) dst,
             crepExactEvalExp state
               (fun a => Classical.propDecidable (state.memaddrs a)) src with
       | some (.word address), some (.word w) =>
           match crepExactMemStore32 state
                   (fun a => Classical.propDecidable (state.memaddrs a))
                   address (BitVec.ofNat 32 w.toNat) with
           | some memory => (none, { state with memory := memory })
           | none => (some .error, state)
       | _, _ => (some .error, state)) := by
  rw [evalCrepSemHOLProgExact_eq_core state (.store32 dst src)
    (fun a => Classical.propDecidable (state.memaddrs a))
    (fun a => Classical.propDecidable (state.shMemaddrs a))]
  exact evalCrepSemHOLProg_store32 state _ _ dst src

/-- HOL `evaluate (StoreByte dst src, s)` (`crepSemScript.sml:281-287`) over the
    no-decider interface. -/
theorem evalCrepSemHOLProgExact_storeByte {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (dst src : CrepExpHOL width) :
    evalCrepSemHOLProgExact state (.storeByte dst src : CrepProgHOL width) =
      (match crepExactEvalExp state
               (fun a => Classical.propDecidable (state.memaddrs a)) dst,
             crepExactEvalExp state
               (fun a => Classical.propDecidable (state.memaddrs a)) src with
       | some (.word address), some (.word w) =>
           match crepExactMemStoreByte state
                   (fun a => Classical.propDecidable (state.memaddrs a))
                   address (UInt8.ofNat w.toNat) with
           | some memory => (none, { state with memory := memory })
           | none => (some .error, state)
       | _, _ => (some .error, state)) := by
  rw [evalCrepSemHOLProgExact_eq_core state (.storeByte dst src)
    (fun a => Classical.propDecidable (state.memaddrs a))
    (fun a => Classical.propDecidable (state.shMemaddrs a))]
  exact evalCrepSemHOLProg_storeByte state _ _ dst src

/-- HOL `evaluate (StoreGlob dst src, s)` (`crepSemScript.sml:288-291`) over the
    no-decider interface. -/
theorem evalCrepSemHOLProgExact_storeGlob {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (dst : BitVec 5) (src : CrepExpHOL width) :
    evalCrepSemHOLProgExact state (.storeGlob dst src : CrepProgHOL width) =
      (match crepExactEvalExp state
               (fun a => Classical.propDecidable (state.memaddrs a)) src with
       | some w => (none, CrepSemHOLState.setGlobals dst w state)
       | none => (some .error, state)) := by
  rw [evalCrepSemHOLProgExact_eq_core state (.storeGlob dst src)
    (fun a => Classical.propDecidable (state.memaddrs a))
    (fun a => Classical.propDecidable (state.shMemaddrs a))]
  exact evalCrepSemHOLProg_storeGlob state _ _ dst src

/-- HOL `evaluate (Return es, s)` (`crepSemScript.sml:324-325`) over the
    no-decider interface. -/
theorem evalCrepSemHOLProgExact_return {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (values : List (CrepExpHOL width)) :
    evalCrepSemHOLProgExact state (.return values : CrepProgHOL width) =
      (match values.mapM (@evalCrepSemHOLExp width ‹NeZero width› σ state
                 (fun a => Classical.propDecidable (state.memaddrs a))) with
       | some ws => (some (.return ws), CrepSemHOLState.emptyLocals state)
       | none => (some .error, state)) := by
  rw [evalCrepSemHOLProgExact_eq_core state (.return values)
    (fun a => Classical.propDecidable (state.memaddrs a))
    (fun a => Classical.propDecidable (state.shMemaddrs a))]
  exact evalCrepSemHOLProg_return state _ _ values



/-! ## No-decider clause equations for the recursive fragment

These restate the named `evaluate_def` recursive-clause equations over the
public no-extra-argument entry point `evalCrepSemHOLProgExact`. The recursive
calls of the core evaluator thread the base state's explicit domain decisions
through derived states (`fixClockCrepSemHOL`, `decClockCrepSemHOL`,
`crepStampExactDomains`), all of which preserve `memaddrs`/`shMemaddrs`; the
`crepStampExactDomains` normalization makes the base decisions definitionally
valid for the stamped state, so each recursive call folds to
`evalCrepSemHOLProgExact`. Declaration-local, UNTAGGED infrastructure. The
enclosing `evaluate_def` tag still awaits source review of the clause set and
carriers (tags are HOLD). -/

/-- HOL `evaluate (If e c1 c2, s)` (`crepSemScript.sml:304-308`) over the no-decider interface. -/
theorem evalCrepSemHOLProgExact_ite {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (condition : CrepExpHOL width)
    (thenBranch elseBranch : CrepProgHOL width) :
    evalCrepSemHOLProgExact state (.ite condition thenBranch elseBranch) =
      (match crepExactEvalExp state
               (fun a => Classical.propDecidable (state.memaddrs a)) condition with
       | some (.word w) =>
           if w ≠ 0 then evalCrepSemHOLProgExact state thenBranch
           else evalCrepSemHOLProgExact state elseBranch
       | _ => (some .error, state)) := by
  simp only [evalCrepSemHOLProgExact]
  exact evalCrepSemHOLProg_ite state _ _ condition thenBranch elseBranch


/-- HOL `evaluate (While e c, s)` (`crepSemScript.sml:313-317`) over the no-decider interface. -/
theorem evalCrepSemHOLProgExact_while {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (condition : CrepExpHOL width)
    (body : CrepProgHOL width) :
    evalCrepSemHOLProgExact state (.while condition body) =
      (match crepExactEvalExp state
               (fun a => Classical.propDecidable (state.memaddrs a)) condition with
       | some (.word w) =>
           if w ≠ 0 then
             if _hclock : state.clock = 0 then
               (some .timeOut, CrepSemHOLState.emptyLocals state)
             else
               let decState := decClockCrepSemHOL state
               let fixed := fixClockCrepSemHOL decState
                 (evalCrepSemHOLProgExact decState body)
               match _hfixed : fixed with
               | (none, loopState) =>
                   evalCrepSemHOLProgExact (crepStampExactDomains state loopState)
                     (.while condition body)
               | (some (.continue 0), loopState) =>
                   evalCrepSemHOLProgExact (crepStampExactDomains state loopState)
                     (.while condition body)
               | (some (.break 0), loopState) => (none, loopState)
               | (result, loopState) => (exitLoopCrepResult result, loopState)
           else (none, state)
       | _ => (some .error, state)) := by
  simp only [evalCrepSemHOLProgExact]
  exact evalCrepSemHOLProg_while state _ _ condition body


/-- HOL `evaluate (ShMem op name e, s)` (`crepSemScript.sml:384-394`) over the no-decider interface. -/
theorem evalCrepSemHOLProgExact_shMem {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (operator : CrepMemOp) (name : Nat)
    (address : CrepExpHOL width) :
    evalCrepSemHOLProgExact state (.shMem operator name address) =
      (match crepExactEvalExp state
               (fun a => Classical.propDecidable (state.memaddrs a)) address with
       | some (.word addressValue) =>
           if crepIsLoadMemOp operator then
             match state.locals.lookup name with
             | some _ => crepShMemLoadHOL operator name addressValue state
                 (fun a => Classical.propDecidable (state.shMemaddrs a))
             | none => (some .error, state)
           else
             match state.locals.lookup name with
             | some (.word _) => crepShMemStoreHOL operator name addressValue state
                 (fun a => Classical.propDecidable (state.shMemaddrs a))
             | _ => (some .error, state)
       | _ => (some .error, state)) := by
  simp only [evalCrepSemHOLProgExact]
  exact evalCrepSemHOLProg_shMem state _ _ operator name address


/-- HOL `evaluate (ExtCall ffi_index ptr1 len1 ptr2 len2, s)` (`crepSemScript.sml:367-379`) over the no-decider interface. -/
theorem evalCrepSemHOLProgExact_extCall {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (function : MlString)
    (configuration configurationLength array arrayLength : Nat) :
    evalCrepSemHOLProgExact state
        (.extCall function configuration configurationLength array arrayLength) =
      (match state.locals.lookup configurationLength, state.locals.lookup configuration,
             state.locals.lookup arrayLength, state.locals.lookup array with
       | some (.word configLength), some (.word configAddress),
         some (.word arrayLengthValue), some (.word arrayAddress) =>
           match readBytearrayWordHOL (byteWidth := 8) configAddress configLength.toNat
                   (crepExactMemLoadByteWord8 state
                     (fun a => Classical.propDecidable (state.memaddrs a))),
                 readBytearrayWordHOL (byteWidth := 8) arrayAddress arrayLengthValue.toNat
                   (crepExactMemLoadByteWord8 state
                     (fun a => Classical.propDecidable (state.memaddrs a))) with
           | some configBytes, some arrayBytes =>
               match callFFIHOL state.ffi (.extCall function)
                   configBytes arrayBytes with
               | .final event => (some (.finalFfi event), state)
               | .ret newFfi newBytes =>
                   (none, { state with
                     memory := crepExactWriteBytearrayWord8 state
                       (fun a => Classical.propDecidable (state.memaddrs a))
                       arrayAddress newBytes,
                     ffi := newFfi })
           | _, _ => (some .error, state)
       | _, _, _, _ => (some .error, state)) := by
  simp only [evalCrepSemHOLProgExact]
  exact evalCrepSemHOLProg_extCall state _ _ function configuration configurationLength array arrayLength

/-- HOL `evaluate (Call ret function arguments, s)`
    (`crepSemScript.sml:330-357`) over the no-decider interface. Matching HOL's
    `proceed` helper is inlined; the equality holds because the derived call /
    handler states preserve `memaddrs`/`shMemaddrs` definitionally. -/
theorem evalCrepSemHOLProgExact_call {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (returnInfo : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (function : MlString) (arguments : List (CrepExpHOL width)) :
    evalCrepSemHOLProgExact state (.call returnInfo function arguments) =
      (match arguments.mapM (@evalCrepSemHOLExp width ‹NeZero width› σ state
               (fun a => Classical.propDecidable (state.memaddrs a))) with
       | none => (some .error, state)
       | some values =>
           match state.code.lookup function with
           | none => (some .error, state)
           | some (parameters, body) =>
               if parameters.length = values.length && parameters.Nodup then
                 let proceed : Option (CrepResultHOLExact width) ×
                     CrepSemHOLState width σ :=
                   if _hclock : state.clock = 0 then
                     (some .timeOut, CrepSemHOLState.emptyLocals state)
                   else
                     let calleeLocals :=
                       HolFiniteMapExact.empty.updateList (parameters.zip values)
                     let callee : CrepSemHOLState width σ :=
                       { state with locals := calleeLocals }
                     let decCallee := decClockCrepSemHOL callee
                     let fixed := fixClockCrepSemHOL decCallee
                       (evalCrepSemHOLProgExact decCallee body)
                     match _hfixed : fixed with
                     | (none, bodyState) => (some .error, bodyState)
                     | (some (.break _), bodyState) => (some .error, bodyState)
                     | (some (.continue _), bodyState) => (some .error, bodyState)
                     | (some (.return retvs), bodyState) =>
                         match returnInfo with
                         | none => (some (.return retvs),
                             CrepSemHOLState.emptyLocals bodyState)
                         | some (rts, _) =>
                             if retvs.length ≠ rts.length then
                               (some .error, bodyState)
                             else
                              match rts.mapM state.locals.lookup with
                              | some _ => (none, { bodyState with
                                  locals := state.locals.updateListEq
                                    (rts.zip retvs) })
                              | none => (some .error, bodyState)
                     | (some (.exception eid), bodyState) =>
                         match returnInfo with
                         | none => (some (.exception eid),
                             CrepSemHOLState.emptyLocals bodyState)
                         | some (_, none) => (some (.exception eid),
                             CrepSemHOLState.emptyLocals bodyState)
                         | some (_, some (eid', handlerBody)) =>
                             let handlerState : CrepSemHOLState width σ :=
                               crepStampExactDomains state
                                 { bodyState with locals := state.locals }
                             if eid = eid' then
                               evalCrepSemHOLProgExact handlerState handlerBody
                             else (some (.exception eid),
                               CrepSemHOLState.emptyLocals bodyState)
                     | (some result, bodyState) =>
                         (some result, CrepSemHOLState.emptyLocals bodyState)
                 match returnInfo with
                 | some (rts, _) => if rts.Nodup then proceed else (some .error, state)
                 | none => proceed
               else (some .error, state)) := by
  simp only [evalCrepSemHOLProgExact]
  exact evalCrepSemHOLProg_call state _ _ returnInfo function arguments

/-!
## Current status of the exact `crepSem$evaluate_def` port

Declaration-local status note for beads `flapjack-4ac.5.16.5`, `flapjack-4ac.5.16.5.13.1`,
`flapjack-4ac.5.16.5.19`, `flapjack-4ac.5.16.5.20` and `flapjack-4ac.5.16.5.22`.

* **Carrier placement.** The finite-map owner `CrepSemHOLState` is reached through
  the transitive import `CrepSem/HOLState.lean`. `AGENTS.md` permits an imported owner
  together with an evaluator-local witness, and this module declares one in
  `namespace CrepSemShMemExact`
  (`CrepSemShMemExact.holFmapAsFiniteSupportWitness`, a re-export of the canonical
  `CrepSemHOLState.holFmapAsFiniteSupportWitness` roundtrip). The reference checker
  resolves the owner from the tagged declaration's own signature and binds the
  `[NeZero <width>]` discharge and the `BitVec <width>` field to the same owning
  declaration and the same width identifier.
* **Word dimension / FFI universe.** HOL's `'a word` (dimension `dimindex (:α)`)
  translates to `BitVec width`, and `'ffi ffi_state` to `HolFfiState σ` with
  `σ : Type`. The qualifier `(words_as_type_indexed_bitvec)` records this and is
  implemented in `Flapjack/HolRef.lean` and `scripts/check-hol-refs.py` (under
  coordinator review). It accepts a literal `BitVec <width>` signature, or a
  reviewed width-indexed carrier (local or imported) whose own header carries
  `[NeZero <width>]` and which mentions `BitVec <width>`.
* **Evaluator tag.** `evalCrepSemHOLProg` / `evalCrepSemHOLProgExact` and the named
  clause equations remain **untagged** pending source review of the clause set and
  carriers. The eventual tag cites
  `cakeml/pancake/semantics/crepSemScript.sml:240` (the rewritten equation is
  rebound at `:443`) with `(fmap_as_finite_support := [locals, globals, code])`
  and, once approved, `(words_as_type_indexed_bitvec)` under the combined manifest
  status `reviewed_fmap_as_finite_support_words_as_type_indexed_bitvec`. The clause
  signatures name `CrepSemHOLState`/`CrepProgHOL` rather than a literal `BitVec`;
  the carrier route above is what admits the word translation for them.
-/
/-- Flapjack-specific, unstamped `Seq` equation for the no-decider exact
evaluator. HOL `evaluate_def` at `crepSemScript.sml:303-306` evaluates the first
command, applies `fix_clock`, then evaluates the second command on that exact
fixed state when the result is `NONE`; otherwise it returns the fixed pair.
The finite evaluator core internally restates domain deciders with
`crepStampExactDomains`, but `evalCrepSemHOLProg_preserves_domains` and
`crepStampExactDomains_eq_self` show that stamp is identity on the recursive
state, so it is absent from this theorem's statement. This theorem remains
untagged: its Lean carrier uses the finite-support map representation and its
qualifier/tag eligibility is still under review. -/
theorem evalCrepSemHOLProgExact_seq {width : Nat} [NeZero width]
    {σ : Type} (state : CrepSemHOLState width σ)
    (first second : CrepProgHOL width) :
    evalCrepSemHOLProgExact state (.seq first second) =
      (let step := fixClockCrepSemHOL state
        (evalCrepSemHOLProgExact state first)
       match step with
       | (none, stepState) => evalCrepSemHOLProgExact stepState second
       | (some _, _) => step) := by
  classical
  let memDec : (a : BitVec width) → Decidable (state.memaddrs a) :=
    fun a => Classical.propDecidable (state.memaddrs a)
  let shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a) :=
    fun a => Classical.propDecidable (state.shMemaddrs a)
  let firstResult := evalCrepSemHOLProg state memDec shMemDec first
  have hFirstExact :
      evalCrepSemHOLProgExact state first = firstResult := by
    dsimp [firstResult]
    exact evalCrepSemHOLProgExact_eq_core state first memDec shMemDec
  have hSeqExact :
      evalCrepSemHOLProgExact state (.seq first second) =
        evalCrepSemHOLProg state memDec shMemDec (.seq first second) :=
    evalCrepSemHOLProgExact_eq_core state (.seq first second) memDec shMemDec
  rw [hSeqExact, evalCrepSemHOLProg_seq, hFirstExact]
  dsimp only [firstResult]
  cases hFirst : evalCrepSemHOLProg state memDec shMemDec first with
  | mk result firstState =>
      cases result with
      | none =>
          simp only [fixClockCrepSemHOL]
          let stepState : CrepSemHOLState width σ :=
            (fixClockCrepSemHOL state
              ((none : Option (CrepResultHOLExact width)), firstState)).2
          have hDomains := evalCrepSemHOLProg_preserves_domains
            state memDec shMemDec first
          simp only [CrepDomainsPreserved] at hDomains
          rw [hFirst] at hDomains
          have hStamp : crepStampExactDomains state stepState = stepState := by
            apply crepStampExactDomains_eq_self
            · simp only [stepState, fixClockCrepSemHOL_memaddrs]
              exact hDomains.1
            · simp only [stepState, fixClockCrepSemHOL_shMemaddrs]
              exact hDomains.2
          change evalCrepSemHOLProg
              (crepStampExactDomains state stepState) memDec shMemDec second =
            evalCrepSemHOLProgExact stepState second
          have hSecondStamped :
              evalCrepSemHOLProgExact (crepStampExactDomains state stepState) second =
                evalCrepSemHOLProg (crepStampExactDomains state stepState)
                  memDec shMemDec second := by
            exact evalCrepSemHOLProgExact_eq_core
              (crepStampExactDomains state stepState) second memDec shMemDec
          calc
            evalCrepSemHOLProg
                (crepStampExactDomains state stepState) memDec shMemDec second =
              evalCrepSemHOLProgExact (crepStampExactDomains state stepState) second :=
                hSecondStamped.symm
            _ = evalCrepSemHOLProgExact stepState second :=
              congrArg (fun s => evalCrepSemHOLProgExact s second) hStamp
      | some result =>
          simp only [fixClockCrepSemHOL]

/-- Flapjack-specific unstamped no-decider restatement of HOL `While` at
`crepSemScript.sml:314-325`. No separate HOL declaration exists for this
public evaluator equation. It preserves the zero-clock timeout, false
condition, `Continue 0`/normal loop re-entry, `Break 0`, and `exit_loop`
branches. The evaluator core stamps recursive loop states so it can reuse
explicit domain decisions; body domain preservation and `fix_clock` projection
show that stamp is identity here, so the public equation has no stamp and no
domain-preservation premise. It remains untagged while the finite-map carrier
qualifier policy is reviewed. -/
theorem evalCrepSemHOLProgExact_while_unstamped {width : Nat} [NeZero width]
    {σ : Type} (state : CrepSemHOLState width σ) (condition : CrepExpHOL width)
    (body : CrepProgHOL width) :
    evalCrepSemHOLProgExact state (.while condition body) =
      (match crepExactEvalExp state
          (fun a => Classical.propDecidable (state.memaddrs a)) condition with
       | some (.word w) =>
           if w ≠ 0 then
             if _hclock : state.clock = 0 then
               (some .timeOut, CrepSemHOLState.emptyLocals state)
             else
               let decState := decClockCrepSemHOL state
               let fixed := fixClockCrepSemHOL decState
                 (evalCrepSemHOLProgExact decState body)
               match _hfixed : fixed with
               | (none, loopState) =>
                   evalCrepSemHOLProgExact loopState (.while condition body)
               | (some (.continue 0), loopState) =>
                   evalCrepSemHOLProgExact loopState (.while condition body)
               | (some (.break 0), loopState) => (none, loopState)
               | (result, loopState) => (exitLoopCrepResult result, loopState)
           else (none, state)
       | _ => (some .error, state)) := by
  classical
  let memDec : (a : BitVec width) → Decidable (state.memaddrs a) :=
    fun a => Classical.propDecidable (state.memaddrs a)
  let shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a) :=
    fun a => Classical.propDecidable (state.shMemaddrs a)
  let bodyResult := evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec body
  let fixed := fixClockCrepSemHOL (decClockCrepSemHOL state) bodyResult
  have hTop :
      evalCrepSemHOLProgExact state (.while condition body) =
        evalCrepSemHOLProg state memDec shMemDec (.while condition body) :=
    evalCrepSemHOLProgExact_eq_core state (.while condition body) memDec shMemDec
  have hBody :
      evalCrepSemHOLProgExact (decClockCrepSemHOL state) body = bodyResult := by
    dsimp [bodyResult]
    exact evalCrepSemHOLProgExact_eq_core (decClockCrepSemHOL state) body memDec shMemDec
  have hBodyDomains :=
    evalCrepSemHOLProg_preserves_domains (decClockCrepSemHOL state) memDec shMemDec body
  simp only [CrepDomainsPreserved] at hBodyDomains
  have hStampFixed (result : Option (CrepResultHOLExact width))
      (loopState : CrepSemHOLState width σ) (hfixed : fixed = (result, loopState)) :
      crepStampExactDomains state loopState = loopState := by
    apply crepStampExactDomains_eq_self
    · have hfix : fixClockCrepSemHOL (decClockCrepSemHOL state) bodyResult = (result, loopState) := by
        simpa [fixed] using hfixed
      have hdomains := fixClock_result_domains (decClockCrepSemHOL state) bodyResult result loopState hfix
      calc
        loopState.memaddrs = bodyResult.2.memaddrs := hdomains.1
        _ = (decClockCrepSemHOL state).memaddrs := hBodyDomains.1
        _ = state.memaddrs := rfl
    · have hfix : fixClockCrepSemHOL (decClockCrepSemHOL state) bodyResult = (result, loopState) := by
        simpa [fixed] using hfixed
      have hdomains := fixClock_result_domains (decClockCrepSemHOL state) bodyResult result loopState hfix
      calc
        loopState.shMemaddrs = bodyResult.2.shMemaddrs := hdomains.2
        _ = (decClockCrepSemHOL state).shMemaddrs := hBodyDomains.2
        _ = state.shMemaddrs := rfl
  rw [hTop, evalCrepSemHOLProg_while]
  cases hcondition : crepExactEvalExp state memDec condition with
  | none => rfl
  | some value =>
      cases value with
      | word w =>
          dsimp only
          by_cases hw : w ≠ 0
          · simp only [if_pos hw]
            by_cases hclock : state.clock = 0
            · simp [hclock]
            ·
              rw [hBody]
              cases hfixed : fixClockCrepSemHOL (decClockCrepSemHOL state) bodyResult with
              | mk result loopState =>
                  have hStamp := hStampFixed result loopState hfixed
                  have hLoopEval (loopState' : CrepSemHOLState width σ)
                      (hStamp' : crepStampExactDomains state loopState' = loopState') :
                      evalCrepSemHOLProg (crepStampExactDomains state loopState')
                          memDec shMemDec (.while condition body) =
                        evalCrepSemHOLProgExact loopState' (.while condition body) := by
                    calc
                      evalCrepSemHOLProg (crepStampExactDomains state loopState')
                          memDec shMemDec (.while condition body) =
                        evalCrepSemHOLProgExact (crepStampExactDomains state loopState')
                            (.while condition body) :=
                          evalCrepSemHOLProgExact_eq_core
                            (crepStampExactDomains state loopState') (.while condition body)
                            memDec shMemDec
                      _ = evalCrepSemHOLProgExact loopState' (.while condition body) :=
                        congrArg (fun st => evalCrepSemHOLProgExact st (.while condition body)) hStamp'
                  cases result with
                  | none => simp only [hStamp, hLoopEval]
                  | some value =>
                      cases value with
                      | «continue» label =>
                          cases label with
                          | zero => simp only [hStamp, hLoopEval]
                          | succ _ => rfl
                      | «break» label =>
                          cases label with
                          | zero => rfl
                          | succ _ => rfl
                      | error => rfl
                      | timeOut => rfl
                      | «return» _ => rfl
                      | exception _ => rfl
                      | finalFfi _ => rfl
          · rw [if_neg hw, if_neg hw]

/-- Flapjack-specific unstamped no-decider restatement of HOL `If` at
`crepSemScript.sml:304-308`. No separate HOL declaration exists for this
public evaluator equation. It preserves the zero/nonzero word branch choice
and the Error result for a non-word condition. It remains untagged while the
finite-support carrier qualifier policy is reviewed. -/
theorem evalCrepSemHOLProgExact_ite_unstamped {width : Nat} [NeZero width]
    {σ : Type} (state : CrepSemHOLState width σ) (condition : CrepExpHOL width)
    (thenBranch elseBranch : CrepProgHOL width) :
    evalCrepSemHOLProgExact state (.ite condition thenBranch elseBranch) =
      (match crepExactEvalExp state
          (fun a => Classical.propDecidable (state.memaddrs a)) condition with
       | some (.word w) =>
           if w ≠ 0 then evalCrepSemHOLProgExact state thenBranch
           else evalCrepSemHOLProgExact state elseBranch
       | _ => (some .error, state)) := by
  classical
  let memDec : (a : BitVec width) → Decidable (state.memaddrs a) :=
    fun a => Classical.propDecidable (state.memaddrs a)
  let shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a) :=
    fun a => Classical.propDecidable (state.shMemaddrs a)
  have hTop :
      evalCrepSemHOLProgExact state (.ite condition thenBranch elseBranch) =
        evalCrepSemHOLProg state memDec shMemDec (.ite condition thenBranch elseBranch) :=
    evalCrepSemHOLProgExact_eq_core state (.ite condition thenBranch elseBranch)
      memDec shMemDec
  have hThen : evalCrepSemHOLProgExact state thenBranch =
      evalCrepSemHOLProg state memDec shMemDec thenBranch :=
    evalCrepSemHOLProgExact_eq_core state thenBranch memDec shMemDec
  have hElse : evalCrepSemHOLProgExact state elseBranch =
      evalCrepSemHOLProg state memDec shMemDec elseBranch :=
    evalCrepSemHOLProgExact_eq_core state elseBranch memDec shMemDec
  rw [hTop, evalCrepSemHOLProg_ite]
  cases hcondition : crepExactEvalExp state memDec condition with
  | none => rfl
  | some value =>
      cases value with
      | word w =>
          dsimp only
          by_cases hw : w ≠ 0
          · simp only [if_pos hw, hThen]
          · simp only [if_neg hw, hElse]

/-- Flapjack-specific unstamped no-decider restatement of HOL
`evaluate_def`'s `ShMem` clause at `crepSemScript.sml:292-303`. It evaluates
the address first and accepts only a `Word`; `is_load` selects the load guard
(`FLOOKUP locals v = SOME _`) or the stricter store guard
(`SOME (Word _)`). A failed address or local check returns `Error` with the
input state, while a successful check forwards the corresponding shared-memory
helper's result and state. The helpers use classical domain decisions for the
finite-support carrier. This public no-decider equation has no separate HOL
declaration, and the finite-support carrier qualification remains under review,
so it is intentionally untagged. -/
theorem evalCrepSemHOLProgExact_shMem_unstamped {width : Nat} [NeZero width]
    {σ : Type} (state : CrepSemHOLState width σ)
    (operator : CrepMemOp) (name : Nat) (address : CrepExpHOL width) :
    evalCrepSemHOLProgExact state (.shMem operator name address) =
      (match crepExactEvalExp state
          (fun a => Classical.propDecidable (state.memaddrs a)) address with
       | some (.word addressValue) =>
           if crepIsLoadMemOp operator then
             match state.locals.lookup name with
             | some _ => crepShMemLoadHOL operator name addressValue state
                 (fun a => Classical.propDecidable (state.shMemaddrs a))
             | none => (some .error, state)
           else
             match state.locals.lookup name with
             | some (.word _) => crepShMemStoreHOL operator name addressValue state
                 (fun a => Classical.propDecidable (state.shMemaddrs a))
             | _ => (some .error, state)
       | _ => (some .error, state)) := by
  classical
  let memDec : (a : BitVec width) → Decidable (state.memaddrs a) :=
    fun a => Classical.propDecidable (state.memaddrs a)
  let shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a) :=
    fun a => Classical.propDecidable (state.shMemaddrs a)
  calc
    evalCrepSemHOLProgExact state (.shMem operator name address) =
        evalCrepSemHOLProg state memDec shMemDec (.shMem operator name address) :=
      evalCrepSemHOLProgExact_eq_core state (.shMem operator name address)
        memDec shMemDec
    _ = (match crepExactEvalExp state memDec address with
         | some (.word addressValue) =>
             if crepIsLoadMemOp operator then
               match state.locals.lookup name with
               | some _ => crepShMemLoadHOL operator name addressValue state shMemDec
               | none => (some .error, state)
             else
               match state.locals.lookup name with
               | some (.word _) => crepShMemStoreHOL operator name addressValue state shMemDec
               | _ => (some .error, state)
         | _ => (some .error, state)) :=
      evalCrepSemHOLProg_shMem state memDec shMemDec operator name address
    _ = _ := by rfl

open Flapjack.Basis.Pure.MlString

@[simp] theorem decClockCrepSemHOL_clock' {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    (decClockCrepSemHOL state).clock = state.clock - 1 := rfl

/-- Packed argument of the total evaluator, carrying the two domain decision
    procedures at the exact dependent type required by the state. -/
structure CrepEvalArg (width : Nat) (σ : Type) [NeZero width] where
  state : CrepSemHOLState width σ
  memDec : (a : BitVec width) → Decidable (state.memaddrs a)
  shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)
  program : CrepProgHOL width

/-- General well-founded induction principle for `evalCrepSemHOLProg`,
    matching its `(state.clock, sizeOf program)` lexicographic measure.

    FLAPJACK-SPECIFIC (untagged). The intended HOL original is
    `crepSemScript.sml:440 evaluate_ind[allow_rebind] =
    REWRITE_RULE [fix_clock_evaluate] evaluate_ind`, the auto-generated
    induction principle of the total clocked evaluator. This principle is
    deliberately **not** tagged: (i) its motive carries the two explicit
    domain decision procedures `memDec`/`shMemDec`, whereas HOL `evaluate`
    takes only `(prog, s)`; (ii) the well-founded relation here is
    `Prod.Lex Nat.lt Nat.lt (state.clock, sizeOf program)`, whereas HOL's
    generated relation is the internal `tdefn` measure on `(prog, s)`; and
    (iii) the carrier is `CrepSemHOLState width σ` with `BitVec width` in
    place of HOL `('a,'ffi) crepSem$state` with `'a word`. A faithful tagged
    port is tracked by `flapjack-2de.1.1`. -/
theorem evalCrepSemHOLProg.inductHOL_general {width : Nat} [NeZero width] {σ : Type}
    {motive : (state : CrepSemHOLState width σ) →
      ((a : BitVec width) → Decidable (state.memaddrs a)) →
      ((a : BitVec width) → Decidable (state.shMemaddrs a)) →
      CrepProgHOL width → Prop}
    (step : ∀ state memDec shMemDec program,
      (∀ state' memDec' shMemDec' program',
        Prod.Lex Nat.lt Nat.lt (state'.clock, sizeOf program') (state.clock, sizeOf program) →
        motive state' memDec' shMemDec' program') →
      motive state memDec shMemDec program) :
    ∀ state memDec shMemDec program, motive state memDec shMemDec program := by
  intro state memDec shMemDec program
  let measureArg : CrepEvalArg width σ → Nat × Nat :=
    fun x => (x.state.clock, sizeOf x.program)
  have hwf : WellFounded (InvImage (Prod.Lex Nat.lt Nat.lt) measureArg) :=
    InvImage.wf measureArg
      (Prod.instWellFoundedRelation.wf)
  have hmain : ∀ x : CrepEvalArg width σ,
      motive x.state x.memDec x.shMemDec x.program := by
    intro x
    exact WellFounded.induction hwf x (fun x ih =>
      step x.state x.memDec x.shMemDec x.program (fun state' memDec' shMemDec' program' hlt =>
        ih ⟨state', memDec', shMemDec', program'⟩ hlt))
  exact hmain ⟨state, memDec, shMemDec, program⟩

/-- Per-constructor well-founded induction principle for the exact
    `evalCrepSemHOLProg`, with one case handler per `CrepProgHOL` constructor and
    induction hypotheses for the sub-programs actually passed by the evaluator.

    FLAPJACK-SPECIFIC (untagged). This is a constructor-structured helper, not
    HOL's `evaluate_ind`: several handlers carry extra branch-selector
    hypotheses (e.g. the `Call` body-result/handler equation with `eid = eid'`,
    the `Seq` `fixClockCrepSemHOL` step equation) and every handler threads the
    explicit `memDec`/`shMemDec` deciders. Per the fleet tag policy such
    branch helpers stay untagged; the faithful tagged port is `flapjack-2de.1.1`. -/
theorem evalCrepSemHOLProg.inductHOL {width : Nat} [NeZero width] {σ : Type}
    {motive : (state : CrepSemHOLState width σ) →
      ((a : BitVec width) → Decidable (state.memaddrs a)) →
      ((a : BitVec width) → Decidable (state.shMemaddrs a)) →
      CrepProgHOL width → Prop}
    (hskip : ∀ state memDec shMemDec, motive state memDec shMemDec .skip)
    (hdec_none : ∀ state memDec shMemDec name value body,
      crepExactEvalExp state memDec value = none →
      motive state memDec shMemDec (.dec name value body))
    (hdec_some : ∀ state memDec shMemDec name value body v,
      crepExactEvalExp state memDec value = some v →
      motive (CrepSemHOLState.setVar name v state) memDec shMemDec body →
      motive state memDec shMemDec (.dec name value body))
    (hprimitive : ∀ state memDec shMemDec names operator args,
      motive state memDec shMemDec (.primitive names operator args))
    (hassign : ∀ state memDec shMemDec name src,
      motive state memDec shMemDec (.assign name src))
    (hstore : ∀ state memDec shMemDec dst src,
      motive state memDec shMemDec (.store dst src))
    (hstore32 : ∀ state memDec shMemDec dst src,
      motive state memDec shMemDec (.store32 dst src))
    (hstoreByte : ∀ state memDec shMemDec dst src,
      motive state memDec shMemDec (.storeByte dst src))
    (hstoreGlob : ∀ state memDec shMemDec dst src,
      motive state memDec shMemDec (.storeGlob dst src))
    (hseq_none : ∀ state memDec shMemDec first second,
      motive state memDec shMemDec first →
      (∀ stepState,
        fixClockCrepSemHOL state (evalCrepSemHOLProg state memDec shMemDec first) =
          (none, stepState) →
        motive (crepStampExactDomains state stepState) memDec shMemDec second) →
      motive state memDec shMemDec (.seq first second))
    (hseq_some : ∀ state memDec shMemDec first second,
      motive state memDec shMemDec first →
      motive state memDec shMemDec (.seq first second))
    (hite_then : ∀ state memDec shMemDec condition thenBranch elseBranch w,
      crepExactEvalExp state memDec condition = some (.word w) → w ≠ 0 →
      motive state memDec shMemDec thenBranch →
      motive state memDec shMemDec (.ite condition thenBranch elseBranch))
    (hite_else : ∀ state memDec shMemDec condition thenBranch elseBranch w,
      crepExactEvalExp state memDec condition = some (.word w) → w = 0 →
      motive state memDec shMemDec elseBranch →
      motive state memDec shMemDec (.ite condition thenBranch elseBranch))
    (hite_other : ∀ state memDec shMemDec condition thenBranch elseBranch,
      (∀ w, crepExactEvalExp state memDec condition = some (.word w) → False) →
      motive state memDec shMemDec (.ite condition thenBranch elseBranch))
    (hwhile_timeout : ∀ state memDec shMemDec condition body w,
      crepExactEvalExp state memDec condition = some (.word w) → w ≠ 0 →
      state.clock = 0 →
      motive state memDec shMemDec (.while condition body))
    (hwhile_false : ∀ state memDec shMemDec condition body w,
      crepExactEvalExp state memDec condition = some (.word w) → w = 0 →
      motive state memDec shMemDec (.while condition body))
    (hwhile_other : ∀ state memDec shMemDec condition body,
      (∀ w, crepExactEvalExp state memDec condition = some (.word w) → False) →
      motive state memDec shMemDec (.while condition body))
    (hwhile_none : ∀ state memDec shMemDec condition body w,
      crepExactEvalExp state memDec condition = some (.word w) → w ≠ 0 →
      ¬ state.clock = 0 →
      (∀ loopState,
        fixClockCrepSemHOL (decClockCrepSemHOL state)
          (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec body) =
            (none, loopState) →
        motive (decClockCrepSemHOL state) memDec shMemDec body →
        motive (crepStampExactDomains state loopState) memDec shMemDec
          (.while condition body)) →
      motive state memDec shMemDec (.while condition body))
    (hwhile_continue : ∀ state memDec shMemDec condition body w,
      crepExactEvalExp state memDec condition = some (.word w) → w ≠ 0 →
      ¬ state.clock = 0 →
      (∀ loopState,
        fixClockCrepSemHOL (decClockCrepSemHOL state)
          (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec body) =
            (some (.continue 0), loopState) →
        motive (decClockCrepSemHOL state) memDec shMemDec body →
        motive (crepStampExactDomains state loopState) memDec shMemDec
          (.while condition body)) →
      motive state memDec shMemDec (.while condition body))
    (hwhile_break : ∀ state memDec shMemDec condition body w,
      crepExactEvalExp state memDec condition = some (.word w) → w ≠ 0 →
      ¬ state.clock = 0 →
      (∀ loopState,
        fixClockCrepSemHOL (decClockCrepSemHOL state)
          (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec body) =
            (some (.break 0), loopState) →
        motive (decClockCrepSemHOL state) memDec shMemDec body) →
      motive state memDec shMemDec (.while condition body))
    (hwhile_other' : ∀ state memDec shMemDec condition body w,
      crepExactEvalExp state memDec condition = some (.word w) → w ≠ 0 →
      ¬ state.clock = 0 →
      (∀ result loopState,
        fixClockCrepSemHOL (decClockCrepSemHOL state)
          (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec body) =
            (result, loopState) →
        result ≠ none →
        result ≠ some (.continue 0) →
        result ≠ some (.break 0) →
        motive (decClockCrepSemHOL state) memDec shMemDec body) →
      motive state memDec shMemDec (.while condition body))
    (hbreak : ∀ state memDec shMemDec label,
      motive state memDec shMemDec (.break label))
    (hcontinue : ∀ state memDec shMemDec label,
      motive state memDec shMemDec (.continue label))
    (hcall_args_none : ∀ state memDec shMemDec returnInfo function arguments,
      arguments.mapM (@evalCrepSemHOLExp width ‹NeZero width› σ state memDec) = none →
      motive state memDec shMemDec (.call returnInfo function arguments))
    (hcall_code_none : ∀ state memDec shMemDec returnInfo function arguments values,
      arguments.mapM (@evalCrepSemHOLExp width ‹NeZero width› σ state memDec) = some values →
      state.code.lookup function = none →
      motive state memDec shMemDec (.call returnInfo function arguments))
    (hcall_bad : ∀ state memDec shMemDec returnInfo function arguments values parameters body,
      arguments.mapM (@evalCrepSemHOLExp width ‹NeZero width› σ state memDec) = some values →
      state.code.lookup function = some (parameters, body) →
      (parameters.length ≠ values.length ∨ ¬ parameters.Nodup) →
      motive state memDec shMemDec (.call returnInfo function arguments))
    (hcall_timeout : ∀ state memDec shMemDec returnInfo function arguments values parameters body,
      arguments.mapM (@evalCrepSemHOLExp width ‹NeZero width› σ state memDec) = some values →
      state.code.lookup function = some (parameters, body) →
      parameters.length = values.length → parameters.Nodup → state.clock = 0 →
      motive state memDec shMemDec (.call returnInfo function arguments))
    (hcall_body : ∀ state memDec shMemDec returnInfo function arguments values parameters body,
      arguments.mapM (@evalCrepSemHOLExp width ‹NeZero width› σ state memDec) = some values →
      state.code.lookup function = some (parameters, body) →
      parameters.length = values.length → parameters.Nodup → ¬ state.clock = 0 →
      (∀ rts eid' handlerBody bodyState eid,
        returnInfo = some (rts, some (eid', handlerBody)) →
        fixClockCrepSemHOL
            (decClockCrepSemHOL
              { state with
                locals := HolFiniteMapExact.empty.updateList (parameters.zip values) })
            (evalCrepSemHOLProg
              (decClockCrepSemHOL
                { state with
                  locals := HolFiniteMapExact.empty.updateList (parameters.zip values) })
              memDec shMemDec body) =
          (some (.exception eid), bodyState) →
        eid = eid' →
        motive (crepStampExactDomains state { bodyState with locals := state.locals })
          memDec shMemDec handlerBody) →
      motive
          (decClockCrepSemHOL
            { state with
              locals := HolFiniteMapExact.empty.updateList (parameters.zip values) })
          memDec shMemDec body →
      motive state memDec shMemDec (.call returnInfo function arguments))
    (hextCall : ∀ state memDec shMemDec function configuration configurationLength
        array arrayLength,
      motive state memDec shMemDec
        (.extCall function configuration configurationLength array arrayLength))
    (hraise : ∀ state memDec shMemDec exception,
      motive state memDec shMemDec (.raise exception))
    (hreturn : ∀ state memDec shMemDec values,
      motive state memDec shMemDec (.return values))
    (hshMem : ∀ state memDec shMemDec operator name address,
      motive state memDec shMemDec (.shMem operator name address))
    (htick : ∀ state memDec shMemDec,
      motive state memDec shMemDec .tick) :
    ∀ state memDec shMemDec program, motive state memDec shMemDec program := by
  apply evalCrepSemHOLProg.inductHOL_general
  intro state memDec shMemDec program ih
  cases program with
  | skip => exact hskip state memDec shMemDec
  | dec name value body =>
      cases h : crepExactEvalExp state memDec value with
      | none => exact hdec_none state memDec shMemDec name value body h
      | some v =>
          exact hdec_some state memDec shMemDec name value body v h
            (ih (CrepSemHOLState.setVar name v state) memDec shMemDec body (by
              rw [Prod.lex_def]
              right
              refine ⟨?_, ?_⟩
              · simp [CrepSemHOLState.setVar]
              · simp_wf
                omega))
  | primitive names operator args =>
      exact hprimitive state memDec shMemDec names operator args
  | assign name value => exact hassign state memDec shMemDec name value
  | store dst src => exact hstore state memDec shMemDec dst src
  | store32 dst src => exact hstore32 state memDec shMemDec dst src
  | storeByte dst src => exact hstoreByte state memDec shMemDec dst src
  | storeGlob dst src => exact hstoreGlob state memDec shMemDec dst src
  | seq first second =>
      have hfirst : motive state memDec shMemDec first :=
        ih state memDec shMemDec first (by
          rw [Prod.lex_def]
          right
          exact ⟨rfl, by simp_wf; omega⟩)
      cases hfx : fixClockCrepSemHOL state (evalCrepSemHOLProg state memDec shMemDec first) with
      | mk res stepState =>
        cases res with
        | none =>
            exact hseq_none state memDec shMemDec first second hfirst (fun stepState' hstep => by
              have hclk : stepState'.clock ≤ state.clock :=
                fixClockCrepSemHOL_IMP_LESS_EQ state
                  (evalCrepSemHOLProg state memDec shMemDec first) none stepState' hstep
              exact ih (crepStampExactDomains state stepState') memDec shMemDec second (by
                rw [Prod.lex_def]
                by_cases hlt : stepState'.clock < state.clock
                · left
                  exact hlt
                · right
                  refine ⟨?_, ?_⟩
                  · show stepState'.clock = state.clock; omega
                  · simp_wf; omega))
        | some val =>
            exact hseq_some state memDec shMemDec first second hfirst
  | ite condition thenBranch elseBranch =>
      cases h : crepExactEvalExp state memDec condition with
      | none => exact hite_other state memDec shMemDec condition thenBranch elseBranch (by simp [h])
      | some v =>
          cases v with
          | word w =>
              by_cases hw : w ≠ 0
              · exact hite_then state memDec shMemDec condition thenBranch elseBranch w h hw
                  (ih state memDec shMemDec thenBranch (by
                    rw [Prod.lex_def]; right; exact ⟨rfl, by simp_wf; omega⟩))
              · exact hite_else state memDec shMemDec condition thenBranch elseBranch w h
                  (by
                    by_cases h0 : w = 0
                    · exact h0
                    · exact (hw h0).elim)
                  (ih state memDec shMemDec elseBranch (by
                    rw [Prod.lex_def]; right; exact ⟨rfl, by simp_wf; omega⟩))
  | «while» condition body =>
      cases h : crepExactEvalExp state memDec condition with
      | none => exact hwhile_other state memDec shMemDec condition body (by simp [h])
      | some v =>
          cases v with
          | word w =>
              by_cases hw : w = 0
              · exact hwhile_false state memDec shMemDec condition body w h hw
              · have hwne : w ≠ 0 := fun hh => hw hh
                by_cases hclk : state.clock = 0
                · exact hwhile_timeout state memDec shMemDec condition body w h hwne hclk
                · have hbody : motive (decClockCrepSemHOL state) memDec shMemDec body :=
                    ih (decClockCrepSemHOL state) memDec shMemDec body (by
                      rw [Prod.lex_def]; left
                      simp only [decClockCrepSemHOL_clock']
                      exact Nat.sub_lt (Nat.pos_of_ne_zero hclk) (by omega))
                  cases hf : fixClockCrepSemHOL (decClockCrepSemHOL state)
                      (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec body) with
                  | mk r loopState =>
                    cases r with
                    | none =>
                        refine hwhile_none state memDec shMemDec condition body w h hwne hclk
                          (fun loopState' hfx _ => ?_)
                        have hbnd : loopState'.clock ≤ (decClockCrepSemHOL state).clock :=
                          fixClockCrepSemHOL_IMP_LESS_EQ (decClockCrepSemHOL state)
                            (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec body)
                            none loopState' hfx
                        have hlex : Prod.Lex Nat.lt Nat.lt
                            ((crepStampExactDomains state loopState').clock,
                              sizeOf (CrepProgHOL.while condition body))
                            (state.clock, sizeOf (CrepProgHOL.while condition body)) := by
                          rw [Prod.lex_def]; left
                          simp only [decClockCrepSemHOL_clock'] at hbnd ⊢
                          exact Nat.lt_of_le_of_lt hbnd
                            (Nat.sub_lt (Nat.pos_of_ne_zero hclk) (by omega))
                        exact ih (crepStampExactDomains state loopState') memDec shMemDec
                          (.while condition body) hlex
                    | some res =>
                      cases res with
                      | «continue» label =>
                          by_cases hl : label = 0
                          · subst hl
                            refine hwhile_continue state memDec shMemDec condition body w h hwne hclk
                              (fun loopState' hfx _ => ?_)
                            have hbnd : loopState'.clock ≤ (decClockCrepSemHOL state).clock :=
                              fixClockCrepSemHOL_IMP_LESS_EQ (decClockCrepSemHOL state)
                                (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec body)
                                (some (.continue 0)) loopState' hfx
                            have hlex : Prod.Lex Nat.lt Nat.lt
                                ((crepStampExactDomains state loopState').clock,
                                  sizeOf (CrepProgHOL.while condition body))
                                (state.clock, sizeOf (CrepProgHOL.while condition body)) := by
                              rw [Prod.lex_def]; left
                              simp only [decClockCrepSemHOL_clock'] at hbnd ⊢
                              exact Nat.lt_of_le_of_lt hbnd
                                (Nat.sub_lt (Nat.pos_of_ne_zero hclk) (by omega))
                            exact ih (crepStampExactDomains state loopState') memDec shMemDec
                              (.while condition body) hlex
                          · exact hwhile_other' state memDec shMemDec condition body w h hwne hclk
                              (fun result loopState' _ _ _ _ => hbody)
                      | «break» label =>
                          by_cases hl : label = 0
                          · subst hl
                            exact hwhile_break state memDec shMemDec condition body w h hwne hclk
                              (fun loopState' _ => hbody)
                          · exact hwhile_other' state memDec shMemDec condition body w h hwne hclk
                              (fun result loopState' _ _ _ _ => hbody)
                      | error =>
                          exact hwhile_other' state memDec shMemDec condition body w h hwne hclk
                            (fun result loopState' _ _ _ _ => hbody)
                      | timeOut =>
                          exact hwhile_other' state memDec shMemDec condition body w h hwne hclk
                            (fun result loopState' _ _ _ _ => hbody)
                      | «return» values =>
                          exact hwhile_other' state memDec shMemDec condition body w h hwne hclk
                            (fun result loopState' _ _ _ _ => hbody)
                      | «exception» e =>
                          exact hwhile_other' state memDec shMemDec condition body w h hwne hclk
                            (fun result loopState' _ _ _ _ => hbody)
                      | finalFfi event =>
                          exact hwhile_other' state memDec shMemDec condition body w h hwne hclk
                            (fun result loopState' _ _ _ _ => hbody)
  | «break» label => exact hbreak state memDec shMemDec label
  | «continue» label => exact hcontinue state memDec shMemDec label
  | call returnInfo function arguments =>
      cases hv : arguments.mapM (@evalCrepSemHOLExp width ‹NeZero width› σ state memDec) with
      | none => exact hcall_args_none state memDec shMemDec returnInfo function arguments hv
      | some values =>
          cases hc : state.code.lookup function with
          | none =>
              exact hcall_code_none state memDec shMemDec returnInfo function arguments values hv hc
          | some p =>
              obtain ⟨parameters, body⟩ := p
              by_cases hlen : parameters.length = values.length
              · by_cases hnodup : parameters.Nodup
                · by_cases hclock : state.clock = 0
                  · exact hcall_timeout state memDec shMemDec returnInfo function arguments values
                      parameters body hv hc hlen hnodup hclock
                  · refine hcall_body state memDec shMemDec returnInfo function arguments values
                      parameters body hv hc hlen hnodup hclock ?_ ?_
                    · intro rts eid' handlerBody bodyState eid hri hfx heid
                      have hlex : Prod.Lex Nat.lt Nat.lt
                          ((crepStampExactDomains state
                            { bodyState with locals := state.locals }).clock, sizeOf handlerBody)
                          (state.clock, sizeOf (CrepProgHOL.call returnInfo function arguments)) := by
                        rw [Prod.lex_def]; left
                        have hbnd : bodyState.clock ≤
                            (decClockCrepSemHOL
                              { state with
                                locals := HolFiniteMapExact.empty.updateList
                                  (parameters.zip values) }).clock :=
                          fixClockCrepSemHOL_IMP_LESS_EQ
                            (decClockCrepSemHOL
                              { state with
                                locals := HolFiniteMapExact.empty.updateList
                                  (parameters.zip values) })
                            (evalCrepSemHOLProg
                              (decClockCrepSemHOL
                                { state with
                                  locals := HolFiniteMapExact.empty.updateList
                                    (parameters.zip values) })
                              memDec shMemDec body)
                            (some (.exception eid)) bodyState hfx
                        simp only [decClockCrepSemHOL_clock'] at hbnd ⊢
                        exact Nat.lt_of_le_of_lt hbnd
                          (Nat.sub_lt (Nat.pos_of_ne_zero hclock) (by omega))
                      exact ih (crepStampExactDomains state
                          { bodyState with locals := state.locals }) memDec shMemDec handlerBody hlex
                    · have hlex : Prod.Lex Nat.lt Nat.lt
                          ((decClockCrepSemHOL
                            { state with
                              locals := HolFiniteMapExact.empty.updateList
                                (parameters.zip values) }).clock, sizeOf body)
                          (state.clock, sizeOf (CrepProgHOL.call returnInfo function arguments)) := by
                        rw [Prod.lex_def]; left
                        simp only [decClockCrepSemHOL_clock']
                        exact Nat.sub_lt (Nat.pos_of_ne_zero hclock) (by omega)
                      exact ih (decClockCrepSemHOL
                          { state with
                            locals := HolFiniteMapExact.empty.updateList
                              (parameters.zip values) }) memDec shMemDec body hlex
                · exact hcall_bad state memDec shMemDec returnInfo function arguments values
                    parameters body hv hc (Or.inr hnodup)
              · exact hcall_bad state memDec shMemDec returnInfo function arguments values
                  parameters body hv hc (Or.inl hlen)
  | extCall function configuration configurationLength array arrayLength =>
      exact hextCall state memDec shMemDec function configuration configurationLength array arrayLength
  | «raise» exception => exact hraise state memDec shMemDec exception
  | «return» values => exact hreturn state memDec shMemDec values
  | shMem operator name address => exact hshMem state memDec shMemDec operator name address
  | tick => exact htick state memDec shMemDec
private def CrepClockBounded {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (program : CrepProgHOL width) : Prop :=
  (evalCrepSemHOLProg state memDec shMemDec program).2.clock ≤ state.clock

private theorem decClock_clock_lt {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (h : state.clock ≠ 0) :
    (decClockCrepSemHOL state).clock < state.clock := by
  rw [decClockCrepSemHOL_clock']; omega

private theorem decClock_clock_le {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    (decClockCrepSemHOL state).clock ≤ state.clock := by
  rw [decClockCrepSemHOL_clock']; omega

private theorem fixClock_clock_le {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (step : Option (CrepResultHOLExact width) × CrepSemHOLState width σ) :
    (fixClockCrepSemHOL state step).2.clock ≤ state.clock := by
  cases h : fixClockCrepSemHOL state step with
  | mk r s' => exact fixClockCrepSemHOL_IMP_LESS_EQ state step r s' h

private theorem shMemLoadClockEq {width : Nat} [NeZero width] {σ : Type}
    (operator : CrepMemOp) (name : Nat) (address : BitVec width)
    (state : CrepSemHOLState width σ) [hsh : DecidablePred state.shMemaddrs] :
    (crepShMemLoadHOL operator name address state hsh).2.clock = state.clock := by
  cases h : crepShMemLoadHOL operator name address state hsh with
  | mk r s' =>
    exact crepShMemLoadClock name address (crepShMemByteWidth operator) state r s' h

private theorem shMemStoreClockEq {width : Nat} [NeZero width] {σ : Type}
    (operator : CrepMemOp) (name : Nat) (address : BitVec width)
    (state : CrepSemHOLState width σ) [hsh : DecidablePred state.shMemaddrs] :
    (crepShMemStoreHOL operator name address state hsh).2.clock = state.clock := by
  cases h : crepShMemStoreHOL operator name address state hsh with
  | mk r s' =>
    exact crepShMemStoreClock name address (crepShMemByteWidth operator) state r s' h

set_option linter.unusedVariables false in
theorem crepWhileStep_clock_le {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (condition : CrepExpHOL width) (body : CrepProgHOL width)
    (loopStep : Option (CrepResultHOLExact width) × CrepSemHOLState width σ)
    (hstep : loopStep.2.clock ≤ state.clock)
    (hrec : (evalCrepSemHOLProg (crepStampExactDomains state loopStep.2)
        memDec shMemDec (.while condition body)).2.clock ≤ state.clock) :
    (match hfixed : loopStep with
     | (none, loopState) =>
         evalCrepSemHOLProg (crepStampExactDomains state loopState) memDec shMemDec
           (.while condition body)
     | (some (.continue 0), loopState) =>
         evalCrepSemHOLProg (crepStampExactDomains state loopState) memDec shMemDec
           (.while condition body)
     | (some (.break 0), loopState) => (none, loopState)
     | (result, loopState) => (exitLoopCrepResult result, loopState)).2.clock ≤
        state.clock := by
  split <;> (first | exact hrec | exact hstep)

set_option linter.unusedVariables false in
theorem crepCallFixed_clock_le {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (returnInfo : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fixed : Option (CrepResultHOLExact width) × CrepSemHOLState width σ)
    (hfix : fixed.2.clock ≤ state.clock)
    (hhandler : ∀ (handlerBody : CrepProgHOL width),
        (evalCrepSemHOLProg
          (crepStampExactDomains state { fixed.2 with locals := state.locals })
          memDec shMemDec handlerBody).2.clock ≤ state.clock) :
    (match hfixed : fixed with
     | (none, bodyState) => (some CrepResultHOLExact.error, bodyState)
     | (some (CrepResultHOLExact.break _), bodyState) => (some CrepResultHOLExact.error, bodyState)
     | (some (CrepResultHOLExact.continue _), bodyState) => (some CrepResultHOLExact.error, bodyState)
     | (some (CrepResultHOLExact.return retvs), bodyState) =>
         match returnInfo with
         | none => (some (CrepResultHOLExact.return retvs), CrepSemHOLState.emptyLocals bodyState)
         | some (rts, _) =>
             if retvs.length ≠ rts.length then (some CrepResultHOLExact.error, bodyState)
             else match rts.mapM state.locals.lookup with
               | some _ => (none, { bodyState with
                   locals := state.locals.updateListEq
                     (rts.zip retvs) })
               | none => (some CrepResultHOLExact.error, bodyState)
     | (some (CrepResultHOLExact.exception eid), bodyState) =>
         match returnInfo with
         | none =>
             (some (CrepResultHOLExact.exception eid), CrepSemHOLState.emptyLocals bodyState)
         | some (_, none) =>
             (some (CrepResultHOLExact.exception eid), CrepSemHOLState.emptyLocals bodyState)
         | some (_, some (eid', handlerBody)) =>
             if eid = eid' then
               evalCrepSemHOLProg
                 (crepStampExactDomains state { bodyState with locals := state.locals })
                 memDec shMemDec handlerBody
             else (some (CrepResultHOLExact.exception eid), CrepSemHOLState.emptyLocals bodyState)
     | (some result, bodyState) =>
         (some result, CrepSemHOLState.emptyLocals bodyState)).2.clock ≤
        state.clock := by
  split
  · exact hfix
  · exact hfix
  · exact hfix
  · split
    · exact hfix
    · split
      · exact hfix
      · split
        · exact hfix
        · exact hfix
  · split
    · exact hfix
    · exact hfix
    · split
      · exact hhandler _
      · exact hfix
  · exact hfix

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 4000 in
theorem evalCrepSemHOLProg_clock_le {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (program : CrepProgHOL width) :
    (evalCrepSemHOLProg state memDec shMemDec program).2.clock ≤ state.clock := by
  have hmain : ∀ (c : Nat) (state : CrepSemHOLState width σ), state.clock ≤ c →
      ∀ (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
        (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
        (program : CrepProgHOL width),
        CrepClockBounded state memDec shMemDec program := by
    intro c
    induction c using Nat.strongRecOn with
    | ind c ihClock =>
      intro state hclk memDec shMemDec program
      have inner : ∀ (n : Nat) (program : CrepProgHOL width), sizeOf program ≤ n →
          ∀ (state : CrepSemHOLState width σ), state.clock ≤ c →
          ∀ (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
            (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)),
            CrepClockBounded state memDec shMemDec program := by
        intro n
        induction n using Nat.strongRecOn with
        | ind n ihSize =>
          intro program hsize state hclk memDec shMemDec
          cases program with
          | skip =>
              simp [CrepClockBounded, evalCrepSemHOLProg_skip]
          | dec name value body =>
              have hsub : sizeOf body < n := by
                have h1 : sizeOf body < sizeOf (CrepProgHOL.dec name value body) := by
                  decreasing_trivial
                omega
              have ihBody := ihSize (sizeOf body) hsub body (by omega)
              unfold CrepClockBounded
              rw [evalCrepSemHOLProg_dec]
              split
              · simp
              · rename_i v _
                have hb := ihBody (CrepSemHOLState.setVar name v state)
                  (by simp only [CrepSemHOLState.setVar]; exact hclk) memDec shMemDec
                unfold CrepClockBounded at hb
                simpa only [CrepSemHOLState.setVar] using hb
          | primitive names operator args =>
              unfold CrepClockBounded
              rw [evalCrepSemHOLProg_primitive]
              repeat' (first | split | simp_all)
          | assign name src =>
              unfold CrepClockBounded
              rw [evalCrepSemHOLProg_assign]
              split
              · simp
              · rename_i value _
                split <;> simp [CrepSemHOLState.setVar]
          | store dst src =>
              unfold CrepClockBounded
              rw [evalCrepSemHOLProg_store]
              repeat' (first | split | simp_all)
          | store32 dst src =>
              unfold CrepClockBounded
              rw [evalCrepSemHOLProg_store32]
              repeat' (first | split | simp_all)
          | storeByte dst src =>
              unfold CrepClockBounded
              rw [evalCrepSemHOLProg_storeByte]
              repeat' (first | split | simp_all)
          | storeGlob dst src =>
              unfold CrepClockBounded
              rw [evalCrepSemHOLProg_storeGlob]
              split <;> simp [CrepSemHOLState.setGlobals]
          | seq first second =>
              have hsubF : sizeOf first < n := by
                have h1 : sizeOf first < sizeOf (CrepProgHOL.seq first second) := by
                  decreasing_trivial
                omega
              have hsubS : sizeOf second < n := by
                have h1 : sizeOf second < sizeOf (CrepProgHOL.seq first second) := by
                  decreasing_trivial
                omega
              have ihFirst := ihSize (sizeOf first) hsubF first (by omega)
              have ihSecond := ihSize (sizeOf second) hsubS second (by omega)
              unfold CrepClockBounded
              simp only [evalCrepSemHOLProg_seq]
              split
              · rename_i stepState hstep
                have hSecond := ihSecond (crepStampExactDomains state stepState)
                  (by
                    have hb := fixClockCrepSemHOL_IMP_LESS_EQ state
                      (evalCrepSemHOLProg state memDec shMemDec first) none stepState
                      (by simpa using hstep)
                    change stepState.clock ≤ c
                    omega)
                  memDec shMemDec
                unfold CrepClockBounded at hSecond
                exact Nat.le_trans hSecond
                  (by
                    change stepState.clock ≤ state.clock
                    exact fixClockCrepSemHOL_IMP_LESS_EQ state
                      (evalCrepSemHOLProg state memDec shMemDec first) none stepState
                      (by simpa using hstep))
              · rename_i val stepState hstep
                have hstep' : fixClockCrepSemHOL state
                    (evalCrepSemHOLProg state memDec shMemDec first) = (some val, stepState) :=
                  hstep
                rw [hstep']
                exact fixClockCrepSemHOL_IMP_LESS_EQ state
                  (evalCrepSemHOLProg state memDec shMemDec first) (some val) stepState hstep
          | ite condition thenBranch elseBranch =>
              have hsubT : sizeOf thenBranch < n := by
                have h1 : sizeOf thenBranch <
                    sizeOf (CrepProgHOL.ite condition thenBranch elseBranch) := by
                  decreasing_trivial
                omega
              have hsubE : sizeOf elseBranch < n := by
                have h1 : sizeOf elseBranch <
                    sizeOf (CrepProgHOL.ite condition thenBranch elseBranch) := by
                  decreasing_trivial
                omega
              have ihThen := ihSize (sizeOf thenBranch) hsubT thenBranch (by omega)
              have ihElse := ihSize (sizeOf elseBranch) hsubE elseBranch (by omega)
              unfold CrepClockBounded
              rw [evalCrepSemHOLProg_ite]
              split
              · rename_i w
                split
                · exact ihThen state hclk memDec shMemDec
                · exact ihElse state hclk memDec shMemDec
              · simp
          | «while» condition body =>
              unfold CrepClockBounded
              rw [evalCrepSemHOLProg_while]
              split
              · rename_i w
                split
                · split
                  · simp [CrepSemHOLState.emptyLocals]
                  · rename_i hne
                    have hfixLe : (fixClockCrepSemHOL (decClockCrepSemHOL state)
                        (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec
                          body)).2.clock ≤ state.clock :=
                      Nat.le_trans
                        (fixClock_clock_le (decClockCrepSemHOL state)
                          (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec body))
                        (decClock_clock_le state)
                    refine crepWhileStep_clock_le state memDec shMemDec condition body
                      (fixClockCrepSemHOL (decClockCrepSemHOL state)
                        (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec
                          body)) hfixLe ?_
                    have hclock : (fixClockCrepSemHOL (decClockCrepSemHOL state)
                          (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec
                            body)).2.clock < c :=
                      Nat.lt_of_le_of_lt
                        (fixClock_clock_le (decClockCrepSemHOL state)
                          (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec body))
                        (Nat.lt_of_lt_of_le (decClock_clock_lt state hne) hclk)
                    have h := ihClock
                      (fixClockCrepSemHOL (decClockCrepSemHOL state)
                        (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec
                          body)).2.clock hclock
                      (crepStampExactDomains state
                        (fixClockCrepSemHOL (decClockCrepSemHOL state)
                          (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec
                            body)).2)
                      (Nat.le_refl _) memDec shMemDec (.while condition body)
                    unfold CrepClockBounded at h
                    exact Nat.le_trans h hfixLe
                · simp
              · simp
          | «break» label =>
              simp [CrepClockBounded, evalCrepSemHOLProg_break]
          | «continue» label =>
              simp [CrepClockBounded, evalCrepSemHOLProg_continue]
          | call calleeInfo function arguments =>
              unfold CrepClockBounded
              rw [evalCrepSemHOLProg_call]
              split
              · simp
              · rename_i values _
                split
                · simp
                · rename_i parameters body _
                  split
                  · dsimp only
                    split
                    · rename_i rts snd
                      split
                      · dsimp only
                        split
                        · simp [CrepSemHOLState.emptyLocals]
                        · rename_i hne
                          refine crepCallFixed_clock_le state memDec shMemDec (some (rts, snd)) _ ?_ ?_
                          · exact Nat.le_trans (fixClock_clock_le _ _) (decClock_clock_le _)
                          · intro handlerBody
                            have hclock : (crepStampExactDomains state
                                  { (fixClockCrepSemHOL (decClockCrepSemHOL
                                      { state with locals :=
                                        HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                    (evalCrepSemHOLProg (decClockCrepSemHOL
                                      { state with locals :=
                                        HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                      memDec shMemDec body)).2 with
                                    locals := state.locals }).clock < c := by
                              change (fixClockCrepSemHOL (decClockCrepSemHOL
                                    { state with locals :=
                                      HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                  (evalCrepSemHOLProg (decClockCrepSemHOL
                                    { state with locals :=
                                      HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                    memDec shMemDec body)).2.clock < c
                              exact Nat.lt_of_le_of_lt (fixClock_clock_le _ _)
                                (Nat.lt_of_lt_of_le (decClock_clock_lt _ hne) hclk)
                            have h := ihClock
                              (crepStampExactDomains state
                                { (fixClockCrepSemHOL (decClockCrepSemHOL
                                    { state with locals :=
                                      HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                  (evalCrepSemHOLProg (decClockCrepSemHOL
                                    { state with locals :=
                                      HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                    memDec shMemDec body)).2 with
                                  locals := state.locals }).clock hclock
                              (crepStampExactDomains state
                                { (fixClockCrepSemHOL (decClockCrepSemHOL
                                    { state with locals :=
                                      HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                  (evalCrepSemHOLProg (decClockCrepSemHOL
                                    { state with locals :=
                                      HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                    memDec shMemDec body)).2 with
                                  locals := state.locals })
                              (Nat.le_refl _) memDec shMemDec handlerBody
                            unfold CrepClockBounded at h
                            exact Nat.le_trans h
                              (Nat.le_trans (fixClock_clock_le _ _) (decClock_clock_le _))
                      · simp
                    · dsimp only
                      split
                      · simp [CrepSemHOLState.emptyLocals]
                      · rename_i hne
                        refine crepCallFixed_clock_le state memDec shMemDec none _ ?_ ?_
                        · exact Nat.le_trans (fixClock_clock_le _ _) (decClock_clock_le _)
                        · intro handlerBody
                          have hclock : (crepStampExactDomains state
                                { (fixClockCrepSemHOL (decClockCrepSemHOL
                                    { state with locals :=
                                      HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                  (evalCrepSemHOLProg (decClockCrepSemHOL
                                    { state with locals :=
                                      HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                    memDec shMemDec body)).2 with
                                  locals := state.locals }).clock < c := by
                            change (fixClockCrepSemHOL (decClockCrepSemHOL
                                  { state with locals :=
                                    HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                (evalCrepSemHOLProg (decClockCrepSemHOL
                                  { state with locals :=
                                    HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                  memDec shMemDec body)).2.clock < c
                            exact Nat.lt_of_le_of_lt (fixClock_clock_le _ _)
                              (Nat.lt_of_lt_of_le (decClock_clock_lt _ hne) hclk)
                          have h := ihClock
                            (crepStampExactDomains state
                              { (fixClockCrepSemHOL (decClockCrepSemHOL
                                  { state with locals :=
                                    HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                (evalCrepSemHOLProg (decClockCrepSemHOL
                                  { state with locals :=
                                    HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                  memDec shMemDec body)).2 with
                                locals := state.locals }).clock hclock
                            (crepStampExactDomains state
                              { (fixClockCrepSemHOL (decClockCrepSemHOL
                                  { state with locals :=
                                    HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                (evalCrepSemHOLProg (decClockCrepSemHOL
                                  { state with locals :=
                                    HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                  memDec shMemDec body)).2 with
                                locals := state.locals })
                            (Nat.le_refl _) memDec shMemDec handlerBody
                          unfold CrepClockBounded at h
                          exact Nat.le_trans h
                            (Nat.le_trans (fixClock_clock_le _ _) (decClock_clock_le _))
                  · simp
          | extCall function configuration configurationLength array arrayLength =>
              unfold CrepClockBounded
              rw [evalCrepSemHOLProg_extCall]
              repeat' (first | split | simp_all)
          | «raise» exception =>
              simp [CrepClockBounded, evalCrepSemHOLProg_raise, CrepSemHOLState.emptyLocals]
          | «return» values =>
              unfold CrepClockBounded
              rw [evalCrepSemHOLProg_return]
              split <;> simp [CrepSemHOLState.emptyLocals]
          | shMem operator name address =>
              unfold CrepClockBounded
              rw [evalCrepSemHOLProg_shMem]
              split
              · rename_i addressValue heq
                split
                · split
                  · rw [shMemLoadClockEq operator name addressValue state]
                    exact Nat.le_refl _
                  · simp
                · split
                  · rw [shMemStoreClockEq operator name addressValue state]
                    exact Nat.le_refl _
                  · simp
              · simp
          | tick =>
              unfold CrepClockBounded
              rw [evalCrepSemHOLProg_tick]
              split
              · simp [CrepSemHOLState.emptyLocals]
              · simp only [decClockCrepSemHOL]; omega
      exact inner (sizeOf program) program (by omega) state hclk memDec shMemDec
  exact hmain state.clock state (by omega) memDec shMemDec program

/-- HOL `fix_clock_evaluate` (`cakeml/pancake/semantics/crepSemScript.sml:432-437`) over the
exact no-decider evaluator: `fixClockCrepSemHOL` is the identity on any result of
`evalCrepSemHOLProgExact`, because the run never raises the clock
(`evalCrepSemHOLProg_clock_le`, HOL `evaluate_clock`, crepSemScript.sml:420-430). This is the
Flapjack-side statement behind HOL `fix_clock_evaluate`; it is deliberately untagged pending the
full exact-evaluator clause/carrier review. -/
theorem fixClockCrepSemHOL_evalCrepSemHOLProgExact {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (program : CrepProgHOL width) :
    fixClockCrepSemHOL state (evalCrepSemHOLProgExact state program) =
      evalCrepSemHOLProgExact state program := by
  classical
  have hclock : (evalCrepSemHOLProgExact state program).2.clock ≤ state.clock := by
    rw [evalCrepSemHOLProgExact_eq_core state program
      (fun a => Classical.propDecidable (state.memaddrs a))
      (fun a => Classical.propDecidable (state.shMemaddrs a))]
    exact evalCrepSemHOLProg_clock_le state _ _ program
  cases h : evalCrepSemHOLProgExact state program with
  | mk res fin =>
    have hfin : fin.clock ≤ state.clock := by
      rw [h] at hclock
      exact hclock
    simp only [fixClockCrepSemHOL]
    rw [if_neg (by omega)]

/-- Fix-clock-free `Seq` clause of HOL `evaluate_def` as rebound at
`cakeml/pancake/semantics/crepSemScript.sml:443` (`evaluate_def =
REWRITE_RULE [fix_clock_evaluate] evaluate_def`). The primal equation
(`:303-306`) fixes the clock around the first command; the line-443 rebind
eliminates it using `fix_clock_evaluate` (`:432-437`), giving a plain
`let (res,s1) = evaluate (c1,s) in if res = NONE then evaluate (c2,s1) else
(res,s1)`. This theorem derives that clause over the no-decider exact
evaluator by rewriting the reviewed line-240 `Seq` equation with the exact
`fixClockCrepSemHOL_evalCrepSemHOLProgExact` identity (bead
`flapjack-4ac.5.16.5.25`). -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "evaluate_def" 443
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem evalCrepSemHOLProgExact_seq_fixClockFree {width : Nat} [NeZero width]
    {σ : Type} (state : CrepSemHOLState width σ) (first second : CrepProgHOL width) :
    evalCrepSemHOLProgExact state (.seq first second) =
      (let step := evalCrepSemHOLProgExact state first
       match step with
       | (none, stepState) => evalCrepSemHOLProgExact stepState second
       | (some _, _) => step) := by
  rw [evalCrepSemHOLProgExact_seq, fixClockCrepSemHOL_evalCrepSemHOLProgExact]

end Flapjack
