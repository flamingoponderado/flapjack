import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Pancake.Semantics.CrepSem.Primop
import Flapjack.Pancake.Semantics.CrepSem.LookupCode
import Flapjack.Pancake.Semantics.CrepSem.TotalEval
import Flapjack.Pancake.Semantics.PanSemStateEval
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
* result: `Option (CrepResultHOL (BitVec width) HolFinalEvent)`, where `none` is
  HOL `NONE` (ordinary completion), exactly as `evaluate` returns
  `result option`. HOL `FinalFFI` always carries a `final_event`, so the event
  type is fixed at `HolFinalEvent` and is not `'ffi`-dependent.

The evaluator `evalCrepSemHOLProg` is a single total function with **no fuel**,
**no `Option`-valued fuel adapter**, and **no dependence on
`evalCrepRuntimeResult`**. It is not a wrapper: every clause is a literal
translation of the corresponding `evaluate_def` disjunct, including the
`fix_clock`/`dec_clock` split, the `While` loop-control labels, the `Call`
handler path, and the FFI clauses.

## Declaration-local representation notes (no `@[hol]` tag)

The declarations here are intentionally **untagged**: the whole-program
statement shape is not yet the reviewed exact HOL statement (the projection of
`CrepResultHOL`'s `return` payload through `PanWordLab`, the `RiscV.Word width`
fixed-width model of HOL's arbitrary finite word dimension, the executable
`HolFfiState`/`UInt8` byte codec used by the FFI clauses, and the omission of a
general agreement proof with the executed interpreter). They are
declaration-local infrastructure only.

* `CrepResultHOL.return` carries `List (PanWordLab (BitVec width))` while HOL
  `crepSem$result` carries `('a word_lab) list`; the exact `HolWordLab` values
  produced by `evalCrepSemHOLExp` are transported by `HolWordLab.toPanWordLab`
  in the `Return`/`Call` clauses.
* `CrepSemHOLState` is the finite-support `HolFiniteMapExact` translation of
  HOL's `|->` fields; the state helpers `setVar`/`setGlobals`/`updLocals`/
  `emptyLocals`/`resVarEq` implement the HOL updates with HOL `=` equality.
* The memory/FFI clause helpers (`panMemStore32HOL`, `panMemStoreByteHOL`,
  `panByteAlignHOL`, `readBytearrayHOL`, `panWriteBytearrayHOL`, `callFFIHOL`)
  are the already-reviewed exact ports; `crepClockWordToBytes` /
  `crepClockWordOfBytes` are the `word_to_bytes`/`word_of_bytes` byte codecs.
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

/-- Exact HOL `write_bytearray` application with an explicit domain decision. -/
def crepExactWriteBytearray {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (address : BitVec width) (bytes : List UInt8) :
    BitVec width → HolWordLab width := by
  haveI : DecidablePred state.memaddrs := memDec
  exact panWriteBytearrayHOL address bytes state.memory state.memaddrs state.be


/-- HOL `exit_loop` (`crepSemScript.sml:220-224`) on an optional control result:
    propagate other outcomes, decrementing the nesting label of `Break` and
    `Continue`. -/
def exitLoopCrepResult {width : Nat} :
    Option (CrepResultHOL (BitVec width) HolFinalEvent) →
      Option (CrepResultHOL (BitVec width) HolFinalEvent)
  | some (.break label) => some (.break (label - 1))
  | some (.continue label) => some (.continue (label - 1))
  | result => result

/-- Exact HOL `sh_mem_load` clause (`crepSemScript.sml:168-184`) over the exact
    finite-support `CrepSemHOLState`: on the appropriate shared-memory domain,
    call the FFI; a terminal result clears the locals, a returned result installs
    the byte-decoded word and the new FFI state. -/
def crepShMemLoadHOL {width : Nat} [NeZero width] {σ : Type}
    (operator : CrepMemOp) (name : Nat) (address : BitVec width)
    (state : CrepSemHOLState width σ)
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) :
    Option (CrepResultHOL (BitVec width) HolFinalEvent) × CrepSemHOLState width σ :=
  let byteWidth := crepShMemByteWidth operator
  let target := if byteWidth = 0 then address else panByteAlignHOL address
  match shMemDec target with
  | .isTrue _ =>
      match callFFIHOL state.ffi (.sharedMem .mappedRead)
          [BitVec.ofNat 8 byteWidth]
          ((crepClockWordToBytes address).map UInt8.toBitVec) with
      | .final event => (some (.finalFfi event), CrepSemHOLState.emptyLocals state)
      | .ret newFfi newBytes =>
          (none, { CrepSemHOLState.setVar name
                      (.word (crepClockWordOfBytes (newBytes.map UInt8.ofBitVec)))
                      state with
                    ffi := newFfi })
  | .isFalse _ => (some .error, state)

/-- Exact HOL `sh_mem_store` clause (`crepSemScript.sml:186-208`) over the exact
    finite-support `CrepSemHOLState`: the named local must hold a word; on the
    domain, call the FFI with the value/address bytes; a terminal result keeps
    the state, a returned result installs the new FFI state. -/
def crepShMemStoreHOL {width : Nat} [NeZero width] {σ : Type}
    (operator : CrepMemOp) (name : Nat) (address : BitVec width)
    (state : CrepSemHOLState width σ)
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) :
    Option (CrepResultHOL (BitVec width) HolFinalEvent) × CrepSemHOLState width σ :=
  let byteWidth := crepShMemByteWidth operator
  let target := if byteWidth = 0 then address else panByteAlignHOL address
  match state.locals.lookup name with
  | some (.word value) =>
      match shMemDec target with
      | .isTrue _ =>
          let valueBytes := crepClockWordToBytes value
          let addressBytes := crepClockWordToBytes address
          let payload :=
            if byteWidth = 0 then valueBytes ++ addressBytes
            else valueBytes.take byteWidth ++ addressBytes
          match callFFIHOL state.ffi (.sharedMem .mappedWrite)
              [BitVec.ofNat 8 byteWidth] (payload.map UInt8.toBitVec) with
          | .final event => (some (.finalFfi event), state)
          | .ret newFfi _ => (none, { state with ffi := newFfi })
      | .isFalse _ => (some .error, state)
  | _ => (some .error, state)

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
      Option (CrepResultHOL (BitVec width) HolFinalEvent) × CrepSemHOLState width σ
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
          match crepPrimopHOL operator (ws.map HolWordLab.toPanWordLab) with
          | some results =>
              if names.length = results.length &&
                 names.all (fun v => (state.locals.lookup v).isSome) &&
                 names.Nodup then
                (none, { state with
                  locals := state.locals.updateListEq
                    (names.zip (results.map PanWordLab.toHolWordLab)) })
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
                let proceed : Option (CrepResultHOL (BitVec width) HolFinalEvent) ×
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
                                    (rts.zip (retvs.map PanWordLab.toHolWordLab)) })
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
          match readBytearrayHOL configAddress configLength.toNat
                  (crepExactMemLoadByte state memDec),
                readBytearrayHOL arrayAddress arrayLengthValue.toNat
                  (crepExactMemLoadByte state memDec) with
          | some configBytes, some arrayBytes =>
              match callFFIHOL state.ffi (.extCall function)
                  (configBytes.map UInt8.toBitVec)
                  (arrayBytes.map UInt8.toBitVec) with
              | .final event => (some (.finalFfi event), state)
              | .ret newFfi newBytes =>
                  (none, { state with
                    memory := crepExactWriteBytearray state memDec arrayAddress
                      (newBytes.map UInt8.ofBitVec),
                    ffi := newFfi })
          | _, _ => (some .error, state)
      | _, _, _, _ => (some .error, state)
  | .raise exception =>
      (some (.exception exception), CrepSemHOLState.emptyLocals state)
  | .return values =>
      match values.mapM (@evalCrepSemHOLExp width ‹NeZero width› σ state memDec) with
      | some ws => (some (.return (ws.map HolWordLab.toPanWordLab)),
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

/-- HOL `evaluate (Dec v e prog, s)` (`crepSemScript.sml:242-249`): evaluate the
    initialiser; on failure `Error`, otherwise bind `v` and apply `res_var`.
    Finite-support `CrepSemHOLState` counterpart; untagged. -/
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

/-- HOL `evaluate (Assign v src, s)` (`crepSemScript.sml:257-262`): the variable
    must already be bound. Finite-support `CrepSemHOLState` counterpart;
    untagged. -/
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

/-- HOL `evaluate (Primitive lhss pop rhss, s)` (`crepSemScript.sml:250-256`).
    Finite-support `CrepSemHOLState` counterpart; untagged. -/
@[simp] theorem evalCrepSemHOLProg_primitive {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (names : List Nat) (operator : PrimOp) (args : List Nat) :
    evalCrepSemHOLProg state memDec shMemDec (.primitive names operator args) =
      (match args.mapM state.locals.lookup with
       | some ws =>
           match crepPrimopHOL operator (ws.map HolWordLab.toPanWordLab) with
           | some results =>
               if names.length = results.length &&
                  names.all (fun v => (state.locals.lookup v).isSome) &&
                  names.Nodup then
                 (none, { state with
                   locals := state.locals.updateListEq
                     (names.zip (results.map PanWordLab.toHolWordLab)) })
               else (some .error, state)
           | none => (some .error, state)
       | none => (some .error, state)) := by
  rw [evalCrepSemHOLProg.eq_def] <;> rfl

/-- HOL `evaluate (Store dst src, s)` (`crepSemScript.sml:263-269`). Finite-support
    `CrepSemHOLState` counterpart; untagged. -/
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

/-- HOL `evaluate (Store32 dst src, s)` (`crepSemScript.sml:270-276`).
    Finite-support `CrepSemHOLState` counterpart; untagged. -/
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

/-- HOL `evaluate (StoreByte dst src, s)` (`crepSemScript.sml:277-283`).
    Finite-support `CrepSemHOLState` counterpart; untagged. -/
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

/-- HOL `evaluate (StoreGlob dst src, s)` (`crepSemScript.sml:284-287`).
    Finite-support `CrepSemHOLState` counterpart; untagged. -/
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
       | some ws => (some (.return (ws.map HolWordLab.toPanWordLab)),
           CrepSemHOLState.emptyLocals state)
       | none => (some .error, state)) := by
  rw [evalCrepSemHOLProg.eq_def] <;> rfl

/-- HOL `evaluate (ShMem op v ad, s)` (`crepSemScript.sml:288-299`): loads accept
    any bound variable and delegate to `sh_mem_load`; stores require a `Word`
    local and delegate to `sh_mem_store`. -/
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
    (`crepSemScript.sml:364-381`): read both byte arrays, dispatch the FFI, then
    on return write the new bytes back and install the new FFI state. -/
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
           match readBytearrayHOL configAddress configLength.toNat
                   (crepExactMemLoadByte state memDec),
                 readBytearrayHOL arrayAddress arrayLengthValue.toNat
                   (crepExactMemLoadByte state memDec) with
           | some configBytes, some arrayBytes =>
               match callFFIHOL state.ffi (.extCall function)
                   (configBytes.map UInt8.toBitVec)
                   (arrayBytes.map UInt8.toBitVec) with
               | .final event => (some (.finalFfi event), state)
               | .ret newFfi newBytes =>
                   (none, { state with
                     memory := crepExactWriteBytearray state memDec arrayAddress
                       (newBytes.map UInt8.ofBitVec),
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

/-- HOL `evaluate (Call caltyp fname argexps, s)` (`crepSemScript.sml:330-363`):
    evaluate the arguments, look up the code, require distinct formals, install
    the callee locals under `dec_clock`, run the body under `fix_clock`, then
    handle ordinary completion/`Break`/`Continue` as `Error`, and `Return`/
    `Exception` including the handler path and `empty_locals` cleanup. -/
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
                 let proceed : Option (CrepResultHOL (BitVec width) HolFinalEvent) ×
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
                                     (rts.zip (retvs.map PanWordLab.toHolWordLab)) })
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

/-- The ShMem-load helper preserves both domain fields. -/
theorem crepShMemLoadHOL_preserves_domains {width : Nat} [NeZero width] {σ : Type}
    (operator : CrepMemOp) (name : Nat) (address : BitVec width)
    (state : CrepSemHOLState width σ)
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) :
    (crepShMemLoadHOL operator name address state shMemDec).2.memaddrs = state.memaddrs ∧
    (crepShMemLoadHOL operator name address state shMemDec).2.shMemaddrs =
      state.shMemaddrs := by
  simp only [crepShMemLoadHOL]
  split
  · split
    · simp [CrepSemHOLState.emptyLocals]
    · simp [CrepSemHOLState.setVar]
  · simp

/-- The ShMem-store helper preserves both domain fields. -/
theorem crepShMemStoreHOL_preserves_domains {width : Nat} [NeZero width] {σ : Type}
    (operator : CrepMemOp) (name : Nat) (address : BitVec width)
    (state : CrepSemHOLState width σ)
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) :
    (crepShMemStoreHOL operator name address state shMemDec).2.memaddrs = state.memaddrs ∧
    (crepShMemStoreHOL operator name address state shMemDec).2.shMemaddrs =
      state.shMemaddrs := by
  simp only [crepShMemStoreHOL]
  split
  · split
    · split
      · simp
      · simp
    · simp
  · simp

set_option linter.unusedVariables false in
/-- Domain preservation of the `Call` callee-result case split. `hfix` records
    that the `fix_clock` result state carries the input state's domain fields,
    and `hhandler` records the exception-handler call's preservation. -/
theorem crepCallFixed_domains {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (returnInfo : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fixed : Option (CrepResultHOL (BitVec width) HolFinalEvent) ×
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
     | (none, bodyState) => (some CrepResultHOL.error, bodyState)
     | (some (CrepResultHOL.break _), bodyState) => (some CrepResultHOL.error, bodyState)
     | (some (CrepResultHOL.continue _), bodyState) => (some CrepResultHOL.error, bodyState)
     | (some (CrepResultHOL.return retvs), bodyState) =>
         match returnInfo with
         | none => (some (CrepResultHOL.return retvs), CrepSemHOLState.emptyLocals bodyState)
         | some (rts, _) =>
             if retvs.length ≠ rts.length then (some CrepResultHOL.error, bodyState)
             else match rts.mapM state.locals.lookup with
               | some _ => (none, { bodyState with
                   locals := state.locals.updateListEq
                     (rts.zip (retvs.map PanWordLab.toHolWordLab)) })
               | none => (some CrepResultHOL.error, bodyState)
     | (some (CrepResultHOL.exception eid), bodyState) =>
         match returnInfo with
         | none =>
             (some (CrepResultHOL.exception eid), CrepSemHOLState.emptyLocals bodyState)
         | some (_, none) =>
             (some (CrepResultHOL.exception eid), CrepSemHOLState.emptyLocals bodyState)
         | some (_, some (eid', handlerBody)) =>
             if eid = eid' then
               evalCrepSemHOLProg
                 (crepStampExactDomains state { bodyState with locals := state.locals })
                 memDec shMemDec handlerBody
             else (some (CrepResultHOL.exception eid), CrepSemHOLState.emptyLocals bodyState)
     | (some result, bodyState) =>
         (some result, CrepSemHOLState.emptyLocals bodyState)).2.memaddrs =
        state.memaddrs ∧
    (match hfixed : fixed with
     | (none, bodyState) => (some CrepResultHOL.error, bodyState)
     | (some (CrepResultHOL.break _), bodyState) => (some CrepResultHOL.error, bodyState)
     | (some (CrepResultHOL.continue _), bodyState) => (some CrepResultHOL.error, bodyState)
     | (some (CrepResultHOL.return retvs), bodyState) =>
         match returnInfo with
         | none => (some (CrepResultHOL.return retvs), CrepSemHOLState.emptyLocals bodyState)
         | some (rts, _) =>
             if retvs.length ≠ rts.length then (some CrepResultHOL.error, bodyState)
             else match rts.mapM state.locals.lookup with
               | some _ => (none, { bodyState with
                   locals := state.locals.updateListEq
                     (rts.zip (retvs.map PanWordLab.toHolWordLab)) })
               | none => (some CrepResultHOL.error, bodyState)
     | (some (CrepResultHOL.exception eid), bodyState) =>
         match returnInfo with
         | none =>
             (some (CrepResultHOL.exception eid), CrepSemHOLState.emptyLocals bodyState)
         | some (_, none) =>
             (some (CrepResultHOL.exception eid), CrepSemHOLState.emptyLocals bodyState)
         | some (_, some (eid', handlerBody)) =>
             if eid = eid' then
               evalCrepSemHOLProg
                 (crepStampExactDomains state { bodyState with locals := state.locals })
                 memDec shMemDec handlerBody
             else (some (CrepResultHOL.exception eid), CrepSemHOLState.emptyLocals bodyState)
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
    (loopStep : Option (CrepResultHOL (BitVec width) HolFinalEvent) ×
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

end Flapjack
