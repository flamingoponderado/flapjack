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

end Flapjack
