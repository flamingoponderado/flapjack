module

public import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
@[expose] public section

/-! Direct original HOL rows for the exact state-owned ShMem evaluator over the
   reviewed `CrepSemHOLState`/`CrepProgHOL` and `HolFfiState` carriers. -/

namespace Flapjack.Test.CrepSemTotalShMemParity

open Flapjack

def address : BitVec 64 := BitVec.ofNat 64 10

def echoOracle : HolOracle Unit :=
  fun _ ffiState _ bytes => .ret ffiState bytes

def finalOracle : HolOracle Unit :=
  fun _ _ _ _ => .final .diverged

def stateWith (oracle : HolOracle Unit) (domain : BitVec 64 → Prop) :
    CrepSemHOLState 64 Unit :=
  { locals := HolFiniteMapExact.update
      (HolFiniteMapExact.update HolFiniteMapExact.empty
        (0, .word (BitVec.ofNat 64 7)))
      (1, .word (BitVec.ofNat 64 0))
    globals := HolFiniteMapExact.empty
    code := HolFiniteMapExact.empty
    memory := fun _ => .word 0
    memaddrs := fun _ => False
    shMemaddrs := domain
    clock := 5
    be := false
    ffi := { oracle := oracle, ffiState := (), ioEvents := [] }
    baseAddr := 0
    topAddr := 100 }

def memDec (oracle : HolOracle Unit) (domain : BitVec 64 → Prop) :
    (value : BitVec 64) → Decidable ((stateWith oracle domain).memaddrs value) :=
  fun _ => isFalse (by simp [stateWith])

def domainDecAddress (value : BitVec 64) :
    Decidable ((fun current : BitVec 64 => current = address) value) :=
  inferInstanceAs (Decidable (value = address))

def domainDecEight (value : BitVec 64) :
    Decidable ((fun current : BitVec 64 => current = BitVec.ofNat 64 8) value) :=
  inferInstanceAs (Decidable (value = BitVec.ofNat 64 8))

def echoPairs (bytes : List UInt8) : List (BitVec 8 × BitVec 8) :=
  bytes.map fun byte => (byte.toBitVec, byte.toBitVec)

def shmemRowsMatch : Bool := Id.run do
  let state := stateWith echoOracle (fun value : BitVec 64 => value = address)
  let loadOk :=
    match evalCrepSemHOLProg state (memDec echoOracle (fun value : BitVec 64 => value = address))
        (domainDecAddress) (.shMem .load 1 (.const address) : CrepProgHOL 64) with
    | (none, post) =>
        post.locals.lookup 1 == some (.word address) &&
        post.ffi.ioEvents.length == 1 &&
        match post.ffi.ioEvents with
        | [event] => event.name == .sharedMem .mappedRead &&
            event.configuration == [BitVec.ofNat 8 0] &&
            event.bytes == echoPairs (crepClockWordToBytes address)
        | _ => false
    | _ => false
  let storeOk :=
    match evalCrepSemHOLProg state (memDec echoOracle (fun value : BitVec 64 => value = address))
        (domainDecAddress) (.shMem .store 0 (.const address) : CrepProgHOL 64) with
    | (none, post) =>
        post.locals.lookup 0 == some (.word (BitVec.ofNat 64 7)) &&
        post.ffi.ioEvents.length == 1 &&
        match post.ffi.ioEvents with
        | [event] => event.name == .sharedMem .mappedWrite &&
            event.configuration == [BitVec.ofNat 8 0] &&
            event.bytes == echoPairs
              (crepClockWordToBytes (BitVec.ofNat 64 7) ++ crepClockWordToBytes address)
        | _ => false
    | _ => false
  let alignedState := stateWith echoOracle
    (fun value : BitVec 64 => value = BitVec.ofNat 64 8)
  let load8Ok :=
    match evalCrepSemHOLProg alignedState
        (memDec echoOracle (fun value : BitVec 64 => value = BitVec.ofNat 64 8))
        (domainDecEight) (.shMem .load8 1 (.const address) : CrepProgHOL 64) with
    | (none, post) =>
        post.locals.lookup 1 == some (.word address) &&
        match post.ffi.ioEvents with
        | [event] => event.name == .sharedMem .mappedRead &&
            event.configuration == [BitVec.ofNat 8 1] &&
            event.bytes == echoPairs (crepClockWordToBytes address)
        | _ => false
    | _ => false
  let store8Ok :=
    match evalCrepSemHOLProg alignedState
        (memDec echoOracle (fun value : BitVec 64 => value = BitVec.ofNat 64 8))
        (domainDecEight) (.shMem .store8 0 (.const address) : CrepProgHOL 64) with
    | (none, post) =>
        post.locals.lookup 0 == some (.word (BitVec.ofNat 64 7)) &&
        match post.ffi.ioEvents with
        | [event] => event.name == .sharedMem .mappedWrite &&
            event.configuration == [BitVec.ofNat 8 1] && event.bytes.length == 9 &&
            event.bytes == echoPairs
              ((crepClockWordToBytes (BitVec.ofNat 64 7)).take 1 ++
                crepClockWordToBytes address)
        | _ => false
    | _ => false
  let domainError :=
    match evalCrepSemHOLProg state (memDec echoOracle (fun value : BitVec 64 => value = address))
        (domainDecAddress) (.shMem .load8 1 (.const address) : CrepProgHOL 64) with
    | (some .error, post) => post.locals.lookup 1 == state.locals.lookup 1 &&
        post.ffi.ioEvents == []
    | _ => false
  let missingLocalError :=
    match evalCrepSemHOLProg state (memDec echoOracle (fun value : BitVec 64 => value = address))
        (domainDecAddress) (.shMem .load 9 (.const address) : CrepProgHOL 64) with
    | (some .error, post) => post.locals.lookup 0 == state.locals.lookup 0 &&
        post.ffi.ioEvents == []
    | _ => false
  let finalState := stateWith finalOracle (fun value : BitVec 64 => value = address)
  let finalLoad :=
    match evalCrepSemHOLProg finalState
        (memDec finalOracle (fun value : BitVec 64 => value = address))
        (domainDecAddress) (.shMem .load 1 (.const address) : CrepProgHOL 64) with
    | (some (.finalFfi event), post) =>
        event.outcome == .diverged && post.locals.lookup 0 == none &&
        post.ffi.ioEvents == []
    | _ => false
  pure (loadOk && storeOk && load8Ok && store8Ok && domainError &&
    missingLocalError && finalLoad)

#guard shmemRowsMatch

theorem shmemLoadDomainError
    (state : CrepSemHOLState 64 Unit)
    (addressExp : CrepExpHOL 64) (value : BitVec 64)
    (haddress : evalCrepSemHOLExp state addressExp = some (.word value))
    (cell : HolWordLab 64)
    (hdestination : state.locals.lookup 1 = some cell)
    (hdomain : ¬ state.shMemaddrs (panByteAlignHOL value)) :
    evalCrepSemHOLProgExact state (.shMem .load8 1 addressExp) = (some .error, state) := by
  rw [evalCrepSemHOLProgExact_shMem_holShape]
  simp only [haddress]
  rw [if_pos (by simp [crepIsLoadMemOp])]
  simp [hdestination, crepShMemOpExactHOL, crepShMemLoadExactHOL, hdomain]

theorem shmemLoadExpressionError
    (state : CrepSemHOLState 64 Unit)
    (addressExp : CrepExpHOL 64)
    (haddress : evalCrepSemHOLExp state addressExp = none) :
    evalCrepSemHOLProgExact state (.shMem .load 1 addressExp) = (some .error, state) := by
  rw [evalCrepSemHOLProgExact_shMem_holShape]
  simp only [haddress]

def runChecks : IO Bool := do
  if shmemRowsMatch then
    IO.println "PASS total Crep HOL ShMem success/domain/error/final clauses match direct oracle"
  else
    IO.println "FAIL total Crep HOL ShMem success/domain/error/final clauses match direct oracle"
  pure shmemRowsMatch

end Flapjack.Test.CrepSemTotalShMemParity
