import Flapjack.Pancake.Semantics.CrepProps

/-! Direct kernel-checked observations for the exact FFI event-prefix theorem
`Flapjack.crepPropsEvaluateIoEventsMono` (HOL
`crepPropsScript.sml:957 evaluate_io_events_mono`) over the exact state carrier
`CrepSemHOLState` and the total evaluator `evalCrepSemHOLProg` /
`evalCrepSemHOLProgExact`.

The `ExtCall` clause is the only place the exact evaluator can append an
event through `call_FFI`. Rows below exercise both a returning oracle (the log
strictly grows from `[]` to one event) and a terminal (`final`) oracle (the log
is unchanged), then state the general theorem and its untagged core prefix lemma
on the concrete fixture. -/

namespace Flapjack.Test.CrepSemIoEventsMonoParity

open Flapjack
open Flapjack.Basis.Pure.MlString

private def echoOracle : HolOracle Unit := fun _ state _ bytes => .ret state bytes

private def finalOracle : HolOracle Unit := fun _ _ _ _ => .final .diverged

private def baseState (oracle : HolOracle Unit) : CrepSemHOLState 8 Unit where
  locals := HolFiniteMapExact.empty.updateList
    [(0, .word (BitVec.ofNat 8 0)), (1, .word (BitVec.ofNat 8 0)),
     (2, .word (BitVec.ofNat 8 0)), (3, .word (BitVec.ofNat 8 0))]
  globals := HolFiniteMapExact.empty
  code := HolFiniteMapExact.empty
  memory := fun _ => .word 0
  memaddrs := fun _ => True
  shMemaddrs := fun _ => False
  clock := 5
  be := false
  ffi := { oracle := oracle, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 100

private def echoState : CrepSemHOLState 8 Unit := baseState echoOracle

private def finalState : CrepSemHOLState 8 Unit := baseState finalOracle

private def program : CrepProgHOL 8 :=
  .extCall (Flapjack.Basis.Pure.MlString.ofString "echo") 1 0 3 2

private def memDec : (a : BitVec 8) → Decidable (echoState.memaddrs a) :=
  fun _ => isTrue trivial

private def shMemDec : (a : BitVec 8) → Decidable (echoState.shMemaddrs a) :=
  fun _ => isFalse (by simp [echoState, baseState])

private def finalMemDec : (a : BitVec 8) → Decidable (finalState.memaddrs a) :=
  fun _ => isTrue trivial

private def finalShMemDec : (a : BitVec 8) → Decidable (finalState.shMemaddrs a) :=
  fun _ => isFalse (by simp [finalState, baseState])

/-- The returning `ExtCall` strictly grows the event log: `[]` becomes one
    `echo` event. -/
def extCallReturnedGrows : Bool :=
  (evalCrepSemHOLProg echoState memDec shMemDec program).2.ffi.ioEvents.length == 1

/-- The terminal (`final`) `ExtCall` leaves the event log empty, matching HOL
    `call_FFI`'s `FFI_final` branch. -/
def extCallFinalPreserves : Bool :=
  (evalCrepSemHOLProg finalState finalMemDec finalShMemDec program).2.ffi.ioEvents.length == 0

/-- Kernel-checked application of the exact core prefix lemma on the fixture. -/
theorem corePrefixExample :
    echoState.ffi.ioEvents <+:
      (evalCrepSemHOLProg echoState memDec shMemDec program).2.ffi.ioEvents :=
  evalCrepSemHOLProg_ioEvents_prefix echoState memDec shMemDec program

/-- Kernel-checked application of the tagged HOL theorem
    `crepPropsEvaluateIoEventsMono` on the fixture. -/
theorem taggedMonoExample
    (result : Option (CrepResultHOLExact 8)) (post : CrepSemHOLState 8 Unit)
    (heval : evalCrepSemHOLProgExact echoState program = (result, post)) :
    echoState.ffi.ioEvents <+: post.ffi.ioEvents :=
  crepPropsEvaluateIoEventsMono program echoState result post heval

#guard extCallReturnedGrows
#guard extCallFinalPreserves

def runChecks : IO Bool := do
  let ok := extCallReturnedGrows && extCallFinalPreserves
  if extCallReturnedGrows then
    IO.println "PASS exact Crep ExtCall returning oracle strictly grows ioEvents"
  else
    IO.println "FAIL exact Crep ExtCall returning oracle strictly grows ioEvents"
  if extCallFinalPreserves then
    IO.println "PASS exact Crep ExtCall final oracle preserves ioEvents"
  else
    IO.println "FAIL exact Crep ExtCall final oracle preserves ioEvents"
  pure ok

end Flapjack.Test.CrepSemIoEventsMonoParity
