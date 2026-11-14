module

public import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
@[expose] public section

/-! Direct HOL-EVAL observations for `crepSem$evaluate_def` are recorded in
`scripts/hol-probes/crep_ext_call_eval_probe.out`. These guards exercise the
same success, final-FFI, missing-local, and failed-read rows on the reviewed
exact `CrepSemHOLState`/`CrepProgHOL` carriers and the exact MlString/word8 FFI
carriers. -/

namespace Flapjack.Test.CrepSemTotalExtCallParity

open Flapjack
open Flapjack.Basis.Pure.MlString

def echoOracle : HolOracle Unit :=
  fun _ _ _ bytes => .ret () (bytes.map fun _ => BitVec.ofNat 8 42)

def finalOracle : HolOracle Unit := fun _ _ _ _ => .final .diverged

def echoFfi : HolFfiState Unit :=
  { oracle := echoOracle, ffiState := (), ioEvents := [] }

def finalFfi : HolFfiState Unit :=
  { oracle := finalOracle, ffiState := (), ioEvents := [] }

def sourceLocals : HolFiniteMapExact Nat (HolWordLab 64) :=
  HolFiniteMapExact.update
    (HolFiniteMapExact.update
      (HolFiniteMapExact.update
        (HolFiniteMapExact.update HolFiniteMapExact.empty
          (0, .word (BitVec.ofNat 64 1)))
        (1, .word (BitVec.ofNat 64 0)))
      (2, .word (BitVec.ofNat 64 1)))
    (3, .word (BitVec.ofNat 64 8))

def sourceState (ffi : HolFfiState Unit) (memaddrs : BitVec 64 → Prop) :
    CrepSemHOLState 64 Unit :=
  { locals := sourceLocals
    globals := HolFiniteMapExact.empty
    code := HolFiniteMapExact.empty
    memory := fun _ => .word 0
    memaddrs := memaddrs
    shMemaddrs := fun _ => False
    clock := 5
    be := false
    ffi := ffi
    baseAddr := 0
    topAddr := 100 }

def memDecTrue (ffi : HolFfiState Unit) :
    (address : BitVec 64) → Decidable ((sourceState ffi (fun _ => True)).memaddrs address) :=
  fun _ => isTrue trivial

def memDecFalse (ffi : HolFfiState Unit) :
    (address : BitVec 64) → Decidable ((sourceState ffi (fun _ => False)).memaddrs address) :=
  fun _ => isFalse (by simp [sourceState])

def shMemDec (ffi : HolFfiState Unit) (domain : BitVec 64 → Prop) :
    (address : BitVec 64) → Decidable ((sourceState ffi domain).shMemaddrs address) :=
  fun _ => isFalse (by simp [sourceState])

def extCallReturnedMatches : Bool :=
  let state := sourceState echoFfi (fun _ => True)
  match evalCrepSemHOLProg state (memDecTrue echoFfi)
      (shMemDec echoFfi (fun _ => True)) (.extCall (ofString "echo") 1 0 3 2 : CrepProgHOL 64) with
  | (none, post) =>
      post.memory 8 == .word (BitVec.ofNat 64 42) && post.ffi.ffiState == () &&
        post.ffi.ioEvents ==
          [{ name := .extCall (ofString "echo"), configuration := [BitVec.ofNat 8 0],
             bytes := [(BitVec.ofNat 8 0, BitVec.ofNat 8 42)] }]
  | _ => false

def extCallFinalMatches : Bool :=
  let state := sourceState finalFfi (fun _ => True)
  match evalCrepSemHOLProg state (memDecTrue finalFfi)
      (shMemDec finalFfi (fun _ => True)) (.extCall (ofString "live") 1 0 3 2 : CrepProgHOL 64) with
  | (some (.finalFfi event), post) =>
      event.name == .extCall (ofString "live") &&
        event.configuration == [BitVec.ofNat 8 0] &&
        event.bytes == [BitVec.ofNat 8 0] && event.outcome == .diverged &&
        post.memory 8 == .word 0 && post.ffi.ioEvents.isEmpty
  | _ => false

def extCallMissingLocalMatches : Bool :=
  let state := { sourceState echoFfi (fun _ => True) with
    locals := HolFiniteMapExact.resVarEq sourceLocals (0, none) }
  match evalCrepSemHOLProg state (memDecTrue echoFfi)
      (shMemDec echoFfi (fun _ => True)) (.extCall (ofString "echo") 1 0 3 2 : CrepProgHOL 64) with
  | (some .error, post) =>
      post.locals.lookup 0 == none && post.memory 8 == .word 0 &&
        post.ffi.ioEvents.isEmpty
  | _ => false

def extCallReadErrorMatches : Bool :=
  let state := sourceState echoFfi (fun _ => False)
  match evalCrepSemHOLProg state (memDecFalse echoFfi)
      (shMemDec echoFfi (fun _ => False)) (.extCall (ofString "echo") 1 0 3 2 : CrepProgHOL 64) with
  | (some .error, post) =>
      post.locals.lookup 0 == some (.word (BitVec.ofNat 64 1)) &&
        post.memory 8 == .word 0 && post.ffi.ioEvents.isEmpty
  | _ => false

#guard extCallReturnedMatches
#guard extCallFinalMatches
#guard extCallMissingLocalMatches
#guard extCallReadErrorMatches

def runChecks : IO Bool := do
  let ok := extCallReturnedMatches && extCallFinalMatches &&
    extCallMissingLocalMatches && extCallReadErrorMatches
  if extCallReturnedMatches then
    IO.println "PASS total Crep HOL ExtCall returned bytes and memory update match direct oracle"
  else
    IO.println "FAIL total Crep HOL ExtCall returned bytes and memory update match direct oracle"
  if extCallFinalMatches then
    IO.println "PASS total Crep HOL ExtCall final event preserves state"
  else
    IO.println "FAIL total Crep HOL ExtCall final event preserves state"
  if extCallMissingLocalMatches then
    IO.println "PASS total Crep HOL ExtCall missing-local Error preserves state"
  else
    IO.println "FAIL total Crep HOL ExtCall missing-local Error preserves state"
  if extCallReadErrorMatches then
    IO.println "PASS total Crep HOL ExtCall failed-read Error preserves state"
  else
    IO.println "FAIL total Crep HOL ExtCall failed-read Error preserves state"
  pure ok

end Flapjack.Test.CrepSemTotalExtCallParity
