module

public import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
@[expose] public section

/-! Direct regression cases for the supported exact source-code-map Call
    fragment over the reviewed `CrepSemHOLState`/`CrepProgHOL` carriers.
    Oracle rows come from crep_total_call_eval_probeScript.sml. -/

namespace Flapjack.Test.CrepSemTotalCallParity

open Flapjack
open Flapjack.Basis.Pure.MlString

def callState (clock : Nat) : CrepSemHOLState 64 Unit :=
  { locals := HolFiniteMapExact.update
      (HolFiniteMapExact.update HolFiniteMapExact.empty
        (0, .word (BitVec.ofNat 64 7)))
      (1, .word (BitVec.ofNat 64 3))
    globals := HolFiniteMapExact.empty
    code := HolFiniteMapExact.update HolFiniteMapExact.empty
      (ofString "id", ([0], .return [.var 0]))
    memory := fun _ => .word 0
    memaddrs := fun _ => False
    shMemaddrs := fun _ => False
    clock := clock
    be := false
    ffi := { oracle := fun _ _ _ _ => .final .diverged, ffiState := (), ioEvents := [] }
    baseAddr := 0
    topAddr := 100 }

def callStateWith (clock : Nat) (function : MlString) (parameters : List Nat)
    (body : CrepProgHOL 64) : CrepSemHOLState 64 Unit :=
  { callState clock with
    code := HolFiniteMapExact.update HolFiniteMapExact.empty
      (function, (parameters, body)) }

def memDec (clock : Nat) :
    (value : BitVec 64) → Decidable ((callState clock).memaddrs value) :=
  fun _ => isFalse (by simp [callState])

def shMemDec (clock : Nat) :
    (value : BitVec 64) → Decidable ((callState clock).shMemaddrs value) :=
  fun _ => isFalse (by simp [callState])

def callOracleRowsMatch : Bool :=
  let state := callState 5
  let zero := callState 0
  let success := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.call none (ofString "id") [.const 9] : CrepProgHOL 64) with
    | (some (.return [.word (BitVec.ofNat 64 9)]), post) =>
        post.clock == 4 && post.locals.lookup 0 == none &&
          (match post.code.lookup (ofString "id") with
          | some ([0], .return [.var 0]) => true
          | _ => false)
    | _ => false
  let destinations := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.call (some ([1], none)) (ofString "id") [.const 9] : CrepProgHOL 64) with
    | (none, post) => post.clock == 4 &&
        post.locals.lookup 0 == some (.word (BitVec.ofNat 64 7)) &&
        post.locals.lookup 1 == some (.word (BitVec.ofNat 64 9))
    | _ => false
  let missing := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.call none (ofString "missing") [.const 9] : CrepProgHOL 64) with
    | (some .error, post) => post.clock == 5 &&
        post.locals.lookup 0 == state.locals.lookup 0
    | _ => false
  let arity := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.call none (ofString "id") [] : CrepProgHOL 64) with
    | (some .error, post) => post.clock == 5 &&
        post.locals.lookup 1 == state.locals.lookup 1
    | _ => false
  let timeout := match evalCrepSemHOLProg zero (memDec 0) (shMemDec 0)
      (.call none (ofString "id") [.const 9] : CrepProgHOL 64) with
    | (some .timeOut, post) => post.clock == 0 && post.locals.lookup 0 == none
    | _ => false
  let normal := match evalCrepSemHOLProg (callStateWith 5 (ofString "worker") [] .skip)
      (memDec 5) (shMemDec 5)
      (.call none (ofString "worker") [] : CrepProgHOL 64) with
    | (some .error, post) => post.clock == 4 && post.locals.lookup 0 == none
    | _ => false
  let breaking := match evalCrepSemHOLProg
      (callStateWith 5 (ofString "worker") [] (.break 0)) (memDec 5) (shMemDec 5)
      (.call none (ofString "worker") [] : CrepProgHOL 64) with
    | (some .error, post) => post.clock == 4 && post.locals.lookup 0 == none
    | _ => false
  let continuing := match evalCrepSemHOLProg
      (callStateWith 5 (ofString "worker") [] (.continue 0)) (memDec 5) (shMemDec 5)
      (.call none (ofString "worker") [] : CrepProgHOL 64) with
    | (some .error, post) => post.clock == 4 && post.locals.lookup 0 == none
    | _ => false
  let exception := match evalCrepSemHOLProg
      (callStateWith 5 (ofString "worker") [] (.raise (BitVec.ofNat 64 3)))
      (memDec 5) (shMemDec 5)
      (.call none (ofString "worker") [] : CrepProgHOL 64) with
    | (some (.exception (BitVec.ofNat 64 3)), post) =>
        post.clock == 4 && post.locals.lookup 0 == none
    | _ => false
  let returnArity := match evalCrepSemHOLProg
      (callStateWith 5 (ofString "ret") [] (.return [.const 9])) (memDec 5) (shMemDec 5)
      (.call (some ([1, 2], none)) (ofString "ret") [] : CrepProgHOL 64) with
    | (some .error, post) => post.clock == 4 && post.locals.lookup 0 == none
    | _ => false
  let duplicateDestinations := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.call (some ([1, 1], none)) (ofString "id") [.const 9] : CrepProgHOL 64) with
    | (some .error, post) => post.clock == 5 &&
        post.locals.lookup 0 == state.locals.lookup 0
    | _ => false
  let missingDestination := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.call (some ([9], none)) (ofString "id") [.const 9] : CrepProgHOL 64) with
    | (some .error, post) => post.clock == 4 && post.locals.lookup 0 == none
    | _ => false
  success && destinations && missing && arity && timeout && normal &&
    breaking && continuing && exception && returnArity &&
    duplicateDestinations && missingDestination

#guard callOracleRowsMatch

def runChecks : IO Bool := do
  if callOracleRowsMatch then
    IO.println "PASS total Crep Call evaluates state-owned code entries and matches direct HOL rows"
  else
    IO.println "FAIL total Crep Call evaluates state-owned code entries and matches direct HOL rows"
  pure callOracleRowsMatch

end Flapjack.Test.CrepSemTotalCallParity
