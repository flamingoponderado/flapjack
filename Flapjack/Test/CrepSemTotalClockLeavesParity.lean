module

public import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
@[expose] public section

/-! Regression cases for the exact total Crep evaluator over the reviewed
   `CrepSemHOLState`/`CrepProgHOL` carriers. The HOL oracle rows are generated
   by `scripts/hol-probes/crep_clock_leaf_eval_probeScript.sml`.
-/

namespace Flapjack.Test.CrepSemTotalClockLeavesParity

open Flapjack

def sampleState (clock : Nat) : CrepSemHOLState 64 Unit :=
  { locals := HolFiniteMapExact.update HolFiniteMapExact.empty
      (0, .word (BitVec.ofNat 64 7))
    globals := HolFiniteMapExact.empty
    code := HolFiniteMapExact.empty
    memory := fun _ => .word 0
    memaddrs := fun _ => False
    shMemaddrs := fun _ => False
    clock := clock
    be := false
    ffi := { oracle := fun _ _ _ _ => .final .diverged, ffiState := (), ioEvents := [] }
    baseAddr := 0
    topAddr := 100 }

def memDec (clock : Nat) :
    (value : BitVec 64) → Decidable ((sampleState clock).memaddrs value) :=
  fun _ => isFalse (by simp [sampleState])

def shMemDec (clock : Nat) :
    (value : BitVec 64) → Decidable ((sampleState clock).shMemaddrs value) :=
  fun _ => isFalse (by simp [sampleState])

def ifOracleRowsMatch : Bool :=
  let state := sampleState 5
  let trueBranch : CrepProgHOL 64 := .ite (.const 5) (.break 3) .skip
  let falseBranch : CrepProgHOL 64 := .ite (.const 0) (.break 3) (.continue 4)
  let errorBranch : CrepProgHOL 64 := .ite (.var 9) .skip (.break 5)
  let nestedBranch : CrepProgHOL 64 :=
    .ite (.const 1) (.ite (.const 0) .skip (.break 6)) (.continue 4)
  let trueOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5) trueBranch with
    | (some (.break 3), post) => post.clock == 5 &&
        post.locals.lookup 0 == some (.word (BitVec.ofNat 64 7))
    | _ => false
  let falseOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5) falseBranch with
    | (some (.continue 4), post) => post.clock == 5
    | _ => false
  let errorOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5) errorBranch with
    | (some .error, post) => post.clock == 5 &&
        post.locals.lookup 0 == some (.word (BitVec.ofNat 64 7))
    | _ => false
  let nestedOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5) nestedBranch with
    | (some (.break 6), post) => post.clock == 5
    | _ => false
  trueOk && falseOk && errorOk && nestedOk

def seqOracleRowsMatch : Bool :=
  let state := sampleState 5
  let zero := sampleState 0
  let normalOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.seq .skip (.break 7)) with
    | (some (.break 7), post) => post.clock == 5
    | _ => false
  let controlOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.seq (.break 8) .tick) with
    | (some (.break 8), post) => post.clock == 5
    | _ => false
  let tickOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.seq .tick .skip) with
    | (none, post) => post.clock == 4 &&
        post.locals.lookup 0 == some (.word (BitVec.ofNat 64 7))
    | _ => false
  let timeoutOk := match evalCrepSemHOLProg zero (memDec 0) (shMemDec 0)
      (.seq .tick .skip) with
    | (some .timeOut, post) => post.clock == 0 && post.locals.lookup 0 == none
    | _ => false
  let raisedClock := { state with clock := 7 }
  let clampOk :=
    (fixClockCrepSemHOL state
      ((none : Option (CrepResultHOLExact 64)), raisedClock)).2.clock == 5
  normalOk && controlOk && tickOk && timeoutOk && clampOk

def returnOracleRowsMatch : Bool :=
  let state := sampleState 5
  let wordOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.return [.const 9]) with
    | (some (.return [.word (BitVec.ofNat 64 9)]), post) =>
        post.clock == 5 && post.locals.lookup 0 == none
    | _ => false
  let emptyOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.return ([] : List (CrepExpHOL 64))) with
    | (some (.return []), post) => post.clock == 5 && post.locals.lookup 0 == none
    | _ => false
  let errorOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.return [.var 9]) with
    | (some .error, post) => post.clock == 5 &&
        post.locals.lookup 0 == some (.word (BitVec.ofNat 64 7))
    | _ => false
  wordOk && emptyOk && errorOk

def raiseOracleRowMatches : Bool :=
  let state := sampleState 5
  match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.raise (BitVec.ofNat 64 9)) with
  | (some (.exception (BitVec.ofNat 64 9)), post) =>
      post.clock == 5 && post.locals.lookup 0 == none &&
        post.globals.lookup 0 == none &&
        post.memory 0 == .word 0 && post.baseAddr == 0 && post.topAddr == 100
  | _ => false

def decOracleRowsMatch : Bool :=
  let state := sampleState 5
  let shadowOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.dec 0 (.const 9) .skip) with
    | (none, post) => post.clock == 5 &&
        post.locals.lookup 0 == some (.word (BitVec.ofNat 64 7))
    | _ => false
  let newOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.dec 1 (.const 9) .skip) with
    | (none, post) => post.clock == 5 && post.locals.lookup 1 == none &&
        post.locals.lookup 0 == some (.word (BitVec.ofNat 64 7))
    | _ => false
  let errorOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.dec 0 (.var 9) .skip) with
    | (some .error, post) => post.clock == 5 &&
        post.locals.lookup 0 == some (.word (BitVec.ofNat 64 7))
    | _ => false
  shadowOk && newOk && errorOk

def whileOracleRowsMatch : Bool :=
  let state := sampleState 5
  let zero := sampleState 0
  let falseOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.while (.const 0) .skip) with
    | (none, post) => post.clock == 5 &&
        post.locals.lookup 0 == some (.word (BitVec.ofNat 64 7))
    | _ => false
  let errorOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.while (.var 9) .skip) with
    | (some .error, post) => post.clock == 5 &&
        post.locals.lookup 0 == some (.word (BitVec.ofNat 64 7))
    | _ => false
  let timeoutOk := match evalCrepSemHOLProg zero (memDec 0) (shMemDec 0)
      (.while (.const 1) .skip) with
    | (some .timeOut, post) => post.clock == 0 && post.locals.lookup 0 == none
    | _ => false
  let recursionOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.while (.var 0) (.assign 0 (.const 0))) with
    | (none, post) => post.clock == 4 &&
        post.locals.lookup 0 == some (.word (BitVec.ofNat 64 0))
    | _ => false
  let breakZeroOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.while (.const 1) (.break 0)) with
    | (none, post) => post.clock == 4 &&
        post.locals.lookup 0 == some (.word (BitVec.ofNat 64 7))
    | _ => false
  let breakLabelOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.while (.const 1) (.break 1)) with
    | (some (.break 0), post) => post.clock == 4
    | _ => false
  let continueLabelOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.while (.const 1) (.continue 1)) with
    | (some (.continue 0), post) => post.clock == 4
    | _ => false
  falseOk && errorOk && timeoutOk && recursionOk && breakZeroOk &&
    breakLabelOk && continueLabelOk

#guard ifOracleRowsMatch
#guard seqOracleRowsMatch
#guard returnOracleRowsMatch
#guard raiseOracleRowMatches
#guard decOracleRowsMatch
#guard whileOracleRowsMatch

theorem skipFullState (state : CrepSemHOLState 64 Unit) :
    evalCrepSemHOLProgExact state (.skip : CrepProgHOL 64) = (none, state) :=
  evalCrepSemHOLProgExact_skip state

theorem breakFullState (state : CrepSemHOLState 64 Unit) :
    evalCrepSemHOLProgExact state (.break 3 : CrepProgHOL 64) =
      (some (.break 3), state) :=
  evalCrepSemHOLProgExact_break state 3

theorem continueFullState (state : CrepSemHOLState 64 Unit) :
    evalCrepSemHOLProgExact state (.continue 2 : CrepProgHOL 64) =
      (some (.continue 2), state) :=
  evalCrepSemHOLProgExact_continue state 2

theorem tickZeroFullState (state : CrepSemHOLState 64 Unit)
    (hclock : state.clock = 0) :
    evalCrepSemHOLProgExact state (.tick : CrepProgHOL 64) =
      (some .timeOut, CrepSemHOLState.emptyLocals state) := by
  rw [evalCrepSemHOLProgExact_tick, if_pos hclock]

theorem tickPositiveFullState (state : CrepSemHOLState 64 Unit)
    (hclock : state.clock ≠ 0) :
    evalCrepSemHOLProgExact state (.tick : CrepProgHOL 64) =
      (none, decClockCrepSemHOL state) := by
  rw [evalCrepSemHOLProgExact_tick, if_neg hclock]

def holOracleRowsMatch : Bool :=
  let state := sampleState 5
  let zero := sampleState 0
  let skipOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5) .skip with
    | (none, post) => post.clock == 5 &&
        post.locals.lookup 0 == some (.word (BitVec.ofNat 64 7))
    | _ => false
  let breakOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5) (.break 1) with
    | (some (.break 1), post) => post.clock == 5
    | _ => false
  let continueOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5)
      (.continue 2) with
    | (some (.continue 2), post) => post.clock == 5
    | _ => false
  let tickZeroOk := match evalCrepSemHOLProg zero (memDec 0) (shMemDec 0) .tick with
    | (some .timeOut, post) => post.clock == 0 && post.locals.lookup 0 == none
    | _ => false
  let tickPositiveOk := match evalCrepSemHOLProg state (memDec 5) (shMemDec 5) .tick with
    | (none, post) => post.clock == 4 &&
        post.locals.lookup 0 == some (.word (BitVec.ofNat 64 7))
    | _ => false
  skipOk && breakOk && continueOk && tickZeroOk && tickPositiveOk

#guard holOracleRowsMatch

def runChecks : IO Bool := do
  if holOracleRowsMatch then
    IO.println "PASS total Crep HOL clock leaves match direct Skip/Break/Continue/Tick oracle"
  else
    IO.println "FAIL total Crep HOL clock leaves match direct Skip/Break/Continue/Tick oracle"
  if ifOracleRowsMatch then
    IO.println "PASS total Crep HOL If true/false/error/nested clauses match direct oracle"
  else
    IO.println "FAIL total Crep HOL If true/false/error/nested clauses match direct oracle"
  if seqOracleRowsMatch then
    IO.println "PASS total Crep HOL Seq fix_clock normal/control/timeout clauses match direct oracle"
  else
    IO.println "FAIL total Crep HOL Seq fix_clock normal/control/timeout clauses match direct oracle"
  if returnOracleRowsMatch then
    IO.println "PASS total Crep HOL Return values/empty/error clauses match direct oracle"
  else
    IO.println "FAIL total Crep HOL Return values/empty/error clauses match direct oracle"
  if raiseOracleRowMatches then
    IO.println "PASS total Crep HOL Raise exception/empty-locals clause matches direct oracle"
  else
    IO.println "FAIL total Crep HOL Raise exception/empty-locals clause matches direct oracle"
  if decOracleRowsMatch then
    IO.println "PASS total Crep HOL Dec bind/restore/error clauses match direct oracle"
  else
    IO.println "FAIL total Crep HOL Dec bind/restore/error clauses match direct oracle"
  if whileOracleRowsMatch then
    IO.println "PASS total Crep HOL While condition/clock/recursion/control clauses match direct oracle"
  else
    IO.println "FAIL total Crep HOL While condition/clock/recursion/control clauses match direct oracle"
  pure (holOracleRowsMatch && ifOracleRowsMatch && seqOracleRowsMatch &&
    returnOracleRowsMatch && raiseOracleRowMatches && decOracleRowsMatch &&
    whileOracleRowsMatch)

end Flapjack.Test.CrepSemTotalClockLeavesParity
