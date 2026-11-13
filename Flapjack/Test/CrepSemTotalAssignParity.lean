module

public import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
@[expose] public section

/-! Regression cases for the exact total Crep Assign clause over the reviewed
   `CrepSemHOLState`/`CrepProgHOL` carriers. The direct HOL rows are generated
   by `scripts/hol-probes/crep_assign_eval_probeScript.sml`. -/

namespace Flapjack.Test.CrepSemTotalAssignParity

open Flapjack

def sampleState : CrepSemHOLState 64 Unit where
  locals := HolFiniteMapExact.update HolFiniteMapExact.empty
    (0, .word (BitVec.ofNat 64 7))
  globals := HolFiniteMapExact.empty
  code := HolFiniteMapExact.empty
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 5
  be := false
  ffi := { oracle := fun _ _ _ _ => .final .diverged, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 100

def memDec (address : BitVec 64) : Decidable (sampleState.memaddrs address) :=
  isFalse (by simp [sampleState])

def shMemDec (address : BitVec 64) : Decidable (sampleState.shMemaddrs address) :=
  isFalse (by simp [sampleState])

def assignOracleRowsMatch : Bool :=
  let state := sampleState
  let overwrite :=
    match evalCrepSemHOLProg state memDec shMemDec (.assign 0 (.const 9)) with
    | (none, post) => post.locals.lookup 0 == some (.word (BitVec.ofNat 64 9)) &&
        post.locals.lookup 1 == none && post.clock == state.clock &&
        post.globals.lookup 0 == state.globals.lookup 0 &&
        post.memory 0 == state.memory 0 &&
        post.baseAddr == state.baseAddr && post.topAddr == state.topAddr
    | _ => false
  let missingDestination :=
    match evalCrepSemHOLProg state memDec shMemDec (.assign 1 (.const 9)) with
    | (some .error, post) => post.locals.lookup 0 == state.locals.lookup 0 &&
        post.locals.lookup 1 == state.locals.lookup 1 && post.clock == state.clock
    | _ => false
  let badExpression :=
    match evalCrepSemHOLProg state memDec shMemDec (.assign 0 (.var 9)) with
    | (some .error, post) => post.locals.lookup 0 == state.locals.lookup 0 &&
        post.clock == state.clock
    | _ => false
  overwrite && missingDestination && badExpression

#guard assignOracleRowsMatch

theorem assignSuccessIsHolSetVar (state : CrepSemHOLState 64 Unit)
    (name : Nat) (value : CrepExpHOL 64)
    (wordLab : HolWordLab 64)
    (hvalue : evalCrepSemHOLExp state value = some wordLab)
    (hbound : ∃ old, state.locals.lookup name = some old) :
    evalCrepSemHOLProgExact state (.assign name value) =
      (none, CrepSemHOLState.setVar name wordLab state) := by
  rw [evalCrepSemHOLProgExact_assign_holShape]
  simp only [hvalue]
  obtain ⟨old, hold⟩ := hbound
  simp [hold, CrepSemHOLState.setVar]

theorem assignExpressionErrorKeepsFullState
    (state : CrepSemHOLState 64 Unit)
    (name : Nat) (value : CrepExpHOL 64)
    (hvalue : evalCrepSemHOLExp state value = none) :
    evalCrepSemHOLProgExact state (.assign name value) = (some .error, state) := by
  rw [evalCrepSemHOLProgExact_assign_holShape]
  simp only [hvalue]

theorem assignMissingDestinationKeepsFullState
    (state : CrepSemHOLState 64 Unit)
    (name : Nat) (value : CrepExpHOL 64)
    (wordLab : HolWordLab 64)
    (hvalue : evalCrepSemHOLExp state value = some wordLab)
    (hmissing : state.locals.lookup name = none) :
    evalCrepSemHOLProgExact state (.assign name value) = (some .error, state) := by
  rw [evalCrepSemHOLProgExact_assign_holShape]
  simp only [hvalue]
  simp [hmissing]

def runChecks : IO Bool := do
  if assignOracleRowsMatch then
    IO.println "PASS total Crep HOL Assign overwrite and Error clauses match direct oracle"
  else
    IO.println "FAIL total Crep HOL Assign overwrite and Error clauses match direct oracle"
  pure assignOracleRowsMatch

end Flapjack.Test.CrepSemTotalAssignParity
