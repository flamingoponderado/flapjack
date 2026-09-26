import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL

/-!
Regression for the total HOL-shaped `crepSem$evaluate` over the exact
`CrepProgHOL`/`CrepSemHOLState` carriers.

The oracle row is transcribed from
`scripts/hol-probes/crep_inline_eval_probe.out`: `skip_eval=T`, i.e. HOL
`evaluate (Skip, s) = (NONE, s)`. The same probe also records
`break_eval=T` and `continue_eval=T`. The evaluator is untagged, so these are
declaration-local infrastructure regressions, not a whole-program HOL claim.
-/

namespace Flapjack.Test.CrepSemTotalEvaluateHOLParity

open Flapjack

/-- A concrete 64-bit finite-support HOL state with `locals 0 = 7`, matching the
    probe's `s` (up to the irrelevant code/derived fields). -/
def sampleHOLState : CrepSemHOLState 64 Unit where
  locals := HolFiniteMapExact.update HolFiniteMapExact.empty
    (0, .word (BitVec.ofNat 64 7))
  globals := HolFiniteMapExact.empty
  code := HolFiniteMapExact.empty
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 5
  be := false
  ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 100

def memDecSample (a : BitVec 64) : Decidable (sampleHOLState.memaddrs a) :=
  isFalse (by simp [sampleHOLState])

def shMemDecSample (a : BitVec 64) : Decidable (sampleHOLState.shMemaddrs a) :=
  isFalse (by simp [sampleHOLState])

def run (program : CrepProgHOL 64) :
    Option (CrepResultHOL (BitVec 64) HolFinalEvent) × CrepSemHOLState 64 Unit :=
  evalCrepSemHOLProg sampleHOLState memDecSample shMemDecSample program

/-- `true` when the result is HOL `NONE` (ordinary completion). -/
def resultIsNormal :
    Option (CrepResultHOL (BitVec 64) HolFinalEvent) → Bool
  | none => true
  | _ => false

/-- `true` when the result is `SOME (Break n)`. -/
def resultIsBreak (n : Nat) :
    Option (CrepResultHOL (BitVec 64) HolFinalEvent) → Bool
  | some (.break m) => m == n
  | _ => false

/-- `true` when the result is `SOME (Continue n)`. -/
def resultIsContinue (n : Nat) :
    Option (CrepResultHOL (BitVec 64) HolFinalEvent) → Bool
  | some (.continue m) => m == n
  | _ => false

/-- `skip_eval=T`: the result is HOL `NONE` and the state is unchanged. -/
def skipEvalGuard : Bool :=
  resultIsNormal (run (.skip : CrepProgHOL 64)).1 &&
  (run (.skip : CrepProgHOL 64)).2.clock == 5 &&
  (run (.skip : CrepProgHOL 64)).2.locals.lookup 0 ==
    some (HolWordLab.word (BitVec.ofNat 64 7))

/-- `break_eval=T`: `evaluate (Break 1, s) = (SOME (Break 1), s)`. -/
def breakEvalGuard : Bool :=
  resultIsBreak 1 (run (.break 1)).1 && (run (.break 1)).2.clock == 5

/-- `continue_eval=T`: `evaluate (Continue 2, s) = (SOME (Continue 2), s)`. -/
def continueEvalGuard : Bool :=
  resultIsContinue 2 (run (.continue 2)).1 && (run (.continue 2)).2.clock == 5

def holOracleRowsMatch : Bool :=
  skipEvalGuard && breakEvalGuard && continueEvalGuard

#guard holOracleRowsMatch

/-- Kernel-checked full pair equality for the Skip constructor, i.e. HOL
    `evaluate (Skip, s) = (NONE, s)` with the state carried through literally. -/
theorem skipFullState :
    evalCrepSemHOLProg sampleHOLState memDecSample shMemDecSample
        (.skip : CrepProgHOL 64) = (none, sampleHOLState) :=
  evalCrepSemHOLProg_skip sampleHOLState memDecSample shMemDecSample

/-- Kernel-checked full pair equality for Break, from the evaluator definition. -/
theorem breakFullState :
    evalCrepSemHOLProg sampleHOLState memDecSample shMemDecSample
        (.break 3 : CrepProgHOL 64) =
      (some (CrepResultHOL.break 3), sampleHOLState) := by
  simp [evalCrepSemHOLProg]

def runChecks : IO Bool := do
  if holOracleRowsMatch then
    IO.println "PASS crepSem total HOL-shaped evaluate Skip/Break/Continue match direct crep_inline_eval_probe oracle"
  else
    IO.println "FAIL crepSem total HOL-shaped evaluate Skip/Break/Continue match direct crep_inline_eval_probe oracle"
  pure holOracleRowsMatch

end Flapjack.Test.CrepSemTotalEvaluateHOLParity
