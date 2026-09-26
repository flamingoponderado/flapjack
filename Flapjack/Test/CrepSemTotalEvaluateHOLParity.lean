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

/-- `true` when the result is `SOME (Exception v)`. -/
def resultIsException (v : BitVec 64) :
    Option (CrepResultHOL (BitVec 64) HolFinalEvent) → Bool
  | some (.exception e) => e == v
  | _ => false

/-- `true` when the result is `SOME TimeOut`. -/
def resultIsTimeOut :
    Option (CrepResultHOL (BitVec 64) HolFinalEvent) → Bool
  | some .timeOut => true
  | _ => false

/-- `true` when the result is `SOME (Return [Word v])`. -/
def resultIsReturnWord (v : BitVec 64) :
    Option (CrepResultHOL (BitVec 64) HolFinalEvent) → Bool
  | some (.return [.word w]) => w == v
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

/-- HOL `evaluate (Seq Skip Skip, s) = (NONE, s)`: `fix_clock` keeps the clock
    and the state passes through unchanged. -/
def seqEvalGuard : Bool :=
  resultIsNormal (run (.seq .skip .skip : CrepProgHOL 64)).1 &&
  (run (.seq .skip .skip : CrepProgHOL 64)).2.clock == 5 &&
  (run (.seq .skip .skip : CrepProgHOL 64)).2.locals.lookup 0 ==
    some (HolWordLab.word (BitVec.ofNat 64 7))

/-- HOL `evaluate (Dec 1 (Const 9) Skip, s)`: `res_var` restores the previous
    (absent) binding of `1`, so `locals 1 = NONE` and `locals 0 = 7` survives. -/
def decEvalGuard : Bool :=
  resultIsNormal (run (.dec 1 (.const (BitVec.ofNat 64 9)) .skip : CrepProgHOL 64)).1 &&
  (run (.dec 1 (.const (BitVec.ofNat 64 9)) .skip : CrepProgHOL 64)).2.clock == 5 &&
  (run (.dec 1 (.const (BitVec.ofNat 64 9)) .skip : CrepProgHOL 64)).2.locals.lookup 1 == none &&
  (run (.dec 1 (.const (BitVec.ofNat 64 9)) .skip : CrepProgHOL 64)).2.locals.lookup 0 ==
    some (HolWordLab.word (BitVec.ofNat 64 7))

/-- HOL `If` true: a nonzero `Word` condition selects the then-branch. -/
def ifTrueGuard : Bool :=
  resultIsBreak 4
    (run (.ite (.const (BitVec.ofNat 64 1)) (.break 4) (.continue 5) : CrepProgHOL 64)).1

/-- HOL `If` false: a zero `Word` condition selects the else-branch. -/
def ifFalseGuard : Bool :=
  resultIsContinue 5
    (run (.ite (.const (BitVec.ofNat 64 0)) (.break 4) (.continue 5) : CrepProgHOL 64)).1

/-- HOL `While` with a zero condition completes with `(NONE, s)`. -/
def whileFalseGuard : Bool :=
  resultIsNormal (run (.while (.const (BitVec.ofNat 64 0)) .skip : CrepProgHOL 64)).1 &&
  (run (.while (.const (BitVec.ofNat 64 0)) .skip : CrepProgHOL 64)).2.clock == 5

/-- HOL `While` clock exhaustion: a nonzero condition with `clock = 5` decrements
    through `dec_clock`/`fix_clock` until `clock = 0`, then `(SOME TimeOut,
    empty_locals s)`. This exercises the `dec_clock` step and the loop-control
    case analysis. -/
def whileTimeoutGuard : Bool :=
  resultIsTimeOut (run (.while (.const (BitVec.ofNat 64 1)) .skip : CrepProgHOL 64)).1 &&
  (run (.while (.const (BitVec.ofNat 64 1)) .skip : CrepProgHOL 64)).2.locals.lookup 0 == none

/-- HOL `Raise 42`: `(SOME (Exception 42), empty_locals s)`. -/
def raiseEvalGuard : Bool :=
  resultIsException 42 (run (.raise (BitVec.ofNat 64 42) : CrepProgHOL 64)).1 &&
  (run (.raise (BitVec.ofNat 64 42) : CrepProgHOL 64)).2.locals.lookup 0 == none

/-- HOL `Return [Const 5]`: `(SOME (Return [Word 5]), empty_locals s)`. -/
def returnEvalGuard : Bool :=
  resultIsReturnWord 5 (run (.return [.const (BitVec.ofNat 64 5)] : CrepProgHOL 64)).1 &&
  (run (.return [.const (BitVec.ofNat 64 5)] : CrepProgHOL 64)).2.locals.lookup 0 == none

/-- HOL `Tick`: at `clock = 5` returns `(NONE, dec_clock s)`, so the clock drops
    to `4`. -/
def tickEvalGuard : Bool :=
  resultIsNormal (run (.tick : CrepProgHOL 64)).1 &&
  (run (.tick : CrepProgHOL 64)).2.clock == 4

def holOracleRowsMatch : Bool :=
  skipEvalGuard && breakEvalGuard && continueEvalGuard && seqEvalGuard &&
  decEvalGuard && ifTrueGuard && ifFalseGuard && whileFalseGuard &&
  whileTimeoutGuard && raiseEvalGuard && returnEvalGuard && tickEvalGuard

#guard holOracleRowsMatch

/-- Kernel-checked full pair equality for the Skip constructor, i.e. HOL
    `evaluate (Skip, s) = (NONE, s)` with the state carried through literally. -/
theorem skipFullState :
    evalCrepSemHOLProg sampleHOLState memDecSample shMemDecSample
        (.skip : CrepProgHOL 64) = (none, sampleHOLState) :=
  evalCrepSemHOLProg_skip sampleHOLState memDecSample shMemDecSample

/-- Kernel-checked full pair equality for Break via the named equation. -/
theorem breakFullState :
    evalCrepSemHOLProg sampleHOLState memDecSample shMemDecSample
        (.break 3 : CrepProgHOL 64) =
      (some (CrepResultHOL.break 3), sampleHOLState) :=
  evalCrepSemHOLProg_break sampleHOLState memDecSample shMemDecSample 3

/-- Kernel-checked full pair equality for Continue via the named equation. -/
theorem continueFullState :
    evalCrepSemHOLProg sampleHOLState memDecSample shMemDecSample
        (.continue 3 : CrepProgHOL 64) =
      (some (CrepResultHOL.continue 3), sampleHOLState) :=
  evalCrepSemHOLProg_continue sampleHOLState memDecSample shMemDecSample 3

/-- Kernel-checked full pair equality for Raise via the named equation. -/
theorem raiseFullState :
    evalCrepSemHOLProg sampleHOLState memDecSample shMemDecSample
        (.raise (BitVec.ofNat 64 42) : CrepProgHOL 64) =
      (some (CrepResultHOL.exception (BitVec.ofNat 64 42)),
        CrepSemHOLState.emptyLocals sampleHOLState) :=
  evalCrepSemHOLProg_raise sampleHOLState memDecSample shMemDecSample _

/-- Kernel-checked Tick equation at `clock = 5`. -/
theorem tickFullState :
    evalCrepSemHOLProg sampleHOLState memDecSample shMemDecSample
        (.tick : CrepProgHOL 64) = (none, decClockCrepSemHOL sampleHOLState) := by
  rw [evalCrepSemHOLProg_tick]
  simp [sampleHOLState]

/-- `Const 0` evaluates to `Word 0`. -/
theorem constZeroEval :
    crepExactEvalExp sampleHOLState memDecSample (.const (BitVec.ofNat 64 0)) =
      some (HolWordLab.word (BitVec.ofNat 64 0)) := by
  simp [crepExactEvalExp, evalCrepSemHOLExp]

/-- `Const 1` evaluates to `Word 1`. -/
theorem constOneEval :
    crepExactEvalExp sampleHOLState memDecSample (.const (BitVec.ofNat 64 1)) =
      some (HolWordLab.word (BitVec.ofNat 64 1)) := by
  simp [crepExactEvalExp, evalCrepSemHOLExp]

/-- Kernel-checked While-false equation using the named constructor equation. -/
theorem whileFalseFullState :
    evalCrepSemHOLProg sampleHOLState memDecSample shMemDecSample
        (.while (.const (BitVec.ofNat 64 0)) (.skip : CrepProgHOL 64)) =
      (none, sampleHOLState) :=
  evalCrepSemHOLProg_while_false sampleHOLState memDecSample shMemDecSample
    _ _ _ constZeroEval rfl

/-- Kernel-checked If-true equation using the named constructor equation. -/
theorem iteTrueFullState :
    evalCrepSemHOLProg sampleHOLState memDecSample shMemDecSample
        (.ite (.const (BitVec.ofNat 64 1)) (.break 4) (.continue 5) : CrepProgHOL 64) =
      evalCrepSemHOLProg sampleHOLState memDecSample shMemDecSample
        (.break 4 : CrepProgHOL 64) :=
  evalCrepSemHOLProg_ite_true sampleHOLState memDecSample shMemDecSample
    _ _ _ _ constOneEval (by decide)

/-- Kernel-checked Seq equation, discharging the `fix_clock` pass-through. -/
theorem seqSkipSkipFullState {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)) :
    evalCrepSemHOLProg state memDec shMemDec (.seq .skip .skip : CrepProgHOL width) =
      (none, state) := by
  rw [evalCrepSemHOLProg_seq, evalCrepSemHOLProg_skip]
  simp only [fixClockCrepSemHOL]
  simp only [crepStampExactDomains]
  rw [evalCrepSemHOLProg_skip]
  simp [Nat.lt_irrefl]

/-- Kernel-checked domain-preservation instance on the concrete sample state:
    the evaluator result carries the input `memaddrs`. -/
theorem whilePreservesMemaddrs :
    (evalCrepSemHOLProg sampleHOLState memDecSample shMemDecSample
        (.while (.const (BitVec.ofNat 64 1)) .skip : CrepProgHOL 64)).2.memaddrs =
      sampleHOLState.memaddrs :=
  evalCrepSemHOLProg_preserves_memaddrs sampleHOLState memDecSample shMemDecSample _

/-- Kernel-checked domain-preservation instance for `shMemaddrs`. -/
theorem whilePreservesShMemaddrs :
    (evalCrepSemHOLProg sampleHOLState memDecSample shMemDecSample
        (.while (.const (BitVec.ofNat 64 1)) .skip : CrepProgHOL 64)).2.shMemaddrs =
      sampleHOLState.shMemaddrs :=
  evalCrepSemHOLProg_preserves_shMemaddrs sampleHOLState memDecSample shMemDecSample _

/-- Kernel-checked recursive-state equality: the `crepStampExactDomains` call the
    `While` clause performs on the produced state is the identity, so threading
    the base state's decision procedures is sound. -/
theorem whileStampIdentity :
    crepStampExactDomains sampleHOLState
      (evalCrepSemHOLProg sampleHOLState memDecSample shMemDecSample
        (.while (.const (BitVec.ofNat 64 1)) .skip : CrepProgHOL 64)).2 =
      (evalCrepSemHOLProg sampleHOLState memDecSample shMemDecSample
        (.while (.const (BitVec.ofNat 64 1)) .skip : CrepProgHOL 64)).2 :=
  crepStampExactDomains_evalCrepSemHOLProg sampleHOLState memDecSample shMemDecSample _

def runChecks : IO Bool := do
  if holOracleRowsMatch then
    IO.println "PASS crepSem total HOL-shaped evaluate Skip/Break/Continue/Seq/Dec/If/While/Raise/Return/Tick match direct crep_inline_eval_probe oracle"
  else
    IO.println "FAIL crepSem total HOL-shaped evaluate Skip/Break/Continue/Seq/Dec/If/While/Raise/Return/Tick match direct crep_inline_eval_probe oracle"
  pure holOracleRowsMatch

end Flapjack.Test.CrepSemTotalEvaluateHOLParity
