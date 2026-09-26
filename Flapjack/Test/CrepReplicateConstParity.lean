import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.Semantics.CrepSem.ExecutedWordLabBridge

/-!
Direct runtime checks against `scripts/hol-probes/crep_replicate_const_probe.out`.
HOL's `pan_to_crepProofScript.sml:evaluate_replicate_const` evaluates a
`REPLICATE n (Const 0w)` argument list to `SOME (REPLICATE n (Word 0w))`.  The
checks below run the production `word_lab`-returning evaluator
`evalCrepRuntimeExpsWordLab` (no post-map) and compare its `PanWordLab` cells
against the recorded HOL rows.
-/

namespace Flapjack.Test.CrepReplicateConstParity

open Flapjack

def noNatMemory : Nat → PanWordLab Nat := fun _ => .word 0
def noNatDomain : Nat → Bool := fun _ => false

/-- Base state with empty locals/globals, matching the probe's `s with locals
:= FEMPTY`. -/
def baseState : CrepRuntimeState Nat Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    code := FEMPTY
    memory := noNatMemory
    memaddrs := noNatDomain
    shMemaddrs := noNatDomain
    memoryModel := natCrepRuntimeMemoryModel
    bytesInWord := 0
    ffiContext := natCrepRuntimeFfiContext
    clock := 3
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 12
    topAddress := 13 }

def evalConsts (values : List Nat) : Option (List (PanWordLab Nat)) :=
  evalCrepRuntimeExpsWordLab baseState (values.map (fun value => .const value))

/-- `replicate_const_one=SOME [Word 0w]`. -/
def oneGuard : Bool :=
  evalConsts [0] == some [.word 0]

/-- `replicate_const_three=SOME [Word 0w; Word 0w; Word 0w]`. -/
def threeGuard : Bool :=
  evalConsts [0, 0, 0] == some [.word 0, .word 0, .word 0]

/-- `replicate_const_empty=SOME []`. -/
def emptyGuard : Bool :=
  evalConsts [] == some []

/-- `replicate_const_nonzero=SOME [Word 9w; Word 9w]`. -/
def nonzeroGuard : Bool :=
  evalConsts [9, 9] == some [.word 9, .word 9]

def replicateConstGuard : Bool :=
  oneGuard && threeGuard && emptyGuard && nonzeroGuard

#guard replicateConstGuard

/-- The word_lab core instantiated concretely.  This core is untagged (the HOL
tag is withheld pending the arbitrary-runtime-hook mismatch tracked by bead
flapjack-pxn.18.4.3.48.1). -/
example : evalCrepRuntimeExpsWordLab baseState
    (List.replicate 3 (.const (0 : Nat))) = some [.word 0, .word 0, .word 0] :=
  evaluateReplicateConst 3 baseState

/-- Projection: the production evaluator read back through `PanWordLab.word`
equals the word_lab core, for a representative expression. -/
example :
    (evalCrepRuntimeExp baseState (.const (7 : Nat))).map PanWordLab.word =
      evalCrepRuntimeExpWordLab baseState (.const (7 : Nat)) :=
  evalCrepRuntimeExp_wordLab_projection baseState (.const (7 : Nat))

/-- Projection: the production list evaluator read back through `PanWordLab.word`
equals the word_lab list core. -/
example :
    (evalCrepRuntimeExps baseState [.const (1 : Nat), .const (2 : Nat)]).map
        (List.map PanWordLab.word) =
      evalCrepRuntimeExpsWordLab baseState [.const (1 : Nat), .const (2 : Nat)] :=
  evalCrepRuntimeExps_wordLab_projection baseState [.const (1 : Nat), .const (2 : Nat)]

/-- Faithful `CrepSemHOLState` for the exact-theorem rows. -/
def replicateFfi : HolFfiState Unit :=
  { oracle := fun _ state _ _ => .ret state []
    ffiState := ()
    ioEvents := [] }

def exactReplicateState : CrepSemHOLState 8 Unit where
  locals := HolFiniteMapExact.empty
  globals := HolFiniteMapExact.empty
  code := HolFiniteMapExact.empty
  memory := fun _ => .word (0 : BitVec 8)
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 0
  be := false
  ffi := replicateFfi
  baseAddr := 0
  topAddr := 0

local instance : DecidablePred exactReplicateState.memaddrs := by
  intro address
  change Decidable False
  infer_instance

/-- Exact labelled theorem instance over the faithful crepSem evaluator
(`evaluateReplicateConstHOL`): matches HOL row `replicate_const_three`. -/
example : (List.replicate 3 (CrepExpHOL.const (0 : BitVec 8))).mapM
    (evalCrepSemHOLExp exactReplicateState) =
      some (List.replicate 3 (HolWordLab.word (0 : BitVec 8))) :=
  evaluateReplicateConstHOL 3 exactReplicateState

/-- Guards for the exact theorem against `crep_replicate_const_probe.out` rows
`replicate_const_one`, `replicate_const_three`, `replicate_const_empty`. -/
def exactReplicateGuard : Bool :=
  ((List.replicate 1 (CrepExpHOL.const (0 : BitVec 8))).mapM
      (evalCrepSemHOLExp exactReplicateState) == some [.word (0 : BitVec 8)]) &&
  ((List.replicate 3 (CrepExpHOL.const (0 : BitVec 8))).mapM
      (evalCrepSemHOLExp exactReplicateState) ==
        some [.word (0 : BitVec 8), .word (0 : BitVec 8), .word (0 : BitVec 8)]) &&
  ((List.replicate 0 (CrepExpHOL.const (0 : BitVec 8))).mapM
      (evalCrepSemHOLExp exactReplicateState) == some [])

#guard exactReplicateGuard

/-- Executed-path bridge (`flapjack-pxn.18.4.3.48.1.21`): the production
`word_lab` list evaluator at the canonical BitVec evaluator state of the
faithful carrier returns the same replicated `word_lab` list as the tagged
exact `evalCrepSemHOLExp`, matching HOL row `replicate_const_three`. -/
example :
    evalCrepRuntimeExpsWordLab (executedCrepState exactReplicateState)
        (List.replicate 3 (CrepExp.const (0 : BitVec 8))) =
      some (List.replicate 3 (PanWordLab.word (0 : BitVec 8))) :=
  evalCrepRuntimeExpsWordLab_replicate_const_executed exactReplicateState 3 (0 : BitVec 8)

/-- Restatement of `evaluate_replicate_const` over the executed evaluator: the
production `word_lab` list context at the canonical BitVec evaluator state
equals the exact tagged `evaluateReplicateConstHOL` output transported through
`HolWordLab.toPanWordLab`. -/
example :
    evalCrepRuntimeExpsWordLab (executedCrepState exactReplicateState)
        (List.replicate 3 (CrepExp.const (0 : BitVec 8))) =
      ((List.replicate 3 (CrepExpHOL.const (0 : BitVec 8))).mapM
        (evalCrepSemHOLExp exactReplicateState)).map
        (List.map HolWordLab.toPanWordLab) := by
  rw [evaluateReplicateConstHOL]
  exact evalCrepRuntimeExpsWordLab_replicate_const_executed exactReplicateState 3 (0 : BitVec 8)

/-- Memory-free arithmetic fragment (`flapjack-pxn.18.4.3.48.1.21`): an `op`
expression is evaluated identically by the executed production evaluator and
the tagged exact `evalCrepSemHOLExp`, read through `holWordLabToWord`. -/
example :
    evalCrepRuntimeExp (executedCrepState exactReplicateState)
        (CrepExp.op BinOp.add [CrepExp.const (1 : BitVec 8), CrepExp.const (2 : BitVec 8)]) =
      (evalCrepSemHOLExp exactReplicateState
        (crepExpToHOL (CrepExp.op BinOp.add
          [CrepExp.const (1 : BitVec 8), CrepExp.const (2 : BitVec 8)]))).map
        holWordLabToWord :=
  evalCrepRuntimeExp_executed_of_noMemLoad exactReplicateState _
    (by simp [crepExpNoMemLoad])

/-- Memory-free fragment (`flapjack-pxn.18.4.3.48.1.21.1`): `cmp`, `shift`
and `crepOp` expressions are evaluated identically by the executed production
evaluator and the tagged exact `evalCrepSemHOLExp`, read through
`holWordLabToWord`. -/
example :
    evalCrepRuntimeExp (executedCrepState exactReplicateState)
        (CrepExp.cmp Cmp.equal (CrepExp.const (1 : BitVec 8)) (CrepExp.const (2 : BitVec 8))) =
      (evalCrepSemHOLExp exactReplicateState
        (crepExpToHOL (CrepExp.cmp Cmp.equal
          (CrepExp.const (1 : BitVec 8)) (CrepExp.const (2 : BitVec 8))))).map
        holWordLabToWord :=
  evalCrepRuntimeExp_executed_of_noMemLoad exactReplicateState _
    (by simp [crepExpNoMemLoad])

example :
    evalCrepRuntimeExp (executedCrepState exactReplicateState)
        (CrepExp.shift Shift.lsl (CrepExp.const (1 : BitVec 8)) (CrepExp.const (1 : BitVec 8))) =
      (evalCrepSemHOLExp exactReplicateState
        (crepExpToHOL (CrepExp.shift Shift.lsl
          (CrepExp.const (1 : BitVec 8)) (CrepExp.const (1 : BitVec 8))))).map
        holWordLabToWord :=
  evalCrepRuntimeExp_executed_of_noMemLoad exactReplicateState _
    (by simp [crepExpNoMemLoad])

example :
    evalCrepRuntimeExp (executedCrepState exactReplicateState)
        (CrepExp.crepOp CrepOp.mul [CrepExp.const (3 : BitVec 8), CrepExp.const (4 : BitVec 8)]) =
      (evalCrepSemHOLExp exactReplicateState
        (crepExpToHOL (CrepExp.crepOp CrepOp.mul
          [CrepExp.const (3 : BitVec 8), CrepExp.const (4 : BitVec 8)]))).map
        holWordLabToWord :=
  evalCrepRuntimeExp_executed_of_noMemLoad exactReplicateState _
    (by simp [crepExpNoMemLoad])

def runChecks : IO Bool := do
  IO.println s!"PASS crep evaluate_replicate_const word_lab shape"
  IO.println s!"PASS exact crepSem evaluate_replicate_const matches HOL oracle rows"
  IO.println s!"PASS executed crep word_lab evaluator agrees with exact evalCrepSemHOLExp on Const path"
  IO.println s!"PASS executed crep word_lab evaluator agrees with exact evalCrepSemHOLExp on memory-free fragment (op/cmp/shift/crepOp)"
  pure (replicateConstGuard && exactReplicateGuard)
end Flapjack.Test.CrepReplicateConstParity