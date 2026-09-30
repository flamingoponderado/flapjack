import Flapjack.RiscV.OracleAllocator
import Flapjack.RiscV.WordDeadCode

/-! Direct HOL parity for CakeML `total_colour` followed by `apply_colour`.
    The source fixture is `scripts/hol-probes/apply_colour_probe.out`. -/

namespace Flapjack.Test.CakeApplyColourParity

open Flapjack

def oracle : NatInfoMap Nat := [(1, 7), (3, 9)]

def totalColourExact : Bool :=
  wordOracleColour oracle 1 == 14 &&
    wordOracleColour oracle 2 == 2 &&
    wordOracleColour oracle 7 == 0

#guard totalColourExact

def assignExact : Bool :=
  match wordApplyTotalColour oracle
      (.assign 1 (.var 3) : WordProg Nat) with
  | .assign name (.var source) => name == 14 && source == 18
  | _ => false

#guard assignExact

def aliasColour (name : Nat) : Nat := if name = 0 then 0 else 1

def applyColourAliasedAssignExact : Bool :=
  match wordApplyColour aliasColour (.assign 2 (.var 1) : WordProg Nat) with
  | .assign name (.var source) => name == 1 && source == 1
  | _ => false

#guard applyColourAliasedAssignExact

def returnRaiseExact : Bool :=
  match wordApplyTotalColour oracle
      (.seq (.return 1 [3, 5]) (.raise 7) : WordProg Nat) with
  | .seq (.return label values) (.raise exception) =>
      label == 14 && values == [18, 0] && exception == 0
  | _ => false

#guard returnRaiseExact

def callHandlerExact : Bool :=
  match wordApplyTotalColour oracle
      (.call
        (some ([1], ([3], [5]), .return 1 [3], 10, 11))
        (some 12) [1, 3]
        (some (7, .raise 3, 13, 14)) : WordProg Nat) with
  | .call (some (values, (normal, exception), .return label returned,
      returnLabel, entryLabel)) (some target) arguments
      (some (handlerException, .raise raised, handlerLabel, handlerEntry)) =>
      values == [14] && normal == [18] && exception == [0] &&
        label == 14 && returned == [18] && returnLabel == 10 &&
        entryLabel == 11 && target == 12 && arguments == [14, 18] &&
        handlerException == 0 && raised == 18 && handlerLabel == 13 &&
        handlerEntry == 14
  | _ => false

#guard callHandlerExact

def loopLiveExact : Bool :=
  match wordApplyTotalColour oracle
      (.loop [1, 7] (.assign 1 (.var 3)) [3] : WordProg Nat) with
  | .loop liveIn (.assign name (.var source)) liveOut =>
      liveIn == [0, 14] && name == 14 && source == 18 && liveOut == [18]
  | _ => false

#guard loopLiveExact

/-- Original `apply_colour_exp_def` EVAL rows in
`scripts/hol-probes/word_alloc_colour_exp_probe.out`. The test executable
calls `wordApplyColourExp`, including its kernel-proved compiler rewrite. -/
def expressionColourExact : Bool :=
  let nested : WordExp (BitVec 8) := .op .add
    [.const 7, .load (.var 3), .lookup (.temp (BitVec.ofNat 5 9)),
      .shift .lsl (.var 5) (.var 6)]
  let nestedOK := match wordApplyColourExp (fun n => n + 10) nested with
    | .op .add [.const v, .load (.var n), .lookup (.temp t),
        .shift .lsl (.var left) (.var right)] =>
        v == 7 && n == 13 && t == BitVec.ofNat 5 9 && left == 15 && right == 16
    | _ => false
  let duplicateOK := match wordApplyColourExp (fun n => n % 2)
      (.op .sub [.var 3, .var 3, .var 4] : WordExp (BitVec 8)) with
    | .op .sub [.var a, .var b, .var c] => a == 1 && b == 1 && c == 0
    | _ => false
  let emptyOK := match wordApplyColourExp (fun n => n + 10)
      (.op .add [] : WordExp (BitVec 8)) with
    | .op .add [] => true
    | _ => false
  nestedOK && duplicateOK && emptyOK

#guard expressionColourExact

/-- Original rows from word_alloc_colour_inst_probe.out: the executed allocator
must retain both 16-bit memory instructions, rename 8/32-bit registers, and
preserve four-register AddCarry operand order. -/
def instructionColourExact : Bool :=
  let f := fun n => n + 10
  let memoryOK (op : WordMemOp) (expectedR expectedA : Nat) :=
    match wordApplyColour f (.inst (.memOffset op 3 5 (BitVec.ofNat 8 7)) : WordProg (BitVec 8)) with
    | .inst (.memOffset actual r a w) =>
        actual == op && r == expectedR && a == expectedA && w == BitVec.ofNat 8 7
    | _ => false
  let carryOK := match wordApplyColour f
      (.inst (.arith (.cakeAddCarry 1 2 3 4)) : WordProg (BitVec 8)) with
    | .inst (.arith (.cakeAddCarry a b c d)) => a == 11 && b == 12 && c == 13 && d == 14
    | _ => false
  let fpOK := match WordAlloc.applyColourInst f
      (.fp (.fpMovFromReg 1 2 3) : WordLangInst (BitVec 8)) with
    | .fp (.fpMovFromReg a b c) => a == 1 && b == 12 && c == 13
    | _ => false
  memoryOK .load16 3 5 && memoryOK .store16 3 5 &&
    memoryOK .load8 13 15 && memoryOK .store32 13 15 && carryOK && fpOK

#guard instructionColourExact

/-- Nine original get_live_inst EVAL rows, including the 16-bit catchall,
output deletion order, four-register carry, and both FP word dimensions.
The shared production instruction cases are replayed below as well. -/
def instructionLivenessExact : Bool :=
  let live : NumSet := sptFromAList [(1, ()), (2, ()), (3, ()), (4, ()), (9, ())]
  let keys {width : Nat} [NeZero width] (inst : WordLangInst (BitVec width)) :=
    (sptToAList (WordAlloc.getLiveInst inst live)).map Prod.fst
  keys (.mem .load16 3 (.addr 5 7) : WordLangInst (BitVec 8)) == [3, 1, 9, 4, 2] &&
    keys (.mem .load8 3 (.addr 5 7) : WordLangInst (BitVec 8)) == [1, 9, 5, 4, 2] &&
    keys (.mem .store32 3 (.addr 5 7) : WordLangInst (BitVec 8)) == [3, 1, 9, 5, 4, 2] &&
    keys (.arith (.addCarry 1 2 3 4) : WordLangInst (BitVec 8)) == [3, 9, 4, 2] &&
    keys (.arith (.addOverflow 1 2 3 4) : WordLangInst (BitVec 8)) == [3, 9, 2] &&
    keys (.fp (.fpMovToReg 1 2 3) : WordLangInst (BitVec 64)) == [3, 9, 4, 2] &&
    keys (.fp (.fpMovToReg 1 2 3) : WordLangInst (BitVec 32)) == [3, 9, 4] &&
    keys (.fp (.fpMovFromReg 1 6 7) : WordLangInst (BitVec 64)) == [3, 1, 9, 4, 2, 6] &&
    keys (.fp (.fpMovFromReg 1 6 7) : WordLangInst (BitVec 32)) == [7, 3, 1, 9, 4, 2, 6]

example : instructionLivenessExact = true := by
  simp [instructionLivenessExact, WordAlloc.getLiveInst, WordAlloc.getLiveInstCore,
    sptToAList, sptFoldi, lrNext, sptFromAList, sptInsert, sptDelete, sptMkBS, sptMkBN]

/-- First four captured HOL liveness rows through the actual allocator list
route, including its memory-offset codec and canonical traversal order. -/
def instructionLivenessExecuted : Bool :=
  let live := [1, 2, 3, 4, 9]
  wordInstLiveBefore (.memOffset .load16 3 5 (BitVec.ofNat 8 7)) live == [3, 1, 9, 4, 2] &&
    wordInstLiveBefore (.memOffset .load8 3 5 (BitVec.ofNat 8 7)) live == [1, 9, 5, 4, 2] &&
    wordInstLiveBefore (.memOffset .store32 3 5 (BitVec.ofNat 8 7)) live == [3, 1, 9, 5, 4, 2] &&
    wordInstLiveBefore (α := BitVec 8) (.arith (.cakeAddCarry 1 2 3 4)) live == [3, 9, 4, 2]

example : instructionLivenessExecuted = true := by
  simp only [instructionLivenessExecuted, wordInstLiveBefore,
    WordAlloc.getLiveInstExecutable_cakeAddCarry]
  simp [WordAlloc.getLiveInstExecutable, WordAlloc.getLiveInstCore, WordAlloc.numSetToExact,
    WordAlloc.numSetFromExact, sptToAList, sptFoldi, lrNext, sptFromAList,
    sptInsert, sptDelete, sptMkBS, sptMkBN]

/-- Original apply_nummaps_key rows, covering independent payload types and
executed paired cutsets with collisions, duplicates and an empty component. -/
def pairedKeyMapExact : Bool :=
  let mixed := WordAlloc.applyNummapsKey (fun n => n + 10)
    (sptFromAList [(1, true), (2, false)], sptFromAList [(3, 7), (4, 8)])
  (sptToAList mixed.1 == [(11, true), (12, false)]) &&
    (sptToAList mixed.2 == [(13, 7), (14, 8)]) &&
    (wordApplyColourNumSets (fun n => n % 2) ([3, 1, 2], [4, 2]) == ([1, 0], [0])) &&
    (wordApplyColourNumSets (fun n => n + 10) ([], [3, 3, 2]) == ([], [13, 12]))

example : pairedKeyMapExact = true := by
  simp [pairedKeyMapExact, wordApplyColourNumSets, WordAlloc.applyNummapsKeyExecutable,
    WordAlloc.applyNummapsKey, WordAlloc.applyNummapKey, WordAlloc.numSetToExact,
    WordAlloc.numSetFromExact, sptToAList, sptFoldi, lrNext, sptFromAList, sptInsert]

/-- Twelve original HOL removal observations, including the literal catchall
and the word-dimension-sensitive integer FP move. -/
def instructionRemovalExact : Bool :=
  let remove {width : Nat} [NeZero width] (inst : WordLangInst (BitVec width))
      (live : List Nat) := WordAlloc.removeDeadInst inst (WordAlloc.numSetToExact live)
  [remove (.skip : WordLangInst (BitVec 8)) [],
    remove (.const 1 7 : WordLangInst (BitVec 8)) [],
    remove (.const 1 7 : WordLangInst (BitVec 8)) [1],
    remove (.mem .load16 1 (.addr 2 7) : WordLangInst (BitVec 8)) [],
    remove (.mem .store16 1 (.addr 2 7) : WordLangInst (BitVec 8)) [],
    remove (.mem .store32 1 (.addr 2 7) : WordLangInst (BitVec 8)) [],
    remove (.mem .load8 1 (.addr 2 7) : WordLangInst (BitVec 8)) [],
    remove (.arith (.addCarry 1 2 3 4) : WordLangInst (BitVec 8)) [4],
    remove (.arith (.addCarry 1 2 3 4) : WordLangInst (BitVec 8)) [],
    remove (.arith (.longMul 1 2 3 4) : WordLangInst (BitVec 8)) [2],
    remove (.fp (.fpMovToReg 1 2 3) : WordLangInst (BitVec 32)) [2],
    remove (.fp (.fpMovToReg 1 2 3) : WordLangInst (BitVec 64)) [2]] ==
    [true, true, false, false, false, false, true, false, true, false, false, true]

example : instructionRemovalExact = true := by
  simp [instructionRemovalExact, WordAlloc.removeDeadInst, WordAlloc.removeDeadInstCore,
    WordAlloc.numSetToExact, sptFromAList, sptInsert, sptLookup]

/-- Actual dead-code retention/drop boundaries guarded by the original rows.
Offset stores and the 16-bit catchall must be retained even with no live output. -/
def instructionRemovalExecuted : Bool :=
  let kept (i : WordInst (BitVec 8)) := match (RiscV.wordDeadInst [] i).1 with
    | .inst _ => true
    | _ => false
  kept (.memOffset .load16 1 2 7) && kept (.memOffset .store16 1 2 7) &&
    kept (.memOffset .store32 1 2 7) && !(kept (.memOffset .load8 1 2 7)) &&
    !(kept (.const 1 7))

example : instructionRemovalExecuted = true := by
  simp [instructionRemovalExecuted, RiscV.wordDeadInst, WordAlloc.removeDeadInstExecutable,
    WordAlloc.removeDeadInstCore, WordAlloc.numSetToExact, sptFromAList]

def parityGuard : Bool :=
  totalColourExact && assignExact && applyColourAliasedAssignExact &&
    returnRaiseExact &&
    callHandlerExact && loopLiveExact && expressionColourExact && instructionColourExact && instructionLivenessExact && instructionLivenessExecuted && pairedKeyMapExact && instructionRemovalExact && instructionRemovalExecuted

#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS Cake apply_colour/total_colour HOL parity"
  else
    IO.println "FAIL Cake apply_colour/total_colour HOL parity"
  pure parityGuard

end Flapjack.Test.CakeApplyColourParity
