import Flapjack.Pancake.Proofs.PanToCrep.EvaluateNestedDecs

/-!
Direct oracle and exact-theorem checks for
`pan_to_crepProofScript.sml:596-620`. The successful declaration cases,
restoration of existing and absent locals, length-mismatch behavior, and
rejected premise rows come from
`scripts/hol-probes/eval_nested_decs_seq_res_var_eq_probe.out`.
-/

namespace Flapjack.Test.CrepNestedDecsSeqResVarEqParity

open Flapjack

private abbrev W := BitVec 64
private abbrev E := CrepExpHOL 64
private abbrev P := CrepProgHOL 64
private abbrev V := HolWordLab 64

private def emptyCode : HolFiniteMapExact MlString (List Nat × P) :=
  HolFiniteMapExact.empty

private def stateAbsent : CrepSemHOLState 64 Unit where
  locals := HolFiniteMapExact.updateListEq HolFiniteMapExact.empty
    [(0, .word (BitVec.ofNat 64 7)), (2, .word 0)]
  globals := HolFiniteMapExact.empty
  code := emptyCode
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 5
  be := false
  ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 100

private def statePresent : CrepSemHOLState 64 Unit where
  locals := HolFiniteMapExact.updateListEq HolFiniteMapExact.empty
    [(0, .word (BitVec.ofNat 64 7)), (1, .word (BitVec.ofNat 64 8)), (2, .word 0)]
  globals := HolFiniteMapExact.empty
  code := emptyCode
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 5
  be := false
  ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 100

private def expressions : List E :=
  [.const (BitVec.ofNat 64 10), .const (BitVec.ofNat 64 20)]
private def names : List Nat := [0, 1]
private def values : List V := [.word (BitVec.ofNat 64 10), .word (BitVec.ofNat 64 20)]
private def body : P := .assign 2 (.var 1)

private def memDecAbsent (address : W) : Decidable (stateAbsent.memaddrs address) :=
  isFalse (by simp [stateAbsent])

private def shMemDecAbsent (address : W) : Decidable (stateAbsent.shMemaddrs address) :=
  isFalse (by simp [stateAbsent])

private def memDecPresent (address : W) : Decidable (statePresent.memaddrs address) :=
  isFalse (by simp [statePresent])

private def shMemDecPresent (address : W) : Decidable (statePresent.shMemaddrs address) :=
  isFalse (by simp [statePresent])

theorem exactEquationRestoresAbsentLocal :
    evalCrepSemHOLProgExact stateAbsent (nestedDecsHOL names expressions body) =
      let result := evalCrepSemHOLProgExact
        { stateAbsent with locals := stateAbsent.locals.updateListEq (names.zip values) } body
      (result.1, { result.2 with locals :=
        ((List.zip names (names.map stateAbsent.locals.lookup)).foldl
          (fun current entry => HolFiniteMapExact.resVarEq current entry) result.2.locals) }) := by
  apply evalNestedDecsSeqResVarEqCrepHOL stateAbsent expressions names values body
  · simp [evalCrepSemHOLExpDefault, evalCrepSemHOLExpWithMemDec, evalCrepSemHOLExp,
      expressions, values]
  · rfl
  · decide
  · decide

theorem exactEquationRestoresExistingLocal :
    evalCrepSemHOLProgExact statePresent (nestedDecsHOL names expressions body) =
      let result := evalCrepSemHOLProgExact
        { statePresent with locals := statePresent.locals.updateListEq (names.zip values) } body
      (result.1, { result.2 with locals :=
        ((List.zip names (names.map statePresent.locals.lookup)).foldl
          (fun current entry => HolFiniteMapExact.resVarEq current entry) result.2.locals) }) := by
  apply evalNestedDecsSeqResVarEqCrepHOL statePresent expressions names values body
  · simp [evalCrepSemHOLExpDefault, evalCrepSemHOLExpWithMemDec, evalCrepSemHOLExp,
      expressions, values]
  · rfl
  · decide
  · decide

private def restoreAbsentLocalOracleRow : Bool :=
  match evalCrepSemHOLProg stateAbsent memDecAbsent shMemDecAbsent
      (nestedDecsHOL names expressions body) with
  | (none, result) =>
      result.locals.lookup 0 == some (.word (BitVec.ofNat 64 7)) &&
      result.locals.lookup 1 == none &&
      result.locals.lookup 2 == some (.word (BitVec.ofNat 64 20)) && result.clock == 5
  | _ => false

private def restoreExistingLocalOracleRow : Bool :=
  match evalCrepSemHOLProg statePresent memDecPresent shMemDecPresent
      (nestedDecsHOL names expressions body) with
  | (none, result) =>
      result.locals.lookup 0 == some (.word (BitVec.ofNat 64 7)) &&
      result.locals.lookup 1 == some (.word (BitVec.ofNat 64 8)) &&
      result.locals.lookup 2 == some (.word (BitVec.ofNat 64 20)) && result.clock == 5
  | _ => false

private def lengthMismatchOracleRow : Bool :=
  match evalCrepSemHOLProg stateAbsent memDecAbsent shMemDecAbsent
      (nestedDecsHOL [0, 1] [.const (BitVec.ofNat 64 10)] body) with
  | (none, result) =>
      result.locals.lookup 0 == some (.word (BitVec.ofNat 64 7)) &&
      result.locals.lookup 1 == none &&
      result.locals.lookup 2 == some (.word 0) && result.clock == 5
  | _ => false

private def rejectedPremiseRows : Bool :=
  !decide (([0, 0] : List Nat).Nodup) &&
  distinctListsHol ([0] : List Nat)
    ([(CrepExpHOL.var 0 : CrepExpHOL 64)].flatMap crepExpVarsHOL) == false &&
  ¬(([0, 1] : List Nat).length =
    ([CrepExpHOL.const (BitVec.ofNat 64 10)] : List (CrepExpHOL 64)).length)

#guard restoreAbsentLocalOracleRow
#guard restoreExistingLocalOracleRow
#guard lengthMismatchOracleRow
#guard rejectedPremiseRows

def runChecks : IO Bool := do
  if restoreAbsentLocalOracleRow && restoreExistingLocalOracleRow &&
      lengthMismatchOracleRow && rejectedPremiseRows then
    IO.println "PASS nested Dec oracle rows and exact evaluator theorem cases"
  else
    IO.println "FAIL nested Dec oracle rows and exact evaluator theorem cases"
  pure (restoreAbsentLocalOracleRow && restoreExistingLocalOracleRow &&
    lengthMismatchOracleRow && rejectedPremiseRows)

end Flapjack.Test.CrepNestedDecsSeqResVarEqParity
