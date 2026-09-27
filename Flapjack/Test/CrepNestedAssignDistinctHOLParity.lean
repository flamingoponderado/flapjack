import Flapjack.Pancake.Proofs.PanToCrep.EvaluateNestedAssign

/-!
Direct oracle and exact-theorem checks for
`pan_to_crepProofScript.sml:540-575`. The successful two-Assign row and the
duplicate-name / expression-interference premise boundaries come from
`scripts/hol-probes/eval_nested_assign_distinct_eq_probe.out`.
-/

namespace Flapjack.Test.CrepNestedAssignDistinctHOLParity

open Flapjack

private abbrev W := BitVec 64
private abbrev E := CrepExpHOL 64
private abbrev P := CrepProgHOL 64
private abbrev V := HolWordLab 64

private def locals : HolFiniteMapExact Nat V :=
  (HolFiniteMapExact.update (HolFiniteMapExact.update HolFiniteMapExact.empty
    (0, .word (BitVec.ofNat 64 7))) (1, .word (BitVec.ofNat 64 8)))

private def emptyCode : HolFiniteMapExact MlString (List Nat × P) :=
  HolFiniteMapExact.empty

private def state : CrepSemHOLState 64 Unit where
  locals := locals
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

private def memDec (a : W) : Decidable (state.memaddrs a) := isFalse (by simp [state])
private def shMemDec (a : W) : Decidable (state.shMemaddrs a) := isFalse (by simp [state])

private def expressions : List E := [.const (BitVec.ofNat 64 10), .const (BitVec.ofNat 64 20)]
private def names : List Nat := [0, 1]
private def values : List V := [.word (BitVec.ofNat 64 10), .word (BitVec.ofNat 64 20)]
private def oldValues : List V := [.word (BitVec.ofNat 64 7), .word (BitVec.ofNat 64 8)]
private def program : P := crepNestedSeqHOL (names.zipWith
  (fun name expression => CrepProgHOL.assign name expression) expressions)

theorem exactTwoAssignEquation :
    evalCrepSemHOLProgDefault state program =
      (none, { state with locals := state.locals.updateListEq (names.zip values) }) := by
  apply evalNestedAssignDistinctEqCrepHOL state expressions names values oldValues
  · simp [evalCrepSemHOLExpDefault, evalCrepSemHOLExpWithMemDec,
      evalCrepSemHOLExp, CrepNestedAssignDistinctHOLParity.expressions,
      CrepNestedAssignDistinctHOLParity.values]
  · decide
  · decide
  · decide
  · rfl

private def successOracleRow : Bool :=
  match evalCrepSemHOLProg state memDec shMemDec program with
  | (none, result) =>
      result.locals.lookup 0 == some (.word (BitVec.ofNat 64 10)) &&
      result.locals.lookup 1 == some (.word (BitVec.ofNat 64 20)) && result.clock == 5
  | _ => false

private def premiseRejectionRows : Bool :=
  !decide (([0, 0] : List Nat).Nodup) &&
  distinctListsHol ([0] : List Nat)
    ([(CrepExpHOL.var 0 : CrepExpHOL 64)].flatMap crepExpVarsHOL) == false

#guard successOracleRow
#guard premiseRejectionRows

def runChecks : IO Bool := do
  if successOracleRow then
    IO.println "PASS exact nested Assign evaluator matches direct HOL success row"
  else
    IO.println "FAIL exact nested Assign evaluator matches direct HOL success row"
  if premiseRejectionRows then
    IO.println "PASS exact theorem premises reject duplicate names and expression interference"
  else
    IO.println "FAIL exact theorem premises reject duplicate names and expression interference"
  pure (successOracleRow && premiseRejectionRows)

end Flapjack.Test.CrepNestedAssignDistinctHOLParity
