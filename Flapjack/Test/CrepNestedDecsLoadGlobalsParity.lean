import Flapjack.Pancake.Proofs.PanToCrep.EvaluateNestedDecs

/-!
Direct HOL observations and exact evaluator regressions for
`pan_to_crepProofScript.sml:4139-4176`, captured in
`scripts/hol-probes/eval_nested_decs_load_globals_probe.out`.
-/

namespace Flapjack.Test.CrepNestedDecsLoadGlobalsParity

open Flapjack

private abbrev W := BitVec 64
private abbrev E := CrepExpHOL 64
private abbrev P := CrepProgHOL 64
private abbrev V := HolWordLab 64
private abbrev RV := ValueHOL 64

private def word64 (value : Nat) : W := BitVec.ofNat 64 value

private def wordState : CrepSemHOLState 64 Unit where
  locals := HolFiniteMapExact.update HolFiniteMapExact.empty
    (0, .word (word64 9))
  globals := HolFiniteMapExact.update HolFiniteMapExact.empty
    (0, .word (word64 7))
  code := HolFiniteMapExact.empty
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 5
  be := false
  ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 100

private def structState : CrepSemHOLState 64 Unit where
  locals := HolFiniteMapExact.update HolFiniteMapExact.empty
    (5, .word (word64 99))
  globals := HolFiniteMapExact.update
    (HolFiniteMapExact.update HolFiniteMapExact.empty (0, .word (word64 3)))
    (1, .word (word64 4))
  code := HolFiniteMapExact.empty
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 7
  be := false
  ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 100

private def wordValue : RV := .val (.word (word64 7))
private def wordNames : List Nat := [0]
private def wordValues : List V := [.word (word64 7)]
private def wordBody : P := .return [.var 0]
private def wordProgram : P := nestedDecsHOL wordNames
  (loadGlobalsHOL (width := 64) 0 1) wordBody

private def wordMemDec (address : W) : Decidable (wordState.memaddrs address) :=
  isFalse (by simp [wordState])

private def wordShMemDec (address : W) : Decidable (wordState.shMemaddrs address) :=
  isFalse (by simp [wordState])

theorem exactWordEquation :
    evalCrepSemHOLProgExact wordState wordProgram =
      let result := evalCrepSemHOLProgExact
        { wordState with locals :=
          (wordState.locals.updateListEq (wordNames.zip wordValues)) } wordBody
      (result.1, { result.2 with locals :=
        ((List.zip wordNames (wordNames.map wordState.locals.lookup)).foldl
          (fun current entry => HolFiniteMapExact.resVarEq current entry)
          result.2.locals) }) := by
  have hLookup : globalsLookupHOL wordState wordValue = some wordValues := by
    simp [globalsLookupHOL, wordState, wordValue, wordValues, word64,
      shapeOfHOLExact,
      List.range, List.range.loop, HolFiniteMapExact.update,
      HolFiniteMapExact.empty, Flapjack.FUPDATE]
  have hEquation := evaluateNestedDecsLoadGlobalsCrepHOL wordState wordValue
    wordValues wordNames wordBody
    ⟨hLookup, (by simp [wordValue, word64, shapeOfHOLExact]), by decide,
      (by simp [wordNames, wordValue, word64, shapeOfHOLExact])⟩
  simpa [wordProgram, wordValue, wordValues, wordNames, word64,
    shapeOfHOLExact] using hEquation

private def structValue : RV := .rStruct
  [.val (.word (word64 3)), .val (.word (word64 4))]
private def structNames : List Nat := [5, 6]
private def structValues : List V := [.word (word64 3), .word (word64 4)]
private def structBody : P := .return [.var 5, .var 6]
private def structProgram : P := nestedDecsHOL structNames
  (loadGlobalsHOL (width := 64) 0 2) structBody

private def structMemDec (address : W) : Decidable (structState.memaddrs address) :=
  isFalse (by simp [structState])

private def structShMemDec (address : W) : Decidable (structState.shMemaddrs address) :=
  isFalse (by simp [structState])

theorem exactStructEquation :
    evalCrepSemHOLProgExact structState structProgram =
      let result := evalCrepSemHOLProgExact
        { structState with locals :=
          (structState.locals.updateListEq (structNames.zip structValues)) } structBody
      (result.1, { result.2 with locals :=
        ((List.zip structNames (structNames.map structState.locals.lookup)).foldl
          (fun current entry => HolFiniteMapExact.resVarEq current entry)
          result.2.locals) }) := by
  have hLookup : globalsLookupHOL structState structValue = some structValues := by
    simp [globalsLookupHOL, structState, structValue, structValues, word64,
      shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeHOL,
      List.range, List.range.loop, HolFiniteMapExact.update,
      HolFiniteMapExact.empty, Flapjack.FUPDATE]
  have hEquation := evaluateNestedDecsLoadGlobalsCrepHOL structState structValue
    structValues structNames structBody
    ⟨hLookup, (by simp [structValue, word64, shapeOfHOLExact]), by decide,
      (by simp [structNames, structValue, word64, shapeOfHOLExact])⟩
  simpa [structProgram, structValue, structValues, structNames, word64,
    shapeOfHOLExact] using hEquation

private def wordOracleRow : Bool :=
  match evalCrepSemHOLProg wordState wordMemDec wordShMemDec wordProgram with
  | (some (.return [.word result]), output) =>
      result == word64 7 &&
      output.locals.lookup 0 == some (.word (word64 9)) && output.clock == 5
  | _ => false

private def structOracleRow : Bool :=
  match evalCrepSemHOLProg structState structMemDec structShMemDec structProgram with
  | (some (.return [.word first, .word second]), output) =>
      first == word64 3 && second == word64 4 &&
      output.locals.lookup 5 == some (.word (word64 99)) &&
      output.locals.lookup 6 == none && output.clock == 7
  | _ => false

#guard wordOracleRow
#guard structOracleRow

def runChecks : IO Bool := do
  if wordOracleRow && structOracleRow then
    IO.println "PASS nested load_globals word/struct oracle rows"
  else
    IO.println "FAIL nested load_globals word/struct oracle rows"
  pure (wordOracleRow && structOracleRow)

end Flapjack.Test.CrepNestedDecsLoadGlobalsParity
