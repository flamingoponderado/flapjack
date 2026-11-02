import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.BoolNot

/-! Boolean equality tests in the production-backed 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- Successful Boolean comparison uses the two immediate encodings and
installs a represented Boolean result. -/
theorem assignBoolTest64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest left right : Nat) (test : AstHOL.Test) (x y : DataSem.Value) (a b : Bool)
    (leftRun : DataSem.getVar left source.locals = some x) (rightRun : DataSem.getVar right source.locals = some y)
    (leftBool : DataSem.destBool x = some a) (rightBool : DataSem.destBool y = some b) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.boolTest test)) [left, right] none) source target locs := by
  let op := ClosLang.Op.blockOp (.boolTest test)
  let middle := DataSem.doStack op [x, y] (DataSem.doLimSafe source op [x, y])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [x, y]
  have leftWord := stateRel64_getBool conf l1 l2 source target locs related left x a leftRun (destBool_isBool x a leftBool)
  have rightWord := stateRel64_getBool conf l1 l2 source target locs related right y b rightRun (destBool_isBool y b rightBool)
  refine ⟨DataSem.setVar dest (DataSem.boolValue (a == b)) middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word (if a == b then 18 else 2)) target, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, leftRun, rightRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, leftBool, rightBool, DataSem.installSfs, op, middle]
  · simp only [compileControl64, compileControl?, Option.getD_some]
    change WordSemStateFiniteExact.evaluate (.ite .equal (adjustVar left) (.reg (adjustVar right))
      (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))) target = _
    cases a <;> cases b <;> simp [WordSemStateFiniteExact.evaluate,
      WordSemStateFiniteExact.getVarImm, WordSemStateFiniteExact.wordExp, wordSemWordCmp,
      Compiler.Encoders.Asm.wordCmpHOL, leftWord, rightWord]
  · exact stateRel64_setBool conf l1 l2 middle target locs middleRel dest (a == b)

/-- Source type safety supplies both local lookups and both Boolean decodings. -/
theorem assignBoolTest64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest left right : Nat) (test : AstHOL.Test)
    (safe : (DataSem.evaluate (.assign dest (.blockOp (.boolTest test)) [left, right] none) source).1 ≠
      some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.boolTest test)) [left, right] none) source target locs := by
  cases leftRun : DataSem.getVar left source.locals with
  | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, leftRun] at safe
  | some x =>
    cases rightRun : DataSem.getVar right source.locals with
    | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, leftRun, rightRun] at safe
    | some y =>
      cases leftBool : DataSem.destBool x with
      | none =>
        simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, leftRun, rightRun,
          DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
          DataSem.applyNonFfi, leftBool] at safe
      | some a =>
        cases rightBool : DataSem.destBool y with
        | none =>
          simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, leftRun, rightRun,
            DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
            DataSem.applyNonFfi, leftBool, rightBool] at safe
        | some b =>
          exact assignBoolTest64 conf secn label l1 l2 source target locs related dest left right test x y a b
            leftRun rightRun leftBool rightBool

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
