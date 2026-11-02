import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.BoolNot
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Block

/-! Empty-constructor tests in the production-backed 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- Testing whether a constructor is empty is implemented by testing the
immediate/pointer bit and creating the corresponding Boolean. -/
theorem assignBlockEmpty64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src stamp tag : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar src source.locals = some (.block stamp tag values)) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.lenEq 0)) [src] none) source target locs := by
  let op := ClosLang.Op.blockOp (.lenEq 0)
  let middle := DataSem.doStack op [.block stamp tag values] (DataSem.doLimSafe source op [.block stamp tag values])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [.block stamp tag values]
  obtain ⟨w, targetRun, test⟩ := stateRel64_getBlockEmpty conf l1 l2 source target locs related src stamp tag values sourceRun
  let b := decide (values.length = 0)
  refine ⟨DataSem.setVar dest (DataSem.boolValue b) middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word (if b then 18 else 2)) target, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, op, middle, b]
  · simp only [compileControl64, compileControl?, Option.getD_some, if_true]
    change WordSemStateFiniteExact.evaluate (.ite .test (adjustVar src) (.imm 1)
      (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))) target = _
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
      targetRun, WordSemStateFiniteExact.wordExp, b]
    cases values <;> simp_all
  · exact stateRel64_setBool conf l1 l2 middle target locs middleRel dest b

/-- Source type safety guarantees that the tested local contains a block. -/
theorem assignBlockEmpty64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src : Nat)
    (safe : (DataSem.evaluate (.assign dest (.blockOp (.lenEq 0)) [src] none) source).1 ≠
      some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.lenEq 0)) [src] none) source target locs := by
  cases sourceRun : DataSem.getVar src source.locals with
  | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun] at safe
  | some value =>
    cases value with
    | block stamp tag values => exact assignBlockEmpty64 conf secn label l1 l2 source target locs related dest src stamp tag values sourceRun
    | number i =>
      simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
        DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux, DataSem.applyNonFfi] at safe
    | word64 w =>
      simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
        DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux, DataSem.applyNonFfi] at safe
    | codePtr loc =>
      simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
        DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux, DataSem.applyNonFfi] at safe
    | refPtr flag loc =>
      simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
        DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux, DataSem.applyNonFfi] at safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
