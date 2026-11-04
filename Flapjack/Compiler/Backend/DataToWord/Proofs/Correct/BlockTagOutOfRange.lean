import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.BlockTagEmpty

/-! Out-of-range constructor-tag tests in the 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A constructor-tag test outside the representable tag range returns
false in both semantics. -/
theorem assignBlockTagOutOfRange64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src stamp found tag : Nat) (values : List DataSem.Value)
    (outOfRange : ¬ tag < 2 ^ 64 / 16)
    (sourceRun : DataSem.getVar src source.locals = some (.block stamp found values)) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.tagEq tag)) [src] none) source target locs := by
  let op := ClosLang.Op.blockOp (.tagEq tag)
  let middle := DataSem.doStack op [.block stamp found values] (DataSem.doLimSafe source op [.block stamp found values])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [.block stamp found values]
  obtain ⟨w, targetRun, foundBound, tagTest⟩ :=
    stateRel64_getBlockTagEmpty conf l1 l2 source target locs related src stamp found tag values sourceRun
  have unequal : found ≠ tag := by omega
  have bound' : ¬ tag < 1152921504606846976 := by simpa using outOfRange
  refine ⟨DataSem.setVar dest (DataSem.boolValue false) middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) target, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, op, middle, unequal]
  · simp [compileControl64, compileControl?, bound', WordSemStateFiniteExact.evaluate,
      WordSemStateFiniteExact.wordExp]
  · exact stateRel64_setBool conf l1 l2 middle target locs middleRel dest false

/-- Source type safety supplies the constructor operand for an out-of-range
tag test. -/
theorem assignBlockTagOutOfRange64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src tag : Nat) (outOfRange : ¬ tag < 2 ^ 64 / 16)
    (safe : (DataSem.evaluate (.assign dest (.blockOp (.tagEq tag)) [src] none) source).1 ≠
      some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.tagEq tag)) [src] none) source target locs := by
  cases sourceRun : DataSem.getVar src source.locals with
  | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun] at safe
  | some value =>
    cases value with
    | block stamp found values =>
      exact assignBlockTagOutOfRange64 conf secn label l1 l2 source target locs related dest src stamp found tag values outOfRange sourceRun
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
