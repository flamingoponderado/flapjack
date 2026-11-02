import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.BlockEmpty

/-! Nullary constructor-tag tests in the 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A nullary constructor-tag test agrees with its generated immediate test,
including out-of-range tags for which the compiler emits false directly. -/
theorem assignBlockTagEmpty64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src stamp found tag : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar src source.locals = some (.block stamp found values)) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.tagLenEq tag 0)) [src] none) source target locs := by
  let op := ClosLang.Op.blockOp (.tagLenEq tag 0)
  let middle := DataSem.doStack op [.block stamp found values] (DataSem.doLimSafe source op [.block stamp found values])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [.block stamp found values]
  obtain ⟨w, targetRun, foundBound, tagTest⟩ :=
    stateRel64_getBlockTagEmpty conf l1 l2 source target locs related src stamp found tag values sourceRun
  let b := decide (found = tag ∧ values.length = 0)
  refine ⟨DataSem.setVar dest (DataSem.boolValue b) middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word (if b then 18 else 2)) target, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, op, middle, b]
  · by_cases bound : tag < 2 ^ 64 / 16
    · have comparison : Compiler.Encoders.Asm.wordCmpHOL .equal w (BitVec.ofNat 64 (16 * tag + 2)) = b := by
        apply Bool.eq_iff_iff.mpr
        simp only [Compiler.Encoders.Asm.wordCmpHOL, beq_iff_eq, b, decide_eq_true_eq]
        simpa using tagTest bound
      simp only [compileControl64, compileControl?, Option.getD_some, bound, ↓reduceIte]
      change WordSemStateFiniteExact.evaluate (.ite .equal (adjustVar src) (.imm (BitVec.ofNat 64 (16 * tag + 2)))
        (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))) target = _
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
        targetRun, comparison, WordSemStateFiniteExact.wordExp]
      cases b <;> rfl
    · have ne : found ≠ tag := by omega
      have falseB : b = false := by simp [b, ne]
      have bound' : ¬ tag < 1152921504606846976 := by simpa using bound
      simp [compileControl64, compileControl?, bound', WordSemStateFiniteExact.evaluate,
        WordSemStateFiniteExact.wordExp, falseB]
  · exact stateRel64_setBool conf l1 l2 middle target locs middleRel dest b

/-- Source safety guarantees a constructor operand. -/
theorem assignBlockTagEmpty64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src tag : Nat)
    (safe : (DataSem.evaluate (.assign dest (.blockOp (.tagLenEq tag 0)) [src] none) source).1 ≠
      some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.tagLenEq tag 0)) [src] none) source target locs := by
  cases sourceRun : DataSem.getVar src source.locals with
  | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun] at safe
  | some value =>
    cases value with
    | block stamp found values => exact assignBlockTagEmpty64 conf secn label l1 l2 source target locs related dest src stamp found tag values sourceRun
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
