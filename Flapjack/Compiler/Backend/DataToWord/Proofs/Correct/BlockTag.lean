import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.BlockTagOutOfRange
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.BlockLength

/-! In-range constructor-tag tests in the 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A related constructor's in-range tag test is simulated by the generated
immediate or heap-header comparison. -/
theorem assignBlockTagInRange64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src stamp found tag : Nat) (values : List DataSem.Value)
    (tagBound : tag < 2 ^ 64 / 16)
    (sourceRun : DataSem.getVar src source.locals = some (.block stamp found values)) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.tagEq tag)) [src] none) source target locs := by
  let op := ClosLang.Op.blockOp (.tagEq tag)
  let middle := DataSem.doStack op [.block stamp found values] (DataSem.doLimSafe source op [.block stamp found values])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [.block stamp found values]
  let result := decide (found = tag)
  by_cases empty : values = []
  · subst values
    obtain ⟨w, targetRun, foundBound, tagTest⟩ :=
      stateRel64_getBlockTagEmpty conf l1 l2 source target locs related src stamp found tag [] sourceRun
    have cmp : Compiler.Encoders.Asm.wordCmpHOL .equal w (BitVec.ofNat 64 (16 * tag + 2)) = result := by
      apply Bool.eq_iff_iff.mpr
      simp only [Compiler.Encoders.Asm.wordCmpHOL, beq_iff_eq, result, decide_eq_true_eq]
      simpa using tagTest tagBound
    let target1 := WordSemStateFiniteExact.setVar 1 (.word w) target
    have targetRel : stateRel64 conf l1 l2 middle target1 none locs :=
      stateRel64_setScratch1 conf l1 l2 middle target locs middleRel (.word w)
    refine ⟨DataSem.setVar dest (DataSem.boolValue result) middle,
      WordSemStateFiniteExact.setVar (adjustVar dest) (.word (if result then 18 else 2)) target1, ?_, ?_, ?_⟩
    · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
        DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
        DataSem.applyNonFfi, DataSem.installSfs, op, middle, result]
    · obtain ⟨w', run', test⟩ := stateRel64_getBlockEmpty conf l1 l2 source target locs related src stamp found [] sourceRun
      have same : w' = w := by rw [targetRun] at run'; exact WordLocW.word.inj (Option.some.inj run').symm
      subst w'
      simp only [List.length_nil, decide_true] at test
      have first : WordSemStateFiniteExact.evaluate (.assign 1 (.var (adjustVar src))) target = (none, target1) := by
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, targetRun, target1]
      have read1 : WordSemStateFiniteExact.getVar (adjustVar src) target1 = some (.word w) := by
        simpa [target1, getVar_setScratch1] using targetRun
      have second : WordSemStateFiniteExact.evaluate
          (.ite .test (adjustVar src) (.imm 1) .skip
            (.assign 1 (.op .and [.load (realAddr conf (adjustVar src)), .const (tagMask conf ||| 2)]))) target1 = (none, target1) := by
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp, read1]
        change Compiler.Encoders.Asm.wordCmpHOL .test w (BitVec.ofNat 64 1) = true at test
        simp only [test]
      have third : WordSemStateFiniteExact.evaluate
          (.ite .equal 1 (.imm (BitVec.ofNat 64 (16 * tag + 2)))
            (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))) target1 =
          (none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word (if result then 18 else 2)) target1) := by
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
          WordSemStateFiniteExact.wordExp, target1, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
        rw [cmp]
        cases result <;> rfl
      have fix1 : WordSemStateFiniteExact.fixClock target ((none : Option (WordSemResult 64)), target1) = (none, target1) := by
        simp [WordSemStateFiniteExact.fixClock, target1, WordSemStateFiniteExact.setVar]
      have fix2 : WordSemStateFiniteExact.fixClock target1 ((none : Option (WordSemResult 64)), target1) = (none, target1) := by
        simp [WordSemStateFiniteExact.fixClock]
      have bound' : tag < 1152921504606846976 := by simpa using tagBound
      simp only [compileControl64, compileControl?, bound', ↓reduceIte, Option.getD_some]
      change WordSemStateFiniteExact.evaluate (.seq (.assign 1 (.var (adjustVar src)))
        (.seq (.ite .test (adjustVar src) (.imm 1) .skip
          (.assign 1 (.op .and [.load (realAddr conf (adjustVar src)), .const (tagMask conf ||| 2)])))
          (.ite .equal 1 (.imm (BitVec.ofNat 64 (16 * tag + 2)))
            (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))))) target = _
      simp only [WordSemStateFiniteExact.evaluate, first, fix1, second, fix2, third]
    · exact stateRel64_setBool conf l1 l2 middle target1 locs targetRel dest result
  · obtain ⟨w, header, targetRun, bit, headerRun, tagTest⟩ :=
      stateRel64_loadBlockTag conf l1 l2 source target locs related src stamp found tag values sourceRun empty tagBound
    let masked := header &&& (tagMask conf ||| 2)
    have cmp : Compiler.Encoders.Asm.wordCmpHOL .equal masked (BitVec.ofNat 64 (16 * tag + 2)) = result := by
      apply Bool.eq_iff_iff.mpr
      simp only [Compiler.Encoders.Asm.wordCmpHOL, beq_iff_eq, result, decide_eq_true_eq]
      exact tagTest
    have ptrTest : Compiler.Encoders.Asm.wordCmpHOL .test w 1 = false := by
      change (w &&& (1 : BitVec 64) == 0) = false
      bv_decide
    let target1 := WordSemStateFiniteExact.setVar 1 (.word w) target
    let target2 := WordSemStateFiniteExact.setVar 1 (.word masked) target1
    have targetRel : stateRel64 conf l1 l2 middle target2 none locs :=
      stateRel64_setScratch1 conf l1 l2 middle target1 locs
        (stateRel64_setScratch1 conf l1 l2 middle target locs middleRel (.word w)) (.word masked)
    have header1 : WordSemStateFiniteExact.wordExp target1 (.load (realAddr conf (adjustVar src))) = some (.word header) := by
      simpa [target1, wordExp_header_setScratch1] using headerRun
    refine ⟨DataSem.setVar dest (DataSem.boolValue result) middle,
      WordSemStateFiniteExact.setVar (adjustVar dest) (.word (if result then 18 else 2)) target2, ?_, ?_, ?_⟩
    · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
        DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
        DataSem.applyNonFfi, DataSem.installSfs, op, middle, result]
    · have first : WordSemStateFiniteExact.evaluate (.assign 1 (.var (adjustVar src))) target = (none, target1) := by
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, targetRun, target1]
      have read1 : WordSemStateFiniteExact.getVar (adjustVar src) target1 = some (.word w) := by
        simpa [target1, getVar_setScratch1] using targetRun
      have second : WordSemStateFiniteExact.evaluate
          (.ite .test (adjustVar src) (.imm 1) .skip
            (.assign 1 (.op .and [.load (realAddr conf (adjustVar src)), .const (tagMask conf ||| 2)]))) target1 = (none, target2) := by
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp, read1]
        change Compiler.Encoders.Asm.wordCmpHOL .test w (BitVec.ofNat 64 1) = false at ptrTest
        simp only [ptrTest]
        simp [WordSemStateFiniteExact.wordExp, header1, wordOpHOL, wordOp, theWords, target2, masked]
        congr 2
        change (header &&& ((tagMask conf ||| 2) &&& (18446744073709551615 : BitVec 64))) =
          (header &&& (tagMask conf ||| 2))
        bv_decide
      have third : WordSemStateFiniteExact.evaluate
          (.ite .equal 1 (.imm (BitVec.ofNat 64 (16 * tag + 2)))
            (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))) target2 =
          (none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word (if result then 18 else 2)) target2) := by
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
          WordSemStateFiniteExact.wordExp, target2, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
        rw [cmp]
        cases result <;> rfl
      have fix1 : WordSemStateFiniteExact.fixClock target ((none : Option (WordSemResult 64)), target1) = (none, target1) := by
        simp [WordSemStateFiniteExact.fixClock, target1, WordSemStateFiniteExact.setVar]
      have fix2 : WordSemStateFiniteExact.fixClock target1 ((none : Option (WordSemResult 64)), target2) = (none, target2) := by
        simp [WordSemStateFiniteExact.fixClock, target2, WordSemStateFiniteExact.setVar]
      have bound' : tag < 1152921504606846976 := by simpa using tagBound
      simp only [compileControl64, compileControl?, bound', ↓reduceIte, Option.getD_some]
      change WordSemStateFiniteExact.evaluate (.seq (.assign 1 (.var (adjustVar src)))
        (.seq (.ite .test (adjustVar src) (.imm 1) .skip
          (.assign 1 (.op .and [.load (realAddr conf (adjustVar src)), .const (tagMask conf ||| 2)])))
          (.ite .equal 1 (.imm (BitVec.ofNat 64 (16 * tag + 2)))
            (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))))) target = _
      simp only [WordSemStateFiniteExact.evaluate, first, fix1, second, fix2, third]
    · exact stateRel64_setBool conf l1 l2 middle target2 locs targetRel dest result

/-- Every constructor-tag test is simulated, including out-of-range tags. -/
theorem assignBlockTag64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src stamp found tag : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar src source.locals = some (.block stamp found values)) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.tagEq tag)) [src] none) source target locs := by
  by_cases bound : tag < 2 ^ 64 / 16
  · exact assignBlockTagInRange64 conf secn label l1 l2 source target locs related dest src stamp found tag values bound sourceRun
  · exact assignBlockTagOutOfRange64 conf secn label l1 l2 source target locs related dest src stamp found tag values bound sourceRun

/-- Source type safety supplies the constructor operand for a tag test. -/
theorem assignBlockTag64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src tag : Nat)
    (safe : (DataSem.evaluate (.assign dest (.blockOp (.tagEq tag)) [src] none) source).1 ≠
      some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.tagEq tag)) [src] none) source target locs := by
  cases sourceRun : DataSem.getVar src source.locals with
  | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun] at safe
  | some value =>
    cases value with
    | block stamp found values =>
      exact assignBlockTag64 conf secn label l1 l2 source target locs related dest src stamp found tag values sourceRun
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
