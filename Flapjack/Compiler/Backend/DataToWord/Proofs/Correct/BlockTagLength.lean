import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.BlockLengthEq
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.BlockTagLength

/-! Constructor tag-and-length tests in the 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- An unencodable positive tag-and-length query cannot match a related
constructor; the compiler's constant-false fallback is correct. -/
theorem assignTagLenUnencodable64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src stamp found tag wanted : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar src source.locals = some (.block stamp found values))
    (positive : 0 < wanted)
    (notFast : ¬ (tag < 2 ^ conf.tagBits - 1 ∧ wanted < 2 ^ conf.lenBits - 1))
    (noHeader : (encodeHeader conf (4 * tag) wanted : Option (BitVec 64)) = none) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.tagLenEq tag wanted)) [src] none) source target locs := by
  let op := ClosLang.Op.blockOp (.tagLenEq tag wanted)
  let middle := DataSem.doStack op [.block stamp found values] (DataSem.doLimSafe source op [.block stamp found values])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [.block stamp found values]
  have mismatch : ¬ (found = tag ∧ values.length = wanted) := by
    by_cases empty : values = []
    · have notZero : 0 ≠ wanted := by omega
      simp [empty, notZero]
    · obtain ⟨word, header, run, bit, load, decoded, bound, encoded⟩ :=
        stateRel64_loadBlockHeader conf l1 l2 source target locs related src stamp found values sourceRun empty
      exact unencodableTagLength64 conf found values.length tag wanted header encoded noHeader
  refine ⟨DataSem.setVar dest (DataSem.boolValue false) middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) target, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, op, middle, mismatch]
  · have notZero : wanted ≠ 0 := by omega
    simp [compileControl64, compileControl?, notZero, notFast, noHeader, WordSemStateFiniteExact.evaluate,
      WordSemStateFiniteExact.wordExp]
  · exact stateRel64_setBool conf l1 l2 middle target locs middleRel dest false

/-- The header-reading branch simulates an encodable positive combined
tag-and-length query when the packed-pointer fast path does not apply. -/
theorem assignTagLenHeader64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src stamp found tag wanted : Nat) (values : List DataSem.Value) (queryHeader : BitVec 64)
    (sourceRun : DataSem.getVar src source.locals = some (.block stamp found values))
    (positive : 0 < wanted)
    (notFast : ¬ (tag < 2 ^ conf.tagBits - 1 ∧ wanted < 2 ^ conf.lenBits - 1))
    (query : encodeHeader conf (4 * tag) wanted = some queryHeader) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.tagLenEq tag wanted)) [src] none) source target locs := by
  let op := ClosLang.Op.blockOp (.tagLenEq tag wanted)
  let middle := DataSem.doStack op [.block stamp found values] (DataSem.doLimSafe source op [.block stamp found values])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [.block stamp found values]
  let result := decide (found = tag ∧ values.length = wanted)
  have queryBit := encodeHeader_lowBit64 conf (4 * tag) wanted queryHeader query
  obtain ⟨w, targetRun, test⟩ := stateRel64_getBlockEmpty conf l1 l2 source target locs related src stamp found values sourceRun
  let target1 := WordSemStateFiniteExact.setVar 1 (.word 0) target
  have targetRel : stateRel64 conf l1 l2 middle target1 none locs :=
    stateRel64_setScratch1 conf l1 l2 middle target locs middleRel (.word 0)
  have read1 : WordSemStateFiniteExact.getVar (adjustVar src) target1 = some (.word w) := by
    simpa [target1, getVar_setScratch1] using targetRun
  have second : ∃ (t : WordSemStateFiniteExact 64 C F) (scratch : BitVec 64),
      stateRel64 conf l1 l2 middle t none locs ∧
      WordSemStateFiniteExact.evaluate (.ite .test (adjustVar src) (.imm 1) .skip
        (.assign 1 (.load (realAddr conf (adjustVar src))))) target1 = (none, t) ∧
      WordSemStateFiniteExact.getVar 1 t = some (.word scratch) ∧
      WordSemStateFiniteExact.fixClock target1 ((none : Option (WordSemResult 64)), t) = (none, t) ∧
      (scratch = queryHeader ↔ found = tag ∧ values.length = wanted) := by
    by_cases empty : values = []
    · subst values
      refine ⟨target1, 0, targetRel, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_nil, decide_true] at test
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp, read1]
        change Compiler.Encoders.Asm.wordCmpHOL .test w (BitVec.ofNat 64 1) = true at test
        simp only [test]
      · simp [target1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
      · simp [WordSemStateFiniteExact.fixClock]
      · have notZero : 0 ≠ wanted := by omega
        have headerNonzero : BitVec.ofNat 64 0 ≠ queryHeader := by
          intro eq
          have bit := congrArg (fun x : BitVec 64 => x.getLsbD 0) eq
          have queryBit' : queryHeader[0] = true := by simpa using queryBit
          simp at bit
          rw [queryBit'] at bit
          contradiction
        simp only [List.length_nil, notZero, and_false, iff_false]
        exact headerNonzero
    · obtain ⟨w', header, targetRun', bit, headerRun, decoded, bound, encoded⟩ :=
        stateRel64_loadBlockHeader conf l1 l2 source target locs related src stamp found values sourceRun empty
      have same : w' = w := by rw [targetRun] at targetRun'; exact WordLocW.word.inj (Option.some.inj targetRun').symm
      subst w'
      let target2 := WordSemStateFiniteExact.setVar 1 (.word header) target1
      have targetRel2 : stateRel64 conf l1 l2 middle target2 none locs :=
        stateRel64_setScratch1 conf l1 l2 middle target1 locs targetRel (.word header)
      have header1 : WordSemStateFiniteExact.wordExp target1 (.load (realAddr conf (adjustVar src))) = some (.word header) := by
        simpa [target1, wordExp_header_setScratch1] using headerRun
      have configBound : conf.lenSize + 2 < 64 := by
        rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, memory⟩
        obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, rest⟩ := memory
        have bound := heapMem.2.2.2.2.1
        omega
      have falseTest : Compiler.Encoders.Asm.wordCmpHOL .test w (BitVec.ofNat 64 1) = false := by
        change (w &&& (1 : BitVec 64) == 0) = false
        bv_decide
      refine ⟨target2, header, targetRel2, ?_, ?_, ?_, ?_⟩
      · simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp, read1]
        simp only [falseTest]
        simp [header1, target2]
      · simp [target2, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
      · simp [WordSemStateFiniteExact.fixClock, target2, WordSemStateFiniteExact.setVar]
      · exact encodedTagLength64 conf found values.length tag wanted header queryHeader configBound encoded query
  obtain ⟨target2, scratch, targetRel2, secondRun, scratchRun, secondFix, equality⟩ := second
  have cmp : Compiler.Encoders.Asm.wordCmpHOL .equal scratch queryHeader = result := by
    apply Bool.eq_iff_iff.mpr
    simpa [Compiler.Encoders.Asm.wordCmpHOL, result] using equality
  refine ⟨DataSem.setVar dest (DataSem.boolValue result) middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word (if result then 18 else 2)) target2, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, op, middle, result]
  · have first : WordSemStateFiniteExact.evaluate (.assign 1 (.const 0)) target = (none, target1) := by
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, target1]
    have firstFix : WordSemStateFiniteExact.fixClock target ((none : Option (WordSemResult 64)), target1) = (none, target1) := by
      simp [WordSemStateFiniteExact.fixClock, target1, WordSemStateFiniteExact.setVar]
    have third : WordSemStateFiniteExact.evaluate
        (.ite .equal 1 (.imm queryHeader) (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))) target2 =
        (none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word (if result then 18 else 2)) target2) := by
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
        WordSemStateFiniteExact.wordExp, scratchRun, cmp]
      cases result <;> rfl
    have notZero : wanted ≠ 0 := by omega
    simp only [compileControl64, compileControl?, notZero, ↓reduceIte, notFast, query, Option.getD_some]
    change WordSemStateFiniteExact.evaluate (.seq (.assign 1 (.const 0))
      (.seq (.ite .test (adjustVar src) (.imm 1) .skip (.assign 1 (.load (realAddr conf (adjustVar src)))))
        (.ite .equal 1 (.imm queryHeader) (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))))) target = _
    simp only [WordSemStateFiniteExact.evaluate, first, firstFix, secondRun, secondFix, third]
  · exact stateRel64_setBool conf l1 l2 middle target2 locs targetRel2 dest result

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
