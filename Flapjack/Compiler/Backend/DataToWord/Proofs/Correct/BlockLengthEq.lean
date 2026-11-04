import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.BlockLength
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.BlockPointer
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Scratch

/-! Packed-pointer constructor length tests in the 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- The compiler's packed-pointer branch simulates a positive,
nonsaturated constructor-length query. This is a case of the candidate
Lean state relation rather than the full HOL pass theorem. -/
theorem assignBlockLenFast64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src stamp tag wanted : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar src source.locals = some (.block stamp tag values))
    (positive : 0 < wanted) (queryBound : wanted < 2 ^ conf.lenBits - 1) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.lenEq wanted)) [src] none) source target locs := by
  let op := ClosLang.Op.blockOp (.lenEq wanted)
  let middle := DataSem.doStack op [.block stamp tag values] (DataSem.doLimSafe source op [.block stamp tag values])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [.block stamp tag values]
  obtain ⟨w, targetRun, comparison⟩ := stateRel64_getBlockFastLength conf l1 l2 source target locs related
    src stamp tag wanted values sourceRun positive queryBound
  let masked : BitVec 64 := w &&& BitVec.ofNat 64 (2 ^ (conf.lenBits + 1) - 1)
  let result := decide (values.length = wanted)
  have cmp : Compiler.Encoders.Asm.wordCmpHOL .equal masked (pointerBits conf 0 wanted ||| 1) = result := by
    apply Bool.eq_iff_iff.mpr
    simp only [Compiler.Encoders.Asm.wordCmpHOL, beq_iff_eq, result, decide_eq_true_eq]
    exact comparison
  let target1 := WordSemStateFiniteExact.setVar 1 (.word masked) target
  have targetRel : stateRel64 conf l1 l2 middle target1 none locs :=
    stateRel64_setScratch1 conf l1 l2 middle target locs middleRel (.word masked)
  refine ⟨DataSem.setVar dest (DataSem.boolValue result) middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word (if result then 18 else 2)) target1, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, op, middle, result]
  · have first : WordSemStateFiniteExact.evaluate
        (.assign 1 (.op .and [.var (adjustVar src), .const (BitVec.ofNat 64 (2 ^ (conf.lenBits + 1) - 1))])) target =
        (none, target1) := by
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, targetRun,
        wordOpHOL, wordOp, theWords, target1, masked]
      congr 2
      change (w &&& (BitVec.ofNat 64 (2 ^ (conf.lenBits + 1) - 1) &&& (18446744073709551615 : BitVec 64))) =
        (w &&& BitVec.ofNat 64 (2 ^ (conf.lenBits + 1) - 1))
      bv_decide
    have second : WordSemStateFiniteExact.evaluate
        (.ite .equal 1 (.imm (pointerBits conf 0 wanted ||| 1))
          (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))) target1 =
        (none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word (if result then 18 else 2)) target1) := by
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
        WordSemStateFiniteExact.wordExp, target1, WordSemStateFiniteExact.getVar,
        WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
      change Compiler.Encoders.Asm.wordCmpHOL .equal masked (pointerBits conf 0 wanted ||| BitVec.ofNat 64 1) = result at cmp
      rw [cmp]
      cases result <;> rfl
    have fix : WordSemStateFiniteExact.fixClock target ((none : Option (WordSemResult 64)), target1) = (none, target1) := by
      simp [WordSemStateFiniteExact.fixClock, target1, WordSemStateFiniteExact.setVar]
    have notZero : wanted ≠ 0 := by omega
    simp only [compileControl64, compileControl?, notZero, ↓reduceIte, queryBound, Option.getD_some]
    change WordSemStateFiniteExact.evaluate
      (.seq (.assign 1 (.op .and [.var (adjustVar src), .const (BitVec.ofNat 64 (2 ^ (conf.lenBits + 1) - 1))]))
        (.ite .equal 1 (.imm (pointerBits conf 0 wanted ||| 1))
          (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2)))) target = _
    simp only [WordSemStateFiniteExact.evaluate, first, fix, second]
  · exact stateRel64_setBool conf l1 l2 middle target1 locs targetRel dest result

/-- A related constructor's field count is bounded by the machine layout. -/
theorem stateRel64_blockLengthBound {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (src stamp tag : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar src source.locals = some (.block stamp tag values)) :
    values.length < 2 ^ (64 - 4) := by
  by_cases empty : values = []
  · simp [empty]
  · obtain ⟨word, header, run, bit, load, decoded, bound, encoded⟩ :=
      stateRel64_loadBlockHeader conf l1 l2 source target locs related src stamp tag values sourceRun empty
    exact bound

/-- A query larger than a 64-bit word cannot equal a related block length. -/
theorem assignBlockLenHuge64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src stamp tag wanted : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar src source.locals = some (.block stamp tag values))
    (huge : ¬ wanted < 2 ^ 64) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.lenEq wanted)) [src] none) source target locs := by
  let op := ClosLang.Op.blockOp (.lenEq wanted)
  let middle := DataSem.doStack op [.block stamp tag values] (DataSem.doLimSafe source op [.block stamp tag values])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [.block stamp tag values]
  have lengthBound := stateRel64_blockLengthBound conf l1 l2 source target locs related src stamp tag values sourceRun
  have unequal : values.length ≠ wanted := by norm_num at lengthBound huge; omega
  have shiftBound : shiftLength conf < 64 := related.2.2.2.2.2.2.2.1
  have bitsBound : conf.lenBits ≤ 61 := by simp [shiftLength] at shiftBound; omega
  have powerBound : 2 ^ conf.lenBits ≤ 2 ^ 61 := Nat.pow_le_pow_right (by decide) bitsBound
  have notFast : ¬ wanted < 2 ^ conf.lenBits - 1 := by norm_num at powerBound huge; omega
  have notZero : wanted ≠ 0 := by norm_num at huge; omega
  refine ⟨DataSem.setVar dest (DataSem.boolValue false) middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) target, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, op, middle, unequal]
  · have huge' : ¬ wanted < 18446744073709551616 := by simpa using huge
    simp [compileControl64, compileControl?, notZero, notFast, huge', WordSemStateFiniteExact.evaluate,
      WordSemStateFiniteExact.wordExp]
  · exact stateRel64_setBool conf l1 l2 middle target locs middleRel dest false

/-- The header-reading fallback simulates a positive constructor-length query
that fits in a machine word and is not represented by the fast field. -/
theorem assignBlockLenHeader64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src stamp tag wanted : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar src source.locals = some (.block stamp tag values))
    (positive : 0 < wanted) (notFast : ¬ wanted < 2 ^ conf.lenBits - 1) (queryBound : wanted < 2 ^ 64) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.lenEq wanted)) [src] none) source target locs := by
  let op := ClosLang.Op.blockOp (.lenEq wanted)
  let middle := DataSem.doStack op [.block stamp tag values] (DataSem.doLimSafe source op [.block stamp tag values])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [.block stamp tag values]
  have lengthBound := stateRel64_blockLengthBound conf l1 l2 source target locs related src stamp tag values sourceRun
  have lengthWordBound : values.length < 2 ^ 64 := by norm_num at lengthBound ⊢; omega
  obtain ⟨w, targetRun, test⟩ := stateRel64_getBlockEmpty conf l1 l2 source target locs related src stamp tag values sourceRun
  let target1 := WordSemStateFiniteExact.setVar 1 (.word 0) target
  have targetRel : stateRel64 conf l1 l2 middle target1 none locs :=
    stateRel64_setScratch1 conf l1 l2 middle target locs middleRel (.word 0)
  have read1 : WordSemStateFiniteExact.getVar (adjustVar src) target1 = some (.word w) := by
    simpa [target1, getVar_setScratch1] using targetRun
  have second : ∃ t : WordSemStateFiniteExact 64 C F,
      stateRel64 conf l1 l2 middle t none locs ∧
      WordSemStateFiniteExact.evaluate (.ite .test (adjustVar src) (.imm 1) .skip
        (.assign 1 (shiftN .lsr (.load (realAddr conf (adjustVar src))) (64 - conf.lenSize)))) target1 = (none, t) ∧
      WordSemStateFiniteExact.getVar 1 t = some (.word (BitVec.ofNat 64 values.length)) ∧
      WordSemStateFiniteExact.fixClock target1 ((none : Option (WordSemResult 64)), t) = (none, t) := by
    by_cases empty : values = []
    · subst values
      refine ⟨target1, targetRel, ?_, ?_, ?_⟩
      · simp only [List.length_nil, decide_true] at test
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp, read1]
        change Compiler.Encoders.Asm.wordCmpHOL .test w (BitVec.ofNat 64 1) = true at test
        simp only [test]
      · simp [target1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
      · simp [WordSemStateFiniteExact.fixClock]
    · obtain ⟨w', header, targetRun', bit, headerRun, decoded, bound, encoded⟩ :=
        stateRel64_loadBlockHeader conf l1 l2 source target locs related src stamp tag values sourceRun empty
      have same : w' = w := by rw [targetRun] at targetRun'; exact WordLocW.word.inj (Option.some.inj targetRun').symm
      subst w'
      let target2 := WordSemStateFiniteExact.setVar 1 (.word (BitVec.ofNat 64 values.length)) target1
      have targetRel2 : stateRel64 conf l1 l2 middle target2 none locs :=
        stateRel64_setScratch1 conf l1 l2 middle target1 locs targetRel (.word (BitVec.ofNat 64 values.length))
      have header1 : WordSemStateFiniteExact.wordExp target1 (.load (realAddr conf (adjustVar src))) = some (.word header) := by
        simpa [target1, wordExp_header_setScratch1] using headerRun
      have configBound : conf.lenSize ≠ 0 ∧ conf.lenSize + 7 < 64 := by
        rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, memory⟩
        obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, rest⟩ := memory
        exact ⟨heapMem.2.2.2.1, heapMem.2.2.2.2.1⟩
      have shiftNat : (BitVec.ofNat 64 (64 - conf.lenSize)).toNat = 64 - conf.lenSize := by
        simp only [BitVec.toNat_ofNat]
        apply Nat.mod_eq_of_lt
        norm_num
        omega
      have notBig : ¬ 64 ≤ 64 - conf.lenSize := by omega
      have shifted : WordSemStateFiniteExact.wordExp target1
          (shiftN .lsr (.load (realAddr conf (adjustVar src))) (64 - conf.lenSize)) =
          some (.word (BitVec.ofNat 64 values.length)) := by
        simp only [WordGcFunctions.decodeLength] at decoded
        simp [shiftN, WordSemStateFiniteExact.wordExp, header1, wordShiftHOL, shiftNat, notBig, decoded]
      have falseTest : Compiler.Encoders.Asm.wordCmpHOL .test w (BitVec.ofNat 64 1) = false := by
        change (w &&& (1 : BitVec 64) == 0) = false
        bv_decide
      refine ⟨target2, targetRel2, ?_, ?_, ?_⟩
      · simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp, read1]
        simp only [falseTest]
        simp [shifted, target2]
      · simp [target2, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
      · simp [WordSemStateFiniteExact.fixClock, target2, WordSemStateFiniteExact.setVar]
  obtain ⟨target2, targetRel2, secondRun, scratchRun, secondFix⟩ := second
  let result := decide (values.length = wanted)
  have wordEq : (BitVec.ofNat 64 values.length = BitVec.ofNat 64 wanted) ↔ values.length = wanted := by
    constructor
    · intro eq
      have numeric := congrArg BitVec.toNat eq
      have left' : values.length < 18446744073709551616 := by simpa using lengthWordBound
      have right' : wanted < 18446744073709551616 := by simpa using queryBound
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt left', Nat.mod_eq_of_lt right'] using numeric
    · rintro rfl
      rfl
  have cmp : Compiler.Encoders.Asm.wordCmpHOL .equal (BitVec.ofNat 64 values.length) (BitVec.ofNat 64 wanted) = result := by
    apply Bool.eq_iff_iff.mpr
    simpa [Compiler.Encoders.Asm.wordCmpHOL, result] using wordEq
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
        (.ite .equal 1 (.imm (BitVec.ofNat 64 wanted))
          (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))) target2 =
        (none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word (if result then 18 else 2)) target2) := by
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
        WordSemStateFiniteExact.wordExp, scratchRun]
      rw [cmp]
      cases result <;> rfl
    have notZero : wanted ≠ 0 := by omega
    have queryBound' : wanted < 18446744073709551616 := by simpa using queryBound
    simp only [compileControl64, compileControl?, notZero, ↓reduceIte, notFast, queryBound', Option.getD_some]
    change WordSemStateFiniteExact.evaluate (.seq (.assign 1 (.const 0))
      (.seq (.ite .test (adjustVar src) (.imm 1) .skip
        (.assign 1 (shiftN .lsr (.load (realAddr conf (adjustVar src))) (64 - conf.lenSize))))
        (.ite .equal 1 (.imm (BitVec.ofNat 64 wanted))
          (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))))) target = _
    simp only [WordSemStateFiniteExact.evaluate, first, firstFix, secondRun, secondFix, third]
  · exact stateRel64_setBool conf l1 l2 middle target2 locs targetRel2 dest result

/-- Every constructor-length test is simulated across all compiler branches. -/
theorem assignBlockLen64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src stamp tag wanted : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar src source.locals = some (.block stamp tag values)) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.lenEq wanted)) [src] none) source target locs := by
  by_cases zero : wanted = 0
  · subst wanted
    exact assignBlockEmpty64 conf secn label l1 l2 source target locs related dest src stamp tag values sourceRun
  · have positive : 0 < wanted := by omega
    by_cases fast : wanted < 2 ^ conf.lenBits - 1
    · exact assignBlockLenFast64 conf secn label l1 l2 source target locs related dest src stamp tag wanted values sourceRun positive fast
    · by_cases fits : wanted < 2 ^ 64
      · exact assignBlockLenHeader64 conf secn label l1 l2 source target locs related dest src stamp tag wanted values sourceRun positive fast fits
      · exact assignBlockLenHuge64 conf secn label l1 l2 source target locs related dest src stamp tag wanted values sourceRun fits

/-- Source type safety guarantees that the tested local contains a block. -/
theorem assignBlockLen64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src wanted : Nat)
    (safe : (DataSem.evaluate (.assign dest (.blockOp (.lenEq wanted)) [src] none) source).1 ≠
      some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.lenEq wanted)) [src] none) source target locs := by
  cases sourceRun : DataSem.getVar src source.locals with
  | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun] at safe
  | some value =>
    cases value with
    | block stamp tag values => exact assignBlockLen64 conf secn label l1 l2 source target locs related dest src stamp tag wanted values sourceRun
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
