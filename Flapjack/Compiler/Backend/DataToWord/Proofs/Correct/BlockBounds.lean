import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.BlockLengthEq
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Bounds64

/-! Constructor bounds checks in the 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- The first generated instruction loads a related block's field count into
reserved register 1, including the immediate empty-block case. -/
theorem blockBounds_loadLength64 {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (src stamp tag : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar src source.locals = some (.block stamp tag values)) :
    WordSemStateFiniteExact.evaluate
      (.ite .test (adjustVar src) (.imm 1) (.assign 1 (.const 0))
        (.assign 1 (shiftN .lsr (.load (realAddr conf (adjustVar src))) (64 - conf.lenSize)))) target =
      (none, WordSemStateFiniteExact.setVar 1 (.word (BitVec.ofNat 64 values.length)) target) := by
  by_cases empty : values = []
  · subst values
    obtain ⟨w, targetRun, test⟩ := stateRel64_getBlockEmpty conf l1 l2 source target locs related src stamp tag [] sourceRun
    simp only [List.length_nil, decide_true] at test
    change Compiler.Encoders.Asm.wordCmpHOL .test w (BitVec.ofNat 64 1) = true at test
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
      targetRun, WordSemStateFiniteExact.wordExp, test]
  · obtain ⟨w, header, targetRun, bit, headerRun, decoded, bound⟩ :=
      stateRel64_loadBlockHeader conf l1 l2 source target locs related src stamp tag values sourceRun empty
    have configBound : conf.lenSize ≠ 0 ∧ conf.lenSize + 7 < 64 := by
      rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, memory⟩
      obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, rest⟩ := memory
      exact ⟨heapMem.2.2.2.1, heapMem.2.2.2.2.1⟩
    have cmp : Compiler.Encoders.Asm.wordCmpHOL .test w 1 = false := by
      change (w &&& (1 : BitVec 64) == 0) = false
      bv_decide
    have shiftNat : (BitVec.ofNat 64 (64 - conf.lenSize)).toNat = 64 - conf.lenSize := by
      simp only [BitVec.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      norm_num
      omega
    have notBig : ¬ 64 ≤ 64 - conf.lenSize := by omega
    have lenWord : WordSemStateFiniteExact.wordExp target
        (shiftN .lsr (.load (realAddr conf (adjustVar src))) (64 - conf.lenSize)) =
        some (.word (BitVec.ofNat 64 values.length)) := by
      simp only [WordGcFunctions.decodeLength] at decoded
      simpa [shiftN, WordSemStateFiniteExact.wordExp, headerRun, wordShiftHOL, shiftNat, notBig] using decoded
    change Compiler.Encoders.Asm.wordCmpHOL .test w (BitVec.ofNat 64 1) = false at cmp
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
      targetRun, cmp, lenWord]

/-- The production bounds-check lowering simulates an arbitrary related block
and integer index. -/
theorem assignBlockBounds64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest base index stamp tag : Nat) (values : List DataSem.Value) (i : Int)
    (blockRun : DataSem.getVar base source.locals = some (.block stamp tag values))
    (indexRun : DataSem.getVar index source.locals = some (.number i)) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp .boundsCheckBlock) [base, index] none) source target locs := by
  let op := ClosLang.Op.blockOp .boundsCheckBlock
  let middle := DataSem.doStack op [.block stamp tag values, .number i]
    (DataSem.doLimSafe source op [.block stamp tag values, .number i])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [.block stamp tag values, .number i]
  have lenBound := stateRel64_blockLengthBound conf l1 l2 source target locs related base stamp tag values blockRun
  have bound : values.length < 2305843009213693952 := by norm_num at lenBound; omega
  obtain ⟨w, targetRun, comparison⟩ := stateRel64_getNumberBounds conf l1 l2 source target locs related
    index i indexRun values.length bound
  let result := decide (0 ≤ i ∧ i < (values.length : Int))
  let target1 := WordSemStateFiniteExact.setVar 1 (.word (BitVec.ofNat 64 values.length)) target
  let target2 := WordSemStateFiniteExact.setVar 3 (.word (w.rotateRight 2)) target1
  have rel1 : stateRel64 conf l1 l2 middle target1 none locs :=
    stateRel64_setScratch1 conf l1 l2 middle target locs middleRel _
  have rel2 : stateRel64 conf l1 l2 middle target2 none locs := by
    apply stateRel64_setScratch conf l1 l2 middle target1 locs rel1 3 _ (by decide)
    intro n
    simp [adjustVar]
  have readIndex : WordSemStateFiniteExact.getVar (adjustVar index) target1 = some (.word w) := by
    simpa [target1, getVar_setScratch1] using targetRun
  have nNat : (BitVec.ofNat 64 values.length).toNat = values.length := by
    simp only [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    norm_num
    omega
  have cmp : Compiler.Encoders.Asm.wordCmpHOL .lower (w.rotateRight 2) (BitVec.ofNat 64 values.length) = result := by
    apply Bool.eq_iff_iff.mpr
    simpa [Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, nNat, result] using comparison
  refine ⟨DataSem.setVar dest (DataSem.boolValue result) middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word (if result then 18 else 2)) target2, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, blockRun, indexRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, op, middle, result]
  · have first := blockBounds_loadLength64 conf l1 l2 source target locs related base stamp tag values blockRun
    change WordSemStateFiniteExact.evaluate
      (.ite .test (adjustVar base) (.imm 1) (.assign 1 (.const 0))
        (.assign 1 (shiftN .lsr (.load (realAddr conf (adjustVar base))) (64 - conf.lenSize)))) target =
      (none, target1) at first
    have second : WordSemStateFiniteExact.evaluate (.assign 3 (shiftVar .ror (adjustVar index) 2)) target1 =
        (none, target2) := by
      simp [WordSemStateFiniteExact.evaluate, shiftVar, shiftN, WordSemStateFiniteExact.wordExp,
        readIndex, wordShiftHOL, target2]
    have read1 : WordSemStateFiniteExact.getVar 1 target2 = some (.word (BitVec.ofNat 64 values.length)) := by
      simp [target2, target1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
    have read3 : WordSemStateFiniteExact.getVar 3 target2 = some (.word (w.rotateRight 2)) := by
      simp [target2, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
    have third : WordSemStateFiniteExact.evaluate
        (.ite .lower 3 (.reg 1) (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))) target2 =
        (none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word (if result then 18 else 2)) target2) := by
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
        WordSemStateFiniteExact.wordExp, read1, read3, cmp]
      cases result <;> rfl
    have fix1 : WordSemStateFiniteExact.fixClock target ((none : Option (WordSemResult 64)), target1) = (none, target1) := by
      simp [WordSemStateFiniteExact.fixClock, target1, WordSemStateFiniteExact.setVar]
    have fix2 : WordSemStateFiniteExact.fixClock target1 ((none : Option (WordSemResult 64)), target2) = (none, target2) := by
      simp [WordSemStateFiniteExact.fixClock, target2, WordSemStateFiniteExact.setVar]
    simp only [compileControl64, compileControl?, Option.getD_some]
    change WordSemStateFiniteExact.evaluate (wordListSeq [
      .ite .test (adjustVar base) (.imm 1) (.assign 1 (.const 0))
        (.assign 1 (shiftN .lsr (.load (realAddr conf (adjustVar base))) (64 - conf.lenSize))),
      .assign 3 (shiftVar .ror (adjustVar index) 2),
      .ite .lower 3 (.reg 1) (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))]) target = _
    simp only [wordListSeq, WordSemStateFiniteExact.evaluate, first, fix1, second, fix2, third]
  · exact stateRel64_setBool conf l1 l2 middle target2 locs rel2 dest result

/-- A source-safe bounds check has a block and numeric index. -/
theorem assignBlockBounds64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest base index : Nat)
    (safe : (DataSem.evaluate (.assign dest (.blockOp .boundsCheckBlock) [base, index] none) source).1 ≠
      some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp .boundsCheckBlock) [base, index] none) source target locs := by
  cases blockRun : DataSem.getVar base source.locals with
  | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, blockRun] at safe
  | some block =>
    cases indexRun : DataSem.getVar index source.locals with
    | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, blockRun, indexRun] at safe
    | some idx =>
      cases block <;> cases idx <;>
        simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, blockRun, indexRun,
          DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
          DataSem.applyNonFfi] at safe
      case block.number stamp tag values i =>
        exact assignBlockBounds64 conf secn label l1 l2 source target locs related dest base index stamp tag values i blockRun indexRun

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
