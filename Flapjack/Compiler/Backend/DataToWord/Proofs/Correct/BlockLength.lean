import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.BlockEmpty
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.BlockLength

/-! Constructor field-count operations in the 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- The compiled length operation follows the source block field count. -/
theorem assignBlockLength64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src stamp tag : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar src source.locals = some (.block stamp tag values)) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp .lengthBlock) [src] none) source target locs := by
  let op := ClosLang.Op.blockOp .lengthBlock
  let middle := DataSem.doStack op [.block stamp tag values] (DataSem.doLimSafe source op [.block stamp tag values])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [.block stamp tag values]
  by_cases empty : values = []
  · subst values
    obtain ⟨w, targetRun, test⟩ := stateRel64_getBlockEmpty conf l1 l2 source target locs related src stamp tag [] sourceRun
    refine ⟨DataSem.setVar dest (.number 0) middle,
      WordSemStateFiniteExact.setVar (adjustVar dest) (.word 0) target, ?_, ?_, ?_⟩
    · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
        DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
        DataSem.applyNonFfi, DataSem.installSfs, op, middle]
    · simp only [compileControl64, compileControl?, Option.getD_some]
      change WordSemStateFiniteExact.evaluate (.ite .test (adjustVar src) (.imm 1)
        (.assign (adjustVar dest) (.const 0)) _) target = _
      simp only [List.length_nil, decide_true] at test
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
        targetRun, WordSemStateFiniteExact.wordExp]
      change Compiler.Encoders.Asm.wordCmpHOL .test w (BitVec.ofNat 64 1) = true at test
      simp only [test]
    · simpa [smallnum_eq_inlined] using stateRel64_setSmallInt conf l1 l2 middle target locs middleRel dest 0 (by norm_num [smallInt])
  · obtain ⟨w, header, targetRun, bit, headerRun, decoded, bound⟩ :=
      stateRel64_loadBlockHeader conf l1 l2 source target locs related src stamp tag values sourceRun empty
    have configBound : conf.lenSize ≠ 0 ∧ conf.lenSize + 7 < 64 := by
      rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, memory⟩
      obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, rest⟩ := memory
      exact ⟨heapMem.2.2.2.1, heapMem.2.2.2.2.1⟩
    have cmp : Compiler.Encoders.Asm.wordCmpHOL .test w 1 = false := by
      change (w &&& (1 : BitVec 64) == 0) = false
      bv_decide
    have small : smallInt 64 (Int.ofNat values.length) := by
      norm_num [smallInt] at bound ⊢
      omega
    have lenBound : 64 - conf.lenSize < 64 := by omega
    have lenWord : WordSemStateFiniteExact.wordExp target
        (shiftN .lsl (shiftN .lsr (.load (realAddr conf (adjustVar src))) (64 - conf.lenSize)) 2) =
        some (.word (smallnum (Int.ofNat values.length))) := by
      have shiftNat : (BitVec.ofNat 64 (64 - conf.lenSize)).toNat = 64 - conf.lenSize := by
        simp only [BitVec.toNat_ofNat]
        apply Nat.mod_eq_of_lt
        norm_num
        omega
      have notBig : ¬ 64 ≤ 64 - conf.lenSize := by omega
      simp only [WordGcFunctions.decodeLength] at decoded
      simp [shiftN, WordSemStateFiniteExact.wordExp, headerRun, wordShiftHOL,
        shiftNat, notBig, decoded, smallnum_eq_inlined]
      have nonnegative : ¬ ((values.length : Int) < 0) := Int.not_lt.mpr (Int.natCast_nonneg _)
      simp [nonnegative, BitVec.ofNat_mul]
      bv_decide
    refine ⟨DataSem.setVar dest (.number values.length) middle,
      WordSemStateFiniteExact.setVar (adjustVar dest) (.word (smallnum (Int.ofNat values.length))) target, ?_, ?_, ?_⟩
    · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
        DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
        DataSem.applyNonFfi, DataSem.installSfs, op, middle]
    · simp only [compileControl64, compileControl?, Option.getD_some]
      change WordSemStateFiniteExact.evaluate (.ite .test (adjustVar src) (.imm 1)
        (.assign (adjustVar dest) (.const 0)) _) target = _
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
        targetRun, lenWord]
      change Compiler.Encoders.Asm.wordCmpHOL .test w (BitVec.ofNat 64 1) = false at cmp
      simp only [cmp]
    · exact stateRel64_setSmallInt conf l1 l2 middle target locs middleRel dest (Int.ofNat values.length) small

/-- Source type safety guarantees that the tested local contains a block. -/
theorem assignBlockLength64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src : Nat)
    (safe : (DataSem.evaluate (.assign dest (.blockOp .lengthBlock) [src] none) source).1 ≠
      some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp .lengthBlock) [src] none) source target locs := by
  cases sourceRun : DataSem.getVar src source.locals with
  | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun] at safe
  | some value =>
    cases value with
    | block stamp tag values => exact assignBlockLength64 conf secn label l1 l2 source target locs related dest src stamp tag values sourceRun
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
