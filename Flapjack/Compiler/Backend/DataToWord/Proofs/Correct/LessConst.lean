import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.BoolNot
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Number

/-! Bounded integer comparisons in the 64-bit data-to-word simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- The source assembler's signed comparison agrees with signed BitVec order. -/
theorem signedLess64 (left right : BitVec 64) :
    Compiler.Encoders.Asm.holAsmSignedLess left right = left.slt right := by
  have bl := left.isLt
  have br := right.isLt
  simp only [Compiler.Encoders.Asm.holAsmSignedLess, BitVec.slt_eq_decide, BitVec.toInt_eq_msb_cond,
    BitVec.msb_eq_decide]
  repeat (any_goals first | split)
  all_goals simp_all only [decide_eq_true_eq]
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp_all [decide_eq_true_eq]
  all_goals omega

/-- The compiler's bounded immediate comparison agrees with integer order. -/
theorem lessConst64_compare (i : Int) (n : Nat) (lo : 0 ≤ i) (hi : i ≤ 1000000) (bound : n < 1000000) :
    Compiler.Encoders.Asm.wordCmpHOL .less (smallnum i : BitVec 64) (BitVec.ofNat 64 (4 * n)) =
      decide (i < Int.ofNat n) := by
  have si : smallInt 64 i := by norm_num [smallInt]; omega
  have sn : smallInt 64 (Int.ofNat n) := by norm_num [smallInt]; omega
  have encoding : (smallnum (Int.ofNat n) : BitVec 64) = BitVec.ofNat 64 (4 * n) := by
    rw [smallnum_eq_inlined]
    simp
  rw [← encoding, Compiler.Encoders.Asm.wordCmpHOL, signedLess64]
  apply Bool.eq_iff_iff.mpr
  simpa using (Memory.numLessThm i (Int.ofNat n) ⟨Or.inr rfl, si, sn⟩).symm

/-- The target implements source-safe bounded integer comparison with an
immediate signed comparison and produces a represented Boolean. -/
theorem assignLessConst64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src : Nat) (n : Nat) (i : Int) (sourceRun : DataSem.getVar src source.locals = some (.number i))
    (lo : 0 ≤ i) (hi : i ≤ 1000000) (bound : n < 1000000) :
    continues64 conf secn label l1 l2 (.assign dest (.intOp (.lessConstSmall n)) [src] none) source target locs := by
  let op := ClosLang.Op.intOp (.lessConstSmall n)
  let middle := DataSem.doStack op [.number i] (DataSem.doLimSafe source op [.number i])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [.number i]
  have small : smallInt 64 i := by norm_num [smallInt]; omega
  have targetRun := stateRel64_getSmallNumber conf l1 l2 source target locs related src i sourceRun small
  let b := decide (i < Int.ofNat n)
  refine ⟨DataSem.setVar dest (DataSem.boolValue b) middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word (if b then 18 else 2)) target, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.doIntApp, lo, hi, bound, DataSem.installSfs, op, middle, b]
  · simp only [compileControl64, compileControl?, Option.getD_some]
    change WordSemStateFiniteExact.evaluate (.ite .less (adjustVar src) (.imm (BitVec.ofNat 64 (4 * n)))
      (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))) target = _
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
      targetRun, lessConst64_compare i n lo hi bound, WordSemStateFiniteExact.wordExp, b]
    cases cmp : decide (i < Int.ofNat n) <;> simp_all
    have notLess : ¬ i < (n : Int) := not_lt_of_ge cmp
    simp [notLess]
  · exact stateRel64_setBool conf l1 l2 middle target locs middleRel dest b

/-- Source type safety supplies a numeric operand and the original comparison
bounds. -/
theorem assignLessConst64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src n : Nat)
    (safe : (DataSem.evaluate (.assign dest (.intOp (.lessConstSmall n)) [src] none) source).1 ≠
      some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.intOp (.lessConstSmall n)) [src] none) source target locs := by
  cases sourceRun : DataSem.getVar src source.locals with
  | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun] at safe
  | some value =>
    cases value with
    | number i =>
      by_cases bounds : 0 ≤ i ∧ i ≤ 1000000 ∧ n < 1000000
      · exact assignLessConst64 conf secn label l1 l2 source target locs related dest src n i sourceRun bounds.1 bounds.2.1 bounds.2.2
      · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
          DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
          DataSem.applyNonFfi, DataSem.doIntApp, bounds] at safe
    | word64 w =>
      simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
        DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
        DataSem.applyNonFfi, DataSem.doIntApp] at safe
    | block stamp tag values =>
      simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
        DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
        DataSem.applyNonFfi, DataSem.doIntApp] at safe
    | codePtr loc =>
      simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
        DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
        DataSem.applyNonFfi, DataSem.doIntApp] at safe
    | refPtr flag loc =>
      simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
        DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
        DataSem.applyNonFfi, DataSem.doIntApp] at safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
