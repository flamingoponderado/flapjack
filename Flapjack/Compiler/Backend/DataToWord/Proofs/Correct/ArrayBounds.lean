import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.BlockBounds
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.ArrayBounds

/-! Value-array bounds checks in the 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- The generated value-array bounds check simulates the source operation
for any related numeric index. -/
theorem assignArrayBounds64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest base index ref : Nat) (bit : Bool) (values : List DataSem.Value) (i : Int)
    (baseRun : DataSem.getVar base source.locals = some (.refPtr bit ref))
    (indexRun : DataSem.getVar index source.locals = some (.number i))
    (found : sptLookup ref source.refs = some (.valueArray values)) :
    continues64 conf secn label l1 l2 (.assign dest (.memOp .boundsCheckArray) [base, index] none) source target locs := by
  let op := ClosLang.Op.memOp .boundsCheckArray
  let middle := DataSem.doStack op [.refPtr bit ref, .number i]
    (DataSem.doLimSafe source op [.refPtr bit ref, .number i])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [.refPtr bit ref, .number i]
  obtain ⟨bound, load⟩ := stateRel64_loadArrayLength conf l1 l2 source target locs related base bit ref values baseRun found
  obtain ⟨w, targetRun, comparison⟩ := stateRel64_getNumberBounds conf l1 l2 source target locs related
    index i indexRun values.length (by omega)
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
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun, indexRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, DataSem.doStack, DataSem.doLimSafe, found, op, middle, result]
  · have first : WordSemStateFiniteExact.evaluate
        (.assign 1 (shiftN .lsr (.load (realAddr conf (adjustVar base))) (64 - conf.lenSize))) target =
        (none, target1) := by simp only [WordSemStateFiniteExact.evaluate, load]; rfl
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
      .assign 1 (shiftN .lsr (.load (realAddr conf (adjustVar base))) (64 - conf.lenSize)),
      .assign 3 (shiftVar .ror (adjustVar index) 2),
      .ite .lower 3 (.reg 1) (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))]) target = _
    simp only [wordListSeq, WordSemStateFiniteExact.evaluate, first, fix1, second, fix2, third]
  · exact stateRel64_setBool conf l1 l2 middle target2 locs rel2 dest result

/-- Source safety supplies a value-array reference and numeric index. -/
theorem assignArrayBounds64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest base index : Nat)
    (safe : (DataSem.evaluate (.assign dest (.memOp .boundsCheckArray) [base, index] none) source).1 ≠
      some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.memOp .boundsCheckArray) [base, index] none) source target locs := by
  cases baseRun : DataSem.getVar base source.locals with
  | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun] at safe
  | some baseVal =>
    cases indexRun : DataSem.getVar index source.locals with
    | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun, indexRun] at safe
    | some indexVal =>
      cases baseVal <;> cases indexVal <;>
        simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun, indexRun,
          DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
          DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe] at safe
      case refPtr.number bit ref i =>
        cases found : sptLookup ref source.refs with
        | none => simp [found] at safe
        | some refVal =>
          cases refVal with
          | valueArray values => exact assignArrayBounds64 conf secn label l1 l2 source target locs related dest base index ref bit values i baseRun indexRun found
          | byteArray flag bytes => simp [found] at safe
          | thunk mode value => simp [found] at safe
          | mutBlock tag flag values => simp [found] at safe

/-- Reading a related value array's length produces the represented source
integer. -/
theorem assignArrayLength64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest base ref : Nat) (bit : Bool) (values : List DataSem.Value)
    (baseRun : DataSem.getVar base source.locals = some (.refPtr bit ref))
    (found : sptLookup ref source.refs = some (.valueArray values)) :
    continues64 conf secn label l1 l2 (.assign dest (.memOp .length) [base] none) source target locs := by
  let op := ClosLang.Op.memOp .length
  let middle := DataSem.doStack op [.refPtr bit ref] (DataSem.doLimSafe source op [.refPtr bit ref])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [.refPtr bit ref]
  obtain ⟨bound, load⟩ := stateRel64_loadArrayLength conf l1 l2 source target locs related base bit ref values baseRun found
  have small : smallInt 64 (Int.ofNat values.length) := by norm_num [smallInt]; omega
  have lenWord : WordSemStateFiniteExact.wordExp target
      (shiftN .lsl (shiftN .lsr (.load (realAddr conf (adjustVar base))) (64 - conf.lenSize)) 2) =
      some (.word (smallnum (Int.ofNat values.length))) := by
    simp only [shiftN] at load
    simp [shiftN, WordSemStateFiniteExact.wordExp, load, wordShiftHOL, smallnum_eq_inlined]
    have nonnegative : ¬ ((values.length : Int) < 0) := Int.not_lt.mpr (Int.natCast_nonneg _)
    simp [nonnegative, BitVec.ofNat_mul]
    bv_decide
  refine ⟨DataSem.setVar dest (.number values.length) middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word (smallnum (Int.ofNat values.length))) target, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, DataSem.doStack, DataSem.doLimSafe, found, op, middle]
  · simp only [compileControl64, compileControl?, Option.getD_some]
    change WordSemStateFiniteExact.evaluate
      (.assign (adjustVar dest) (shiftN .lsl (shiftN .lsr (.load (realAddr conf (adjustVar base))) (64 - conf.lenSize)) 2)) target = _
    simp [WordSemStateFiniteExact.evaluate, lenWord]
  · exact stateRel64_setSmallInt conf l1 l2 middle target locs middleRel dest (Int.ofNat values.length) small

/-- Source safety supplies a value-array reference for length. -/
theorem assignArrayLength64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest base : Nat)
    (safe : (DataSem.evaluate (.assign dest (.memOp .length) [base] none) source).1 ≠
      some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.memOp .length) [base] none) source target locs := by
  cases baseRun : DataSem.getVar base source.locals with
  | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun] at safe
  | some baseVal =>
    cases baseVal <;>
      simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun,
        DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
        DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe] at safe
    case refPtr bit ref =>
      cases found : sptLookup ref source.refs with
      | none => simp [found] at safe
      | some refVal =>
        cases refVal with
        | valueArray values => exact assignArrayLength64 conf secn label l1 l2 source target locs related dest base ref bit values baseRun found
        | byteArray flag bytes => simp [found] at safe
        | thunk mode value => simp [found] at safe
        | mutBlock tag flag values => simp [found] at safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
