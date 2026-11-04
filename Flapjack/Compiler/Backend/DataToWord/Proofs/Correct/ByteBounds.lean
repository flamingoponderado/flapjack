import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.BlockBounds
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.ByteBounds

/-! Byte-array bounds checks in the 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- Both the strict and inclusive byte bounds checks simulate their source
operations for any related integer index. -/
theorem assignByteBounds64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest base index ref : Nat) (bit flag loose : Bool) (bytes : List (BitVec 8)) (i : Int)
    (baseRun : DataSem.getVar base source.locals = some (.refPtr bit ref))
    (indexRun : DataSem.getVar index source.locals = some (.number i))
    (found : sptLookup ref source.refs = some (.byteArray flag bytes)) :
    continues64 conf secn label l1 l2 (.assign dest (.memOp (.boundsCheckByte loose)) [base, index] none) source target locs := by
  let op := ClosLang.Op.memOp (.boundsCheckByte loose)
  let middle := DataSem.doStack op [.refPtr bit ref, .number i]
    (DataSem.doLimSafe source op [.refPtr bit ref, .number i])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [.refPtr bit ref, .number i]
  obtain ⟨bound, load⟩ := stateRel64_loadByteLength conf l1 l2 source target locs related base bit flag ref bytes baseRun found
  obtain ⟨w, targetRun, strict⟩ := stateRel64_getNumberBounds conf l1 l2 source target locs related
    index i indexRun bytes.length (by omega)
  obtain ⟨w', targetRun', inclusive⟩ := stateRel64_getNumberBoundsLe conf l1 l2 source target locs related
    index i indexRun bytes.length bound
  have same : w = w' := by rw [targetRun] at targetRun'; exact WordLocW.word.inj (Option.some.inj targetRun')
  subst w'
  let result := decide (0 ≤ i ∧ if loose then i ≤ (bytes.length : Int) else i < (bytes.length : Int))
  let target1 := WordSemStateFiniteExact.setVar 1 (.word (BitVec.ofNat 64 bytes.length)) target
  let target2 := WordSemStateFiniteExact.setVar 3 (.word (w.rotateRight 2)) target1
  have rel1 : stateRel64 conf l1 l2 middle target1 none locs :=
    stateRel64_setScratch1 conf l1 l2 middle target locs middleRel _
  have rel2 : stateRel64 conf l1 l2 middle target2 none locs := by
    apply stateRel64_setScratch conf l1 l2 middle target1 locs rel1 3 _ (by decide)
    intro n
    simp [adjustVar]
  have readIndex : WordSemStateFiniteExact.getVar (adjustVar index) target1 = some (.word w) := by
    simpa [target1, getVar_setScratch1] using targetRun
  have nNat : (BitVec.ofNat 64 bytes.length).toNat = bytes.length := by
    simp only [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    norm_num
    omega
  have cmpStrict : Compiler.Encoders.Asm.wordCmpHOL .lower (w.rotateRight 2) (BitVec.ofNat 64 bytes.length) =
      decide (0 ≤ i ∧ i < (bytes.length : Int)) := by
    apply Bool.eq_iff_iff.mpr
    simpa [Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, nNat] using strict
  have cmpInclusive : Compiler.Encoders.Asm.wordCmpHOL .notLower (BitVec.ofNat 64 bytes.length) (w.rotateRight 2) =
      decide (0 ≤ i ∧ i ≤ (bytes.length : Int)) := by
    apply Bool.eq_iff_iff.mpr
    simpa [Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, nNat, not_lt] using inclusive
  refine ⟨DataSem.setVar dest (DataSem.boolValue result) middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word (if result then 18 else 2)) target2, ?_, ?_, ?_⟩
  · cases loose <;> simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun, indexRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, DataSem.doStack, DataSem.doLimSafe, found, op, middle, result]
  · have first : WordSemStateFiniteExact.evaluate
        (.assign 1 (.op .sub [shiftN .lsr (.load (realAddr conf (adjustVar base))) (64 - conf.lenSize - 3), .const 8])) target =
        (none, target1) := by simp only [WordSemStateFiniteExact.evaluate, load]; rfl
    have second : WordSemStateFiniteExact.evaluate (.assign 3 (shiftVar .ror (adjustVar index) 2)) target1 =
        (none, target2) := by
      simp [WordSemStateFiniteExact.evaluate, shiftVar, shiftN, WordSemStateFiniteExact.wordExp,
        readIndex, wordShiftHOL, target2]
    have read1 : WordSemStateFiniteExact.getVar 1 target2 = some (.word (BitVec.ofNat 64 bytes.length)) := by
      simp [target2, target1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
    have read3 : WordSemStateFiniteExact.getVar 3 target2 = some (.word (w.rotateRight 2)) := by
      simp [target2, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
    have fix1 : WordSemStateFiniteExact.fixClock target ((none : Option (WordSemResult 64)), target1) = (none, target1) := by
      simp [WordSemStateFiniteExact.fixClock, target1, WordSemStateFiniteExact.setVar]
    have fix2 : WordSemStateFiniteExact.fixClock target1 ((none : Option (WordSemResult 64)), target2) = (none, target2) := by
      simp [WordSemStateFiniteExact.fixClock, target2, WordSemStateFiniteExact.setVar]
    have third : WordSemStateFiniteExact.evaluate
        (if loose then .ite .notLower 1 (.reg 3) (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))
         else .ite .lower 3 (.reg 1) (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))) target2 =
        (none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word (if result then 18 else 2)) target2) := by
      cases loose <;> simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
        WordSemStateFiniteExact.wordExp, read1, read3, cmpStrict, cmpInclusive, result]
      all_goals split <;> simp_all
      all_goals split <;> simp_all; omega
    simp only [compileControl64, compileControl?, Option.getD_some]
    change WordSemStateFiniteExact.evaluate (wordListSeq [
      .assign 1 (.op .sub [shiftN .lsr (.load (realAddr conf (adjustVar base))) (64 - conf.lenSize - 3), .const 8]),
      .assign 3 (shiftVar .ror (adjustVar index) 2),
      if loose then .ite .notLower 1 (.reg 3) (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))
      else .ite .lower 3 (.reg 1) (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))]) target = _
    simp only [wordListSeq, WordSemStateFiniteExact.evaluate, first, fix1, second, fix2, third]
  · exact stateRel64_setBool conf l1 l2 middle target2 locs rel2 dest result

/-- Source safety supplies a byte-array reference and numeric index. -/
theorem assignByteBounds64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest base index : Nat) (loose : Bool)
    (safe : (DataSem.evaluate (.assign dest (.memOp (.boundsCheckByte loose)) [base, index] none) source).1 ≠
      some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.memOp (.boundsCheckByte loose)) [base, index] none) source target locs := by
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
          | byteArray flag bytes => exact assignByteBounds64 conf secn label l1 l2 source target locs related dest base index ref bit flag loose bytes i baseRun indexRun found
          | valueArray values => simp [found] at safe
          | thunk mode value => simp [found] at safe
          | mutBlock tag flag values => simp [found] at safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
