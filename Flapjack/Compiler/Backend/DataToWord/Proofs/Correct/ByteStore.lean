import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ByteElement
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.ByteStore
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Construct

/-! Dynamic byte-array updates in the 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A valid byte update is simulated by the generated address calculation,
value decoding, byte-store instruction and unit result. -/
theorem assignByteStore64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest base index value ref n : Nat) (bit flag : Bool) (bytes : List (BitVec 8)) (byte : BitVec 8)
    (baseRun : DataSem.getVar base source.locals = some (.refPtr bit ref))
    (indexRun : DataSem.getVar index source.locals = some (.number (Int.ofNat n)))
    (valueRun : DataSem.getVar value source.locals = some (.number (Int.ofNat byte.toNat)))
    (bound : n < bytes.length) (found : sptLookup ref source.refs = some (.byteArray flag bytes)) :
    continues64 conf secn label l1 l2 (.assign dest (.memOp .updateByte) [base, index, value] none) source target locs := by
  let op := ClosLang.Op.memOp .updateByte
  let args : List DataSem.Value := [.refPtr bit ref, .number (Int.ofNat n), .number (Int.ofNat byte.toNat)]
  let middle := DataSem.doStack op args (DataSem.doLimSafe source op args)
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op args
  have small : smallInt 64 (Int.ofNat byte.toNat) := by
    have h := byte.isLt
    norm_num [smallInt] at h ⊢
    omega
  have targetValue := stateRel64_getSmallNumber conf l1 l2 source target locs related value _ valueRun small
  have middleBase : DataSem.getVar base middle.locals = some (.refPtr bit ref) := by
    simpa [middle, DataSem.doStack, DataSem.doLimSafe, op, args] using baseRun
  have middleIndex : DataSem.getVar index middle.locals = some (.number (Int.ofNat n)) := by
    simpa [middle, DataSem.doStack, DataSem.doLimSafe, op, args] using indexRun
  have middleFound : sptLookup ref middle.refs = some (.byteArray flag bytes) := by
    simpa [middle, DataSem.doStack, DataSem.doLimSafe, op, args] using found
  obtain ⟨addr, updated, addrRun, storeRun, storeRel⟩ :=
    stateRel64_storeByteElement conf l1 l2 middle target locs middleRel base index ref n bit flag bytes byte
      middleBase middleIndex middleFound bound
  let source1 := { middle with refs := sptInsert ref (.byteArray flag (bytes.set n byte)) middle.refs }
  let target1 := WordSemStateFiniteExact.setVar 1 (.word addr) target
  let target2 := WordSemStateFiniteExact.setVar 3 (.word (byte.setWidth 64)) target1
  let target3 := { target2 with memory := updated }
  have rel1 : stateRel64 conf l1 l2 source1 { target with memory := updated } none locs := storeRel
  have rel2 : stateRel64 conf l1 l2 source1 (WordSemStateFiniteExact.setVar 1 (.word addr) { target with memory := updated }) none locs :=
    stateRel64_setScratch1 conf l1 l2 source1 _ locs rel1 _
  have rel3 : stateRel64 conf l1 l2 source1 target3 none locs := by
    have h := stateRel64_setScratch conf l1 l2 source1 _ locs rel2 3 (.word (byte.setWidth 64)) (by decide) (by intro k; simp [adjustVar])
    simpa [target3, target2, target1, WordSemStateFiniteExact.setVar] using h
  have readValue : WordSemStateFiniteExact.getVar (adjustVar value) target1 = some (.word (smallnum (Int.ofNat byte.toNat))) := by
    simpa [target1, getVar_setScratch1] using targetValue
  have decoded : ((smallnum (Int.ofNat byte.toNat) : BitVec 64) >>> (2 : Nat)) = byte.setWidth 64 := by
    have nonnegative : ¬ ((byte.toNat : Int) < 0) := Int.not_lt.mpr (Int.natCast_nonneg _)
    simp [smallnum_eq_inlined, BitVec.ofNat_mul, nonnegative]
    have limit := byte.isLt
    bv_decide
  refine ⟨DataSem.setVar dest DataSem.unitValue source1,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) target3, ?_, ?_, ?_⟩
  · have nonnegative : ¬ ((n : Int) < 0) := Int.not_lt.mpr (Int.natCast_nonneg _)
    have notge : ¬ bytes.length ≤ n := by omega
    simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun, indexRun, valueRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, DataSem.doStack, DataSem.doLimSafe, found, op, args, middle,
      notge, nonnegative, ClosSem.intToByte_toNat, source1]
  · have first : WordSemStateFiniteExact.evaluate
        (.assign 1 (.op .add [realAddr conf (adjustVar base),
          .op .add [.const 8, shiftN .lsr (.var (adjustVar index)) 2]])) target = (none, target1) := by
      simp only [WordSemStateFiniteExact.evaluate, addrRun]
      rfl
    have second : WordSemStateFiniteExact.evaluate (.assign 3 (shiftN .lsr (.var (adjustVar value)) 2)) target1 =
        (none, target2) := by
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, shiftN, readValue, wordShiftHOL, target2]
      change WordSemStateFiniteExact.setVar 3 (.word ((smallnum (Int.ofNat byte.toNat) : BitVec 64) >>> (2 : Nat))) target1 =
        WordSemStateFiniteExact.setVar 3 (.word (byte.setWidth 64)) target1
      rw [decoded]
    have readAddr : WordSemStateFiniteExact.getVar 1 target2 = some (.word addr) := by
      simp [target2, target1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
    have readByte : WordSemStateFiniteExact.getVar 3 target2 = some (.word (byte.setWidth 64)) := by
      simp [target2, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
    have store2 : memStoreByteAuxExact target2.memory target2.mdomain target2.be addr byte = some updated := by
      simpa [target2, target1, WordSemStateFiniteExact.setVar] using storeRun
    have third : WordSemStateFiniteExact.evaluate (.inst (.mem .store8 3 (.addr 1 0))) target2 = (none, target3) := by
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, WordSemStateFiniteExact.wordExp,
        wordOpHOL, wordOp, theWords, readAddr, readByte, store2, target3]
    have fourth : WordSemStateFiniteExact.evaluate (.assign (adjustVar dest) (.const 2)) target3 =
        (none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) target3) := by
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp]
    have fix1 : WordSemStateFiniteExact.fixClock target ((none : Option (WordSemResult 64)), target1) = (none, target1) := by
      simp [WordSemStateFiniteExact.fixClock, target1, WordSemStateFiniteExact.setVar]
    have fix2 : WordSemStateFiniteExact.fixClock target1 ((none : Option (WordSemResult 64)), target2) = (none, target2) := by
      simp [WordSemStateFiniteExact.fixClock, target2, WordSemStateFiniteExact.setVar]
    have fix3 : WordSemStateFiniteExact.fixClock target2 ((none : Option (WordSemResult 64)), target3) = (none, target3) := by
      simp [WordSemStateFiniteExact.fixClock, target3]
    simp only [compileControl64, compileControl?, Option.getD_some]
    change WordSemStateFiniteExact.evaluate (wordListSeq [
      .assign 1 (.op .add [realAddr conf (adjustVar base), .op .add [.const 8, shiftN .lsr (.var (adjustVar index)) 2]]),
      .assign 3 (shiftN .lsr (.var (adjustVar value)) 2), .inst (.mem .store8 3 (.addr 1 0)),
      .assign (adjustVar dest) (.const 2)]) target = _
    simp only [wordListSeq, WordSemStateFiniteExact.evaluate, first, fix1, second, fix2, third, fix3, fourth]
  · simpa [DataSem.unitValue] using stateRel64_setEmptyBlock conf l1 l2 source1 target3 locs rel3 dest 0 (by norm_num)

/-- Source safety supplies a byte-array reference, in-range index and a byte
value, so the generated update sequence simulates every safe source update. -/
theorem assignByteStore64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest base index value : Nat)
    (safe : (DataSem.evaluate (.assign dest (.memOp .updateByte) [base, index, value] none) source).1 ≠
      some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.memOp .updateByte) [base, index, value] none) source target locs := by
  cases baseRun : DataSem.getVar base source.locals with
  | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun] at safe
  | some baseVal =>
    cases indexRun : DataSem.getVar index source.locals with
    | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun, indexRun] at safe
    | some indexVal =>
      cases valueRun : DataSem.getVar value source.locals with
      | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun, indexRun, valueRun] at safe
      | some valueVal =>
        cases baseVal <;> cases indexVal <;> cases valueVal <;>
          simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun, indexRun, valueRun,
            DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
            DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe] at safe
        case refPtr.number.number bit ref idx val =>
          cases idx with
          | negSucc n =>
            cases found : sptLookup ref source.refs <;> simp [found] at safe
            case some entry => cases entry <;> simp at safe
          | ofNat n =>
            cases found : sptLookup ref source.refs with
            | none => simp [found] at safe
            | some entry =>
              cases entry with
              | byteArray flag bytes =>
                by_cases bound : n < bytes.length
                · cases converted : ClosSem.intToByte val with
                  | none => simp [found, converted] at safe
                  | some byte =>
                    have valEq := (ClosSem.intToByte_iff val byte).mp converted
                    subst val
                    exact assignByteStore64 conf secn label l1 l2 source target locs related dest base index value ref n bit flag bytes byte baseRun indexRun valueRun bound found
                · have ge : bytes.length ≤ n := Nat.le_of_not_gt bound
                  simp [found, ge] at safe
              | valueArray values => simp [found] at safe
              | thunk mode item => simp [found] at safe
              | mutBlock tag flag values => simp [found] at safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
