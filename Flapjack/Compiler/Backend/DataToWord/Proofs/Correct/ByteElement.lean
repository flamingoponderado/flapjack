import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ByteBounds
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.ByteElement

/-! Dynamic byte-array reads in the 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A valid byte-array read is simulated by the actual address calculation,
byte-load instruction, and integer encoding. -/
theorem assignByteElement64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest base index ref n : Nat) (bit flag : Bool) (bytes : List (BitVec 8))
    (baseRun : DataSem.getVar base source.locals = some (.refPtr bit ref))
    (indexRun : DataSem.getVar index source.locals = some (.number (Int.ofNat n)))
    (bound : n < bytes.length) (found : sptLookup ref source.refs = some (.byteArray flag bytes)) :
    continues64 conf secn label l1 l2 (.assign dest (.memOp .derefByte) [base, index] none) source target locs := by
  let op := ClosLang.Op.memOp .derefByte
  let middle := DataSem.doStack op [.refPtr bit ref, .number (Int.ofNat n)]
    (DataSem.doLimSafe source op [.refPtr bit ref, .number (Int.ofNat n)])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [.refPtr bit ref, .number (Int.ofNat n)]
  obtain ⟨addr, addrRun, read⟩ := stateRel64_loadByteElement conf l1 l2 source target locs related
    base index ref n bit flag bytes baseRun indexRun found bound
  let byte := bytes[n]
  let target1 := WordSemStateFiniteExact.setVar 1 (.word addr) target
  let target2 := WordSemStateFiniteExact.setVar 3 (.word (byte.setWidth 64)) target1
  have rel1 : stateRel64 conf l1 l2 middle target1 none locs :=
    stateRel64_setScratch1 conf l1 l2 middle target locs middleRel _
  have rel2 : stateRel64 conf l1 l2 middle target2 none locs := by
    apply stateRel64_setScratch conf l1 l2 middle target1 locs rel1 3 _ (by decide)
    intro k
    simp [adjustVar]
  have small : smallInt 64 (Int.ofNat byte.toNat) := by
    have h := byte.isLt
    norm_num [smallInt] at h ⊢
    omega
  refine ⟨DataSem.setVar dest (.number byte.toNat) middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word (smallnum (Int.ofNat byte.toNat))) target2, ?_, ?_, ?_⟩
  · have nonnegative : ¬ ((n : Int) < 0) := Int.not_lt.mpr (Int.natCast_nonneg _)
    simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun, indexRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, DataSem.doStack, DataSem.doLimSafe, found, op, middle, bound, nonnegative, byte]
  · have first : WordSemStateFiniteExact.evaluate
        (.assign 1 (.op .add [realAddr conf (adjustVar base),
          .op .add [.const 8, shiftN .lsr (.var (adjustVar index)) 2]])) target = (none, target1) := by
      simp only [WordSemStateFiniteExact.evaluate, addrRun]
      rfl
    have read1 : WordSemStateFiniteExact.getVar 1 target1 = some (.word addr) := by
      simp [target1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
    have read1mem : memLoadByteAuxExact target1.memory target1.mdomain target1.be addr = some byte := by
      simpa [target1, WordSemStateFiniteExact.setVar, byte] using read
    have second : WordSemStateFiniteExact.evaluate (.inst (.mem .load8 3 (.addr 1 0))) target1 = (none, target2) := by
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, WordSemStateFiniteExact.wordExp,
        wordOpHOL, wordOp, theWords, read1, target2, read1mem]
    have read3 : WordSemStateFiniteExact.getVar 3 target2 = some (.word (byte.setWidth 64)) := by
      simp [target2, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
    have encoded : (byte.setWidth 64 <<< (2 : Nat)) = (smallnum (Int.ofNat byte.toNat) : BitVec 64) := by
      have nonnegative : ¬ ((byte.toNat : Int) < 0) := Int.not_lt.mpr (Int.natCast_nonneg _)
      simp [smallnum_eq_inlined, BitVec.ofNat_mul, nonnegative]
      bv_decide
    have third : WordSemStateFiniteExact.evaluate (.assign (adjustVar dest) (shiftN .lsl (.var 3) 2)) target2 =
        (none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word (smallnum (Int.ofNat byte.toNat))) target2) := by
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, shiftN, read3, wordShiftHOL, encoded]
    have fix1 : WordSemStateFiniteExact.fixClock target ((none : Option (WordSemResult 64)), target1) = (none, target1) := by
      simp [WordSemStateFiniteExact.fixClock, target1, WordSemStateFiniteExact.setVar]
    have fix2 : WordSemStateFiniteExact.fixClock target1 ((none : Option (WordSemResult 64)), target2) = (none, target2) := by
      simp [WordSemStateFiniteExact.fixClock, target2, WordSemStateFiniteExact.setVar]
    simp only [compileControl64, compileControl?, Option.getD_some]
    change WordSemStateFiniteExact.evaluate (wordListSeq [
      .assign 1 (.op .add [realAddr conf (adjustVar base), .op .add [.const 8, shiftN .lsr (.var (adjustVar index)) 2]]),
      .inst (.mem .load8 3 (.addr 1 0)), .assign (adjustVar dest) (shiftN .lsl (.var 3) 2)]) target = _
    simp only [wordListSeq, WordSemStateFiniteExact.evaluate, first, fix1, second, fix2, third]
  · exact stateRel64_setSmallInt conf l1 l2 middle target2 locs rel2 dest (Int.ofNat byte.toNat) small

/-- Source safety supplies an in-range nonnegative index and a byte-array
reference. -/
theorem assignByteElement64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest base index : Nat)
    (safe : (DataSem.evaluate (.assign dest (.memOp .derefByte) [base, index] none) source).1 ≠
      some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.memOp .derefByte) [base, index] none) source target locs := by
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
        cases i with
        | negSucc n =>
          cases found : sptLookup ref source.refs <;> simp [found] at safe
          case some val => cases val <;> simp at safe
        | ofNat n =>
          cases found : sptLookup ref source.refs with
          | none => simp [found] at safe
          | some entry =>
            cases entry with
            | byteArray flag bytes =>
              by_cases bound : n < bytes.length
              · exact assignByteElement64 conf secn label l1 l2 source target locs related dest base index ref n bit flag bytes baseRun indexRun bound found
              · simp [found, bound] at safe
            | valueArray values => simp [found] at safe
            | thunk mode value => simp [found] at safe
            | mutBlock tag flag values => simp [found] at safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
