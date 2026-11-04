import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.BlockElement
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.BlockLengthEq
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.ArrayBounds
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.ArrayElement

/-! Dynamic reads from blocks and value arrays in the 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A dynamic read of a related constructor field follows its source value. -/
theorem assignDynamicBlockElement64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest base index stamp tag n : Nat) (values : List DataSem.Value)
    (baseRun : DataSem.getVar base source.locals = some (.block stamp tag values))
    (indexRun : DataSem.getVar index source.locals = some (.number (Int.ofNat n)))
    (bound : n < values.length) :
    continues64 conf secn label l1 l2 (.assign dest (.memOp .el) [base, index] none) source target locs := by
  let op := ClosLang.Op.memOp .el
  let middle := DataSem.doStack op [.block stamp tag values, .number (Int.ofNat n)]
    (DataSem.doLimSafe source op [.block stamp tag values, .number (Int.ofNat n)])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [.block stamp tag values, .number (Int.ofNat n)]
  have lenBound := stateRel64_blockLengthBound conf l1 l2 source target locs related base stamp tag values baseRun
  have small : smallInt 64 (Int.ofNat n) := by norm_num [smallInt] at lenBound ⊢; omega
  have targetIndex := stateRel64_getSmallNumber conf l1 l2 source target locs related index _ indexRun small
  have middleRun : DataSem.getVar base middle.locals = some (.block stamp tag values) := by
    simpa [middle, DataSem.doStack, DataSem.doLimSafe] using baseRun
  obtain ⟨child, load, newMemory⟩ := stateRel64_loadBlockElement conf l1 l2 middle target locs middleRel
    base stamp tag values n middleRun bound
  have dynamic := dynamicElementExp64 conf target base index n targetIndex
  refine ⟨DataSem.setVar dest values[n] middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) child target, ?_, ?_, ?_⟩
  · have nonnegative : ¬ ((n : Int) < 0) := Int.not_lt.mpr (Int.natCast_nonneg _)
    simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun, indexRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, op, middle, bound, nonnegative]
  · simp only [compileControl64, compileControl?, Option.getD_some]
    change WordSemStateFiniteExact.evaluate (.assign (adjustVar dest)
      (.load (.op .add [realAddr conf (adjustVar base),
        .op .add [.const 8, .shift .lsl (.var (adjustVar index)) (.const 1)]]))) target = _
    simp only [WordSemStateFiniteExact.evaluate, dynamic, load]
  · exact stateRel64_setNewLocal conf l1 l2 middle target locs middleRel dest values[n] child newMemory

/-- A dynamic read of a related value-array field follows its source value. -/
theorem assignDynamicArrayElement64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest base index ref n : Nat) (bit : Bool) (values : List DataSem.Value)
    (baseRun : DataSem.getVar base source.locals = some (.refPtr bit ref))
    (indexRun : DataSem.getVar index source.locals = some (.number (Int.ofNat n)))
    (bound : n < values.length) (found : sptLookup ref source.refs = some (.valueArray values)) :
    continues64 conf secn label l1 l2 (.assign dest (.memOp .el) [base, index] none) source target locs := by
  let op := ClosLang.Op.memOp .el
  let middle := DataSem.doStack op [.refPtr bit ref, .number (Int.ofNat n)]
    (DataSem.doLimSafe source op [.refPtr bit ref, .number (Int.ofNat n)])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [.refPtr bit ref, .number (Int.ofNat n)]
  obtain ⟨lenBound, _⟩ := stateRel64_loadArrayLength conf l1 l2 source target locs related base bit ref values baseRun found
  have small : smallInt 64 (Int.ofNat n) := by norm_num [smallInt]; omega
  have targetIndex := stateRel64_getSmallNumber conf l1 l2 source target locs related index _ indexRun small
  have middleRun : DataSem.getVar base middle.locals = some (.refPtr bit ref) := by
    simpa [middle, DataSem.doStack, DataSem.doLimSafe] using baseRun
  have middleFound : sptLookup ref middle.refs = some (.valueArray values) := by
    simpa [middle, DataSem.doStack, DataSem.doLimSafe] using found
  obtain ⟨child, load, newMemory⟩ := stateRel64_loadRefArrayElement conf l1 l2 middle target locs middleRel
    base bit ref values n middleRun bound middleFound
  have dynamic := dynamicElementExp64 conf target base index n targetIndex
  refine ⟨DataSem.setVar dest values[n] middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) child target, ?_, ?_, ?_⟩
  · have nonnegative : ¬ ((n : Int) < 0) := Int.not_lt.mpr (Int.natCast_nonneg _)
    simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun, indexRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, DataSem.doStack, DataSem.doLimSafe, found, op, middle, bound, nonnegative]
  · simp only [compileControl64, compileControl?, Option.getD_some]
    change WordSemStateFiniteExact.evaluate (.assign (adjustVar dest)
      (.load (.op .add [realAddr conf (adjustVar base),
        .op .add [.const 8, .shift .lsl (.var (adjustVar index)) (.const 1)]]))) target = _
    simp only [WordSemStateFiniteExact.evaluate, dynamic, load]
  · exact stateRel64_setNewLocal conf l1 l2 middle target locs middleRel dest values[n] child newMemory

/-- A source-safe dynamic element read has a nonnegative in-range index and
either a constructor block or a value-array reference. -/
theorem assignDynamicElement64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest base index : Nat)
    (safe : (DataSem.evaluate (.assign dest (.memOp .el) [base, index] none) source).1 ≠
      some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.memOp .el) [base, index] none) source target locs := by
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
      case block.number stamp tag values i =>
        cases i with
        | negSucc n => simp at safe
        | ofNat n =>
          by_cases bound : n < values.length
          · exact assignDynamicBlockElement64 conf secn label l1 l2 source target locs related dest base index stamp tag n values baseRun indexRun bound
          · simp [bound] at safe
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
            | valueArray values =>
              by_cases bound : n < values.length
              · exact assignDynamicArrayElement64 conf secn label l1 l2 source target locs related dest base index ref n bit values baseRun indexRun bound found
              · simp [found, bound] at safe
            | byteArray flag bytes => simp [found] at safe
            | thunk mode value => simp [found] at safe
            | mutBlock tag flag values => simp [found] at safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
