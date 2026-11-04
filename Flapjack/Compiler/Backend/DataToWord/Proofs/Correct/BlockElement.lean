import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.BlockLength
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.BlockElement

/-! Constructor field reads in the 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A valid field read from a source constructor is simulated by the
compiled memory load. The source operation also accepts value-array
references; that separate case is not asserted by this theorem. -/
theorem assignBlockElement64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src stamp tag index : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar src source.locals = some (.block stamp tag values))
    (bound : index < values.length) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.elemAt index)) [src] none) source target locs := by
  let op := ClosLang.Op.blockOp (.elemAt index)
  let middle := DataSem.doStack op [.block stamp tag values] (DataSem.doLimSafe source op [.block stamp tag values])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [.block stamp tag values]
  have middleRun : DataSem.getVar src middle.locals = some (.block stamp tag values) := by
    simpa [middle, DataSem.doStack, DataSem.doLimSafe] using sourceRun
  obtain ⟨child, targetRun, newMemory⟩ :=
    stateRel64_loadBlockElement conf l1 l2 middle target locs middleRel src stamp tag values index middleRun bound
  refine ⟨DataSem.setVar dest values[index] middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) child target, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, op, middle, bound]
  · simp only [compileControl64, compileControl?, Option.getD_some]
    change WordSemStateFiniteExact.evaluate (.assign (adjustVar dest)
      (.load (.op .add [realAddr conf (adjustVar src),
        .const (BitVec.ofNat 64 8 + BitVec.ofNat 64 8 * BitVec.ofNat 64 index)]))) target = _
    simp [WordSemStateFiniteExact.evaluate, targetRun]
  · exact stateRel64_setNewLocal conf l1 l2 middle target locs middleRel dest values[index] child newMemory

/-- A valid field read from a source value-array reference is simulated by the
compiled memory load. This uses the value-array heap invariant. -/
theorem assignRefArrayElement64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src : Nat) (bit : Bool) (ref index : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar src source.locals = some (.refPtr bit ref))
    (bound : index < values.length)
    (found : sptLookup ref source.refs = some (.valueArray values)) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.elemAt index)) [src] none) source target locs := by
  let op := ClosLang.Op.blockOp (.elemAt index)
  let middle := DataSem.doStack op [.refPtr bit ref] (DataSem.doLimSafe source op [.refPtr bit ref])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [.refPtr bit ref]
  have middleRun : DataSem.getVar src middle.locals = some (.refPtr bit ref) := by
    simpa [middle, DataSem.doStack, DataSem.doLimSafe] using sourceRun
  have middleFound : sptLookup ref middle.refs = some (.valueArray values) := by
    simpa [middle, DataSem.doStack, DataSem.doLimSafe] using found
  obtain ⟨child, targetRun, newMemory⟩ :=
    stateRel64_loadRefArrayElement conf l1 l2 middle target locs middleRel src bit ref values index middleRun bound middleFound
  refine ⟨DataSem.setVar dest values[index] middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) child target, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, DataSem.doStack, DataSem.doLimSafe, op, middle, bound, found]
  · simp only [compileControl64, compileControl?, Option.getD_some]
    change WordSemStateFiniteExact.evaluate (.assign (adjustVar dest)
      (.load (.op .add [realAddr conf (adjustVar src),
        .const (BitVec.ofNat 64 8 + BitVec.ofNat 64 8 * BitVec.ofNat 64 index)]))) target = _
    simp [WordSemStateFiniteExact.evaluate, targetRun]
  · exact stateRel64_setNewLocal conf l1 l2 middle target locs middleRel dest values[index] child newMemory

/-- Source safety supplies either a valid constructor or value-array element. -/
theorem assignElement64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src index : Nat)
    (safe : (DataSem.evaluate (.assign dest (.blockOp (.elemAt index)) [src] none) source).1 ≠
      some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.elemAt index)) [src] none) source target locs := by
  cases sourceRun : DataSem.getVar src source.locals with
  | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun] at safe
  | some value =>
    cases value with
    | number n =>
      simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
        DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux, DataSem.applyNonFfi] at safe
    | word64 w =>
      simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
        DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux, DataSem.applyNonFfi] at safe
    | codePtr loc =>
      simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
        DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux, DataSem.applyNonFfi] at safe
    | block stamp tag values =>
      by_cases bound : index < values.length
      · exact assignBlockElement64 conf secn label l1 l2 source target locs related dest src stamp tag index values sourceRun bound
      · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
          DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux, DataSem.applyNonFfi, bound] at safe
    | refPtr bit ref =>
      cases found : sptLookup ref source.refs with
      | none =>
        simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
          DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux, DataSem.applyNonFfi,
          DataSem.doStack, DataSem.doLimSafe, found] at safe
      | some entry =>
        cases entry with
        | byteArray flag bytes =>
          simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
            DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux, DataSem.applyNonFfi,
            DataSem.doStack, DataSem.doLimSafe, found] at safe
        | thunk mode value =>
          simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
            DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux, DataSem.applyNonFfi,
            DataSem.doStack, DataSem.doLimSafe, found] at safe
        | mutBlock tag final left child right =>
          simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
            DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux, DataSem.applyNonFfi,
            DataSem.doStack, DataSem.doLimSafe, found] at safe
        | valueArray values =>
          by_cases bound : index < values.length
          · exact assignRefArrayElement64 conf secn label l1 l2 source target locs related dest src bit ref index values sourceRun bound found
          · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
              DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux, DataSem.applyNonFfi,
              DataSem.doStack, DataSem.doLimSafe, found, bound] at safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
