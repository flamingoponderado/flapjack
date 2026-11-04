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

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
