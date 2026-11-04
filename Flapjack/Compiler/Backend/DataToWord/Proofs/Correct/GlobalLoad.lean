import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Globals
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GlobalLoad

/-! Global reads in the 64-bit data-to-word simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A valid global read is simulated by the generated indexed word load. -/
theorem assignGlobal64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest ref index : Nat) (values : List DataSem.Value)
    (global : source.global = some ref) (found : sptLookup ref source.refs = some (.valueArray values))
    (bound : index < values.length) :
    continues64 conf secn label l1 l2 (.assign dest (.globOp (.global index)) [] none) source target locs := by
  let op := ClosLang.Op.globOp (.global index)
  let middle := DataSem.doStack op [] (DataSem.doLimSafe source op [])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op []
  have middleGlobal : middle.global = some ref := by simpa [middle, DataSem.doStack, DataSem.doLimSafe, op] using global
  have middleFound : sptLookup ref middle.refs = some (.valueArray values) := by
    simpa [middle, DataSem.doStack, DataSem.doLimSafe, op] using found
  obtain ⟨word, load, extended⟩ := stateRel64_loadGlobal conf l1 l2 middle target locs middleRel ref index values middleGlobal middleFound bound
  refine ⟨DataSem.setVar dest values[index] middle, WordSemStateFiniteExact.setVar (adjustVar dest) word target, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, global, found, bound, DataSem.installSfs, op, middle]
  · simp only [compileControl64, compileControl?, Option.getD_some]
    change target.wordExp (.load (.op .add [.lookup .globReal,
      .const (BitVec.ofNat 64 (64 / 8) * BitVec.ofNat 64 (index + 1))])) = some word at load
    simp only [WordSemStateFiniteExact.evaluate]
    rw [load]
  · exact stateRel64_setNewLocal conf l1 l2 middle target locs middleRel dest _ word extended

/-- Safety supplies an existing global reference and an in-range index. -/
theorem assignGlobal64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs) (dest index : Nat)
    (safe : (DataSem.evaluate (.assign dest (.globOp (.global index)) [] none) source).1 ≠ some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.globOp (.global index)) [] none) source target locs := by
  cases global : source.global with
  | none =>
    simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, global] at safe
  | some ref =>
    cases found : sptLookup ref source.refs with
    | none =>
      simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars,
        DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
        DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, global, found] at safe
    | some entry =>
      cases entry with
      | valueArray values =>
        by_cases bound : index < values.length
        · exact assignGlobal64 conf secn label l1 l2 source target locs related dest ref index values global found bound
        · have ge : values.length ≤ index := Nat.le_of_not_gt bound
          simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars,
            DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
            DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, global, found, List.getElem?_eq_none ge] at safe
      | byteArray flag bytes =>
        simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars,
          DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
          DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, global, found] at safe
      | thunk mode value =>
        simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars,
          DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
          DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, global, found] at safe
      | mutBlock tag finalised left value right =>
        simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars,
          DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
          DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, global, found] at safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
