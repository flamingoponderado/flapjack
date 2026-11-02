import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.ReturnRoots
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockHeader
import Flapjack.Compiler.Backend.Semantics.DataSem.Control

/-! Boolean local values in the production-backed data-to-word relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- A source Boolean local is represented by its actual target immediate:
18 for true and 2 for false. -/
theorem stateRel64_getBool {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (name : Nat) (value : DataSem.Value) (b : Bool)
    (sourceRun : DataSem.getVar name source.locals = some value) (isBool : DataSem.isBool b value = true) :
    WordSemStateFiniteExact.getVar (adjustVar name) target = some (.word (if b then 18 else 2)) := by
  obtain ⟨word, wordRun⟩ := stateRel64_getVar conf l1 l2 source target none locs related name value sourceRun
  have member := localPair_mem_joinEnv source.locals target.locals name value word sourceRun wordRun
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, memory⟩
  let roots := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
    [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
  have focused : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain ((value, word) :: roots) := by
    apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain roots
    · intro pair present
      simp only [List.mem_cons] at present
      rcases present with rfl | tail
      · exact List.mem_append_left _ (List.mem_append_left _ member)
      · exact tail
    · simpa [roots] using memory
  cases value with
  | block stamp tag values =>
    cases values with
    | cons value values => simp [DataSem.isBool] at isBool
    | nil =>
      have tagEq' : BackendCommon.boolToTag b = tag := by simpa [DataSem.isBool] using isBool
      have tagEq := tagEq'.symm
      subst tag
      obtain ⟨w, eq, facts⟩ := Memory.memoryRel_blockImp conf target.be (holThe source.tstamps) source.refs source.space
        target.store target.memory target.mdomain stamp (BackendCommon.boolToTag b) [] word roots ⟨focused, Or.inr rfl⟩
      simp only [ite_true] at facts
      have encoded : word = .word (if b then 18 else 2) := by
        rw [eq, facts.1]
        cases b <;> decide
      simpa [encoded] using wordRun
  | number n => simp [DataSem.isBool] at isBool
  | word64 w => simp [DataSem.isBool] at isBool
  | codePtr n => simp [DataSem.isBool] at isBool
  | refPtr b n => simp [DataSem.isBool] at isBool

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
