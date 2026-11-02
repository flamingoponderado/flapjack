import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.ReturnRoots
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberCompare

/-! Immediate numeric locals in the production-backed state relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- A related small-number local has the 64-bit immediate representation. -/
theorem stateRel64_getSmallNumber {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (name : Nat) (i : Int) (sourceRun : DataSem.getVar name source.locals = some (.number i))
    (small : smallInt 64 i) :
    WordSemStateFiniteExact.getVar (adjustVar name) target = some (.word (smallnum i)) := by
  obtain ⟨word, wordRun⟩ := stateRel64_getVar conf l1 l2 source target none locs related name (.number i) sourceRun
  have member := localPair_mem_joinEnv source.locals target.locals name (.number i) word sourceRun wordRun
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, memory⟩
  let roots := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
    [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
  have focused : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain ((.number i, word) :: roots) := by
    apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain roots
    · intro pair present
      simp only [List.mem_cons] at present
      rcases present with rfl | tail
      · exact List.mem_append_left _ (List.mem_append_left _ member)
      · exact tail
    · simpa [roots] using memory
  have encoded := Memory.memoryRel_numberImp conf target.be (holThe source.tstamps) source.refs source.space
    target.store target.memory target.mdomain i word roots ⟨Or.inr rfl, small, focused⟩
  simpa [encoded] using wordRun

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
