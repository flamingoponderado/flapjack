import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Number
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Bounds64

/-! Numeric bounds checks in the production-backed state relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Every related numeric local has a word whose rotated unsigned comparison
agrees with the source bounds check, including heap-backed integers. -/
theorem stateRel64_getNumberBounds {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (name : Nat) (i : Int) (sourceRun : DataSem.getVar name source.locals = some (.number i))
    (n : Nat) (bound : n < 2305843009213693952) :
    ∃ word : BitVec 64, WordSemStateFiniteExact.getVar (adjustVar name) target = some (.word word) ∧
      ((word.rotateRight 2).toNat < n ↔ 0 ≤ i ∧ i < (n : Int)) := by
  obtain ⟨location, wordRun⟩ := stateRel64_getVar conf l1 l2 source target none locs related name (.number i) sourceRun
  have member := localPair_mem_joinEnv source.locals target.locals name (.number i) location sourceRun wordRun
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, memory⟩
  let roots := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
    [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
  have focused : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain ((.number i, location) :: roots) := by
    apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain roots
    · intro pair present
      simp only [List.mem_cons] at present
      rcases present with rfl | tail
      · exact List.mem_append_left _ (List.mem_append_left _ member)
      · exact tail
    · simpa [roots] using memory
  obtain ⟨word, encoding, _⟩ := Memory.memoryRel_anyNumberImp conf target.be (holThe source.tstamps)
    source.refs source.space target.store target.memory target.mdomain i location roots ⟨Or.inr rfl, focused⟩
  refine ⟨word, ?_, ?_⟩
  · simpa [encoding] using wordRun
  · apply Memory.memoryRel_numberBounds64 conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain i word roots n
    · simpa [encoding] using focused
    · exact bound

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
