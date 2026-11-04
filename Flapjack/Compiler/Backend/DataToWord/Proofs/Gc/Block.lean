import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.ReturnRoots
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockTests
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
import Mathlib.Tactic

/-! Constructor locals in the production-backed 64-bit relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Testing bit zero of a related block identifies precisely the nullary
constructor representation. -/
theorem stateRel64_getBlockEmpty {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (name stamp tag : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar name source.locals = some (.block stamp tag values)) :
    ∃ w : BitVec 64, WordSemStateFiniteExact.getVar (adjustVar name) target = some (.word w) ∧
      Compiler.Encoders.Asm.wordCmpHOL .test w 1 = decide (values.length = 0) := by
  obtain ⟨word, wordRun⟩ := stateRel64_getVar conf l1 l2 source target none locs related name (.block stamp tag values) sourceRun
  have member := localPair_mem_joinEnv source.locals target.locals name (.block stamp tag values) word sourceRun wordRun
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, memory⟩
  let roots := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
    [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
  have focused : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain ((.block stamp tag values, word) :: roots) := by
    apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain roots
    · intro pair present
      simp only [List.mem_cons] at present
      rcases present with rfl | tail
      · exact List.mem_append_left _ (List.mem_append_left _ member)
      · exact tail
    · simpa [roots] using memory
  obtain ⟨w, encoded, facts⟩ := Memory.memoryRel_blockImp conf target.be (holThe source.tstamps) source.refs source.space
    target.store target.memory target.mdomain stamp tag values word roots ⟨focused, Or.inr rfl⟩
  refine ⟨w, by simpa [encoded] using wordRun, ?_⟩
  by_cases empty : values = []
  · simp only [empty, ↓reduceIte] at facts
    simp only [empty, List.length_nil, decide_true]
    change (w &&& (1 : BitVec 64) == 0) = true
    have bit := facts.2.1
    bv_decide
  · simp only [empty, ↓reduceIte] at facts
    obtain ⟨_, _, bit, _⟩ := facts
    have lengthNe : values.length ≠ 0 := by simpa using empty
    simp only [lengthNe, decide_false]
    change (w &&& (1 : BitVec 64) == 0) = false
    bv_decide

/-- A related block has an in-range tag, and equality with an in-range
immediate encoding detects exactly a nullary block with that tag. -/
theorem stateRel64_getBlockTagEmpty {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (name stamp found tag : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar name source.locals = some (.block stamp found values)) :
    ∃ w : BitVec 64, WordSemStateFiniteExact.getVar (adjustVar name) target = some (.word w) ∧
      found < 2 ^ 64 / 16 ∧ (tag < 2 ^ 64 / 16 →
        (w = BitVec.ofNat 64 (16 * tag + 2) ↔ found = tag ∧ values = [])) := by
  obtain ⟨word, wordRun⟩ := stateRel64_getVar conf l1 l2 source target none locs related name (.block stamp found values) sourceRun
  have member := localPair_mem_joinEnv source.locals target.locals name (.block stamp found values) word sourceRun wordRun
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, memory⟩
  let roots := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
    [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
  have focused : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain ((.block stamp found values, word) :: roots) := by
    apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain roots
    · intro pair present
      simp only [List.mem_cons] at present
      rcases present with rfl | tail
      · exact List.mem_append_left _ (List.mem_append_left _ member)
      · exact tail
    · simpa [roots] using memory
  have foundBound := Memory.memoryRel_tagLimit conf target.be (holThe source.tstamps) source.refs source.space
    target.store target.memory target.mdomain stamp found values word roots ⟨focused, Or.inr rfl⟩
  obtain ⟨w, wordEq, _⟩ := Memory.memoryRel_blockImp conf target.be (holThe source.tstamps) source.refs source.space
    target.store target.memory target.mdomain stamp found values word roots ⟨focused, Or.inr rfl⟩
  refine ⟨w, by simpa [wordEq] using wordRun, foundBound, ?_⟩
  intro tagBound
  obtain ⟨w', equal, equivalence⟩ := Memory.memoryRel_testNilEq conf target.be (holThe source.tstamps) source.refs source.space
    target.store target.memory target.mdomain stamp found tag values word roots ⟨focused, tagBound, Or.inr rfl⟩
  have same : w' = w := by rw [wordEq] at equal; exact WordLocW.word.inj equal.symm
  simpa [same] using equivalence

/-- A related nonempty constructor has a readable concrete header whose
encoded length is the source field count. This lifts the memory relation to
the local-variable interface used by the compiled block operations. -/
theorem stateRel64_getBlockHeader {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (name stamp tag : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar name source.locals = some (.block stamp tag values))
    (nonempty : values ≠ []) :
    ∃ (word address header : BitVec 64),
      WordSemStateFiniteExact.getVar (adjustVar name) target = some (.word word) ∧
      word.getLsbD 0 = true ∧ Memory.getRealAddr conf target.store word = some address ∧
      target.memory address = .word header ∧ target.mdomain address = true ∧
      WordGcFunctions.decodeLength conf header = BitVec.ofNat 64 values.length ∧
      values.length < 2 ^ (64 - 4) := by
  obtain ⟨word, wordRun⟩ := stateRel64_getVar conf l1 l2 source target none locs related name (.block stamp tag values) sourceRun
  have member := localPair_mem_joinEnv source.locals target.locals name (.block stamp tag values) word sourceRun wordRun
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, memory⟩
  let roots := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
    [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
  have focused : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain ((.block stamp tag values, word) :: roots) := by
    apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain roots
    · intro pair present
      simp only [List.mem_cons] at present
      rcases present with rfl | tail
      · exact List.mem_append_left _ (List.mem_append_left _ member)
      · exact tail
    · simpa [roots] using memory
  obtain ⟨w, encoded, facts⟩ := Memory.memoryRel_blockImp conf target.be (holThe source.tstamps) source.refs source.space
    target.store target.memory target.mdomain stamp tag values word roots ⟨focused, Or.inr rfl⟩
  simp only [nonempty, ↓reduceIte] at facts
  obtain ⟨address, header, bit, _, _, real, mem, domain, decoded, bound, _, _⟩ := facts
  exact ⟨w, address, header, by simpa [encoded] using wordRun, bit, real, mem, domain, decoded, bound⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
