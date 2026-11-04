import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.BlockLength
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.NewLocal
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockStack
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.RefArrayElement

/-! Reading constructor fields through the candidate state relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- A valid source constructor field is available at the generated target
load address, and the resulting source/target pair extends the memory
relation. This is Lean-side simulation infrastructure. -/
theorem stateRel64_loadBlockElement {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (name stamp tag : Nat) (values : List DataSem.Value) (index : Nat)
    (sourceRun : DataSem.getVar name source.locals = some (.block stamp tag values))
    (bound : index < values.length) :
    ∃ child : WordLocW 64,
      WordSemStateFiniteExact.wordExp target
        (.load (.op .add [realAddr conf (adjustVar name),
          .const (BitVec.ofNat 64 8 + BitVec.ofNat 64 8 * BitVec.ofNat 64 index)])) = some child ∧
      Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
        target.store target.memory target.mdomain
        ((values[index], child) :: (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
          [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)) := by
  obtain ⟨word, wordRun⟩ := stateRel64_getVar conf l1 l2 source target none locs related name (.block stamp tag values) sourceRun
  have member := localPair_mem_joinEnv source.locals target.locals name (.block stamp tag values) word sourceRun wordRun
  have shiftBound : shiftLength conf < 64 := related.2.2.2.2.2.2.2.1
  have memory := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
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
  obtain ⟨w, addr, unused, encoded, real, domain, extended⟩ :=
    Memory.memoryRel_elAny conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain stamp tag values word roots index bound ⟨focused, Or.inr rfl⟩
  have targetRun : WordSemStateFiniteExact.getVar (adjustVar name) target = some (.word w) := by
    simpa [encoded] using wordRun
  have addrRun := wordExp_realAddr64 conf target (adjustVar name) w addr shiftBound targetRun real
  let child := target.memory (addr + StackRemove.bytesInWord 64 + StackRemove.bytesInWord 64 * BitVec.ofNat 64 index)
  refine ⟨child, ?_, ?_⟩
  · have domain' : target.mdomain (addr + (8 + 8 * BitVec.ofNat 64 index)) = true := by
      simpa [StackRemove.bytesInWord, BitVec.add_assoc] using domain
    simp [WordSemStateFiniteExact.wordExp, addrRun, wordOpHOL, wordOp, theWords,
      WordSemStateFiniteExact.memLoad, StackRemove.bytesInWord, child, BitVec.add_assoc]
    simpa using domain'
  · apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      ((values[index], child) :: (.block stamp tag values, word) :: roots)
    · intro pair present
      simp only [List.mem_cons] at present ⊢
      rcases present with same | old
      · exact Or.inl same
      · exact Or.inr (Or.inr old)
    · exact extended

/-- A valid source value-array field is available at the generated target
load address, and the resulting source/target pair extends the memory
relation. This is Lean-side simulation infrastructure. -/
theorem stateRel64_loadRefArrayElement {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (name : Nat) (bit : Bool) (ref : Nat) (values : List DataSem.Value) (index : Nat)
    (sourceRun : DataSem.getVar name source.locals = some (.refPtr bit ref))
    (bound : index < values.length)
    (found : sptLookup ref source.refs = some (.valueArray values)) :
    ∃ child : WordLocW 64,
      WordSemStateFiniteExact.wordExp target
        (.load (.op .add [realAddr conf (adjustVar name),
          .const (BitVec.ofNat 64 8 + BitVec.ofNat 64 8 * BitVec.ofNat 64 index)])) = some child ∧
      Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
        target.store target.memory target.mdomain
        ((values[index], child) :: (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
          [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)) := by
  obtain ⟨word, wordRun⟩ := stateRel64_getVar conf l1 l2 source target none locs related name (.refPtr bit ref) sourceRun
  have member := localPair_mem_joinEnv source.locals target.locals name (.refPtr bit ref) word sourceRun wordRun
  have shiftBound : shiftLength conf < 64 := related.2.2.2.2.2.2.2.1
  have memory := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  let roots := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
    [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
  have focused : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain ((.refPtr bit ref, word) :: roots) := by
    apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain roots
    · intro pair present
      simp only [List.mem_cons] at present
      rcases present with rfl | tail
      · exact List.mem_append_left _ (List.mem_append_left _ member)
      · exact tail
    · simpa [roots] using memory
  obtain ⟨w, addr, encoded, real, domain, extended⟩ :=
    Memory.memoryRel_refArrayElement conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain bit ref values word roots index bound found ⟨focused, Or.inr rfl⟩
  have targetRun : WordSemStateFiniteExact.getVar (adjustVar name) target = some (.word w) := by
    simpa [encoded] using wordRun
  have addrRun := wordExp_realAddr64 conf target (adjustVar name) w addr shiftBound targetRun real
  let child := target.memory (addr + StackRemove.bytesInWord 64 + StackRemove.bytesInWord 64 * BitVec.ofNat 64 index)
  refine ⟨child, ?_, ?_⟩
  · have domain' : target.mdomain (addr + (8 + 8 * BitVec.ofNat 64 index)) = true := by
      simpa [StackRemove.bytesInWord, BitVec.add_assoc] using domain
    simp [WordSemStateFiniteExact.wordExp, addrRun, wordOpHOL, wordOp, theWords,
      WordSemStateFiniteExact.memLoad, StackRemove.bytesInWord, child, BitVec.add_assoc]
    simpa using domain'
  · apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      ((values[index], child) :: (.refPtr bit ref, word) :: roots)
    · intro pair present
      simp only [List.mem_cons] at present ⊢
      rcases present with same | old
      · exact Or.inl same
      · exact Or.inr (Or.inr old)
    · exact extended

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
