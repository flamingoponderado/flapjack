import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.BlockElement

/-! Global-variable reads through the cached globals base. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- A valid global variable is loaded through the actual cached globals
address, and the loaded value can be added to the related roots. -/
theorem stateRel64_loadGlobal {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (ref index : Nat) (values : List DataSem.Value)
    (global : source.global = some ref) (found : sptLookup ref source.refs = some (.valueArray values))
    (bound : index < values.length) :
    ∃ word,
      WordSemStateFiniteExact.wordExp target
        (.load (.op .add [.lookup .globReal, .const (8 * BitVec.ofNat 64 (index + 1))])) = some word ∧
      Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
        target.store target.memory target.mdomain
        ((values[index], word) :: joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
          [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack) := by
  have memory := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  let roots := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
    [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
  have memoryCopy := memory
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, _, _, _⟩ := memoryCopy
  obtain ⟨_, _, _, _, _, _, _, curr, _, _, _, currStore, _, _, _, _, _, globInv, _, _⟩ := heapMem
  obtain ⟨globalWord, globalsLookup, globalReal⟩ := globInv
  have member : (DataSem.Value.refPtr true ref, .word globalWord) ∈ roots := by
    simp [roots, theGlobal, global, holFapply_of_lookup globalsLookup]
  have focused : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain ((.refPtr true ref, .word globalWord) :: roots) := by
    apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain roots
    · intro pair present
      simp only [List.mem_cons] at present
      rcases present with rfl | tail
      · exact member
      · exact tail
    · simpa [roots] using memory
  obtain ⟨encoded, addr, encodedEq, _, simpleEq, inDomain, extended⟩ :=
    Memory.memoryRel_refArrayElement conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain true ref values (.word globalWord) roots index bound found ⟨focused, Or.inr rfl⟩
  have wordEq : encoded = globalWord := WordLocW.word.inj encodedEq.symm
  subst encoded
  have addrEq : addr = curr + ((globalWord >>> shiftLength conf) <<< wordShiftAmount 64) := by
    simpa [Memory.getRealSimpleAddr, currStore] using simpleEq.symm
  subst addr
  let address := curr + ((globalWord >>> shiftLength conf) <<< wordShiftAmount 64) + 8 + 8 * BitVec.ofNat 64 index
  refine ⟨target.memory address, ?_, ?_⟩
  · have inDomain' : target.mdomain address = true := by
      simpa [address, StackRemove.bytesInWord] using inDomain
    have offset : (8 : BitVec 64) * BitVec.ofNat 64 (index + 1) = 8 + 8 * BitVec.ofNat 64 index := by
      simp [BitVec.ofNat_add, BitVec.mul_add, BitVec.add_comm]
    rw [offset]
    simpa [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore, globalReal, wordOpHOL,
      wordOp, theWords, WordSemStateFiniteExact.memLoad, address, BitVec.add_assoc] using inDomain'
  · have reduced : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
        target.store target.memory target.mdomain ((values[index], target.memory address) :: roots) := by
      apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
        target.store target.memory target.mdomain
        ((values[index], target.memory address) :: (.refPtr true ref, .word globalWord) :: roots)
      · intro pair present
        simp only [List.mem_cons] at present ⊢
        rcases present with rfl | tail
        · exact Or.inl rfl
        · exact Or.inr (Or.inr tail)
      · simpa [address, StackRemove.bytesInWord] using extended
    simpa [roots] using reduced

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
