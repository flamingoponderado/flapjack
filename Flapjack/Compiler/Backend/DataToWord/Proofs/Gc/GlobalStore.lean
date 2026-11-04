import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GlobalLoad
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ArrayStore

/-! Global-variable stores through the cached globals base. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- A valid global update uses the cached globals base and preserves the
state relation after writing the corresponding target word. -/
theorem stateRel64_storeGlobal {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (ref index value : Nat) (values : List DataSem.Value) (item : DataSem.Value)
    (global : source.global = some ref) (found : sptLookup ref source.refs = some (.valueArray values))
    (bound : index < values.length) (valueRun : DataSem.getVar value source.locals = some item) :
    ∃ address word,
      WordSemStateFiniteExact.wordExp target
        (.op .add [.lookup .globReal, .const (8 * BitVec.ofNat 64 (index + 1))]) = some (.word address) ∧
      WordSemStateFiniteExact.getVar (adjustVar value) target = some word ∧ target.mdomain address = true ∧
      stateRel64 conf l1 l2 { source with refs := sptInsert ref (.valueArray (values.set index item)) source.refs }
        { target with memory := fun key => if key = address then word else target.memory key } none locs := by
  obtain ⟨itemWord, itemRun⟩ := stateRel64_getVar conf l1 l2 source target none locs related value item valueRun
  have valueMember := localPair_mem_joinEnv source.locals target.locals value item itemWord valueRun itemRun
  have memory := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  let roots := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
    [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
  have memoryCopy := memory
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, _, _, _⟩ := memoryCopy
  obtain ⟨_, _, _, _, _, _, _, curr, _, _, _, currStore, _, _, _, _, _, globInv, _, _⟩ := heapMem
  obtain ⟨globalWord, globalsLookup, globalReal⟩ := globInv
  have globalMember : (DataSem.Value.refPtr true ref, .word globalWord) ∈ roots := by
    simp [roots, theGlobal, global, holFapply_of_lookup globalsLookup]
  have focused : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain ((item, itemWord) :: (.refPtr true ref, .word globalWord) :: roots) := by
    apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain roots
    · intro pair present
      simp only [List.mem_cons] at present
      rcases present with rfl | rfl | tail
      · exact List.mem_append_left _ (List.mem_append_left _ valueMember)
      · exact globalMember
      · exact tail
    · simpa [roots] using memory
  obtain ⟨encoded, addr, encodedEq, _, simpleEq, inDomain, updated⟩ :=
    Memory.memoryRel_refStore conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain item itemWord true ref (.word globalWord) roots values index
      found bound (Or.inr rfl) focused
  have wordEq : encoded = globalWord := WordLocW.word.inj encodedEq.symm
  subst encoded
  have addrEq : addr = curr + ((globalWord >>> shiftLength conf) <<< wordShiftAmount 64) := by
    simpa [Memory.getRealSimpleAddr, currStore] using simpleEq.symm
  subst addr
  let address := curr + ((globalWord >>> shiftLength conf) <<< wordShiftAmount 64) + 8 + BitVec.ofNat 64 index * 8
  refine ⟨address, itemWord, ?_, itemRun, ?_, ?_⟩
  · have offset : (8 : BitVec 64) * BitVec.ofNat 64 (index + 1) = 8 + BitVec.ofNat 64 index * 8 := by
      simp [BitVec.ofNat_add, BitVec.mul_add, BitVec.add_comm, BitVec.mul_comm]
    rw [offset]
    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore, globalReal, wordOpHOL,
      wordOp, theWords, address, BitVec.add_assoc]
  · simpa [address, StackRemove.bytesInWord] using inDomain
  · have memoryNew : Memory.memoryRel conf target.be (holThe source.tstamps)
        (sptInsert ref (.valueArray (values.set index item)) source.refs) source.space
        target.store (fun key => if key = address then itemWord else target.memory key) target.mdomain roots := by
      apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps)
        (sptInsert ref (.valueArray (values.set index item)) source.refs) source.space target.store _ target.mdomain
        ((item, itemWord) :: (.refPtr true ref, .word globalWord) :: roots)
      · intro pair present
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ present)
      · exact updated
    rcases related with ⟨ffi, clock, handler, gc, code, oracle, good, shift, stamps, globals, zero,
      names, stackRel, locRel, stackBound, stackMax, stackSize, localsSize, limits, _⟩
    exact ⟨ffi, clock, handler, gc, code, oracle, good, shift, stamps, globals, zero,
      names, stackRel, locRel, stackBound, stackMax, stackSize, localsSize, limits, by simpa [roots] using memoryNew⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
