import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.ArrayBounds
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ArrayStore

/-! Value-array stores in the production-backed state relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- The generated array-store address is in the memory domain and the actual
word update preserves the state relation for the source reference update. -/
theorem stateRel64_storeArrayElement {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (base index value ref n : Nat) (bit : Bool) (old : List DataSem.Value) (item : DataSem.Value)
    (baseRun : DataSem.getVar base source.locals = some (.refPtr bit ref))
    (indexRun : DataSem.getVar index source.locals = some (.number (Int.ofNat n)))
    (valueRun : DataSem.getVar value source.locals = some item)
    (found : sptLookup ref source.refs = some (.valueArray old)) (bound : n < old.length) :
    ∃ address word,
      WordSemStateFiniteExact.wordExp target
        (.op .add [realAddr conf (adjustVar base),
          .op .add [.const 8, .shift .lsl (.var (adjustVar index)) (.const 1)]]) = some (.word address) ∧
      WordSemStateFiniteExact.getVar (adjustVar value) target = some word ∧ target.mdomain address = true ∧
      stateRel64 conf l1 l2 { source with refs := sptInsert ref (.valueArray (old.set n item)) source.refs }
        { target with memory := fun key => if key = address then word else target.memory key } none locs := by
  obtain ⟨lengthBound, _⟩ := stateRel64_loadArrayLength conf l1 l2 source target locs related base bit ref old baseRun found
  have small : smallInt 64 (Int.ofNat n) := by norm_num [smallInt]; omega
  have targetIndex := stateRel64_getSmallNumber conf l1 l2 source target locs related index _ indexRun small
  obtain ⟨location, wordRun⟩ := stateRel64_getVar conf l1 l2 source target none locs related base (.refPtr bit ref) baseRun
  obtain ⟨itemWord, itemRun⟩ := stateRel64_getVar conf l1 l2 source target none locs related value item valueRun
  have baseMember := localPair_mem_joinEnv source.locals target.locals base (.refPtr bit ref) location baseRun wordRun
  have valueMember := localPair_mem_joinEnv source.locals target.locals value item itemWord valueRun itemRun
  have shiftBound : shiftLength conf < 64 := related.2.2.2.2.2.2.2.1
  have memory := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  let roots := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
    [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
  have focused : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain ((item, itemWord) :: (.refPtr bit ref, location) :: roots) := by
    apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain roots
    · intro pair present
      simp only [List.mem_cons] at present
      rcases present with rfl | rfl | tail
      · exact List.mem_append_left _ (List.mem_append_left _ valueMember)
      · exact List.mem_append_left _ (List.mem_append_left _ baseMember)
      · exact tail
    · simpa [roots] using memory
  obtain ⟨pointerWord, addr, encoding, real, inDomain, result⟩ :=
    Memory.memoryRel_refStore conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain item itemWord bit ref location roots old n found bound (Or.inr rfl) focused
  have targetBase : WordSemStateFiniteExact.getVar (adjustVar base) target = some (.word pointerWord) := by
    simpa [encoding] using wordRun
  have addrRun := wordExp_realAddr64 conf target (adjustVar base) pointerWord addr shiftBound targetBase real
  have encodingIndex : (smallnum (Int.ofNat n) : BitVec 64) = BitVec.ofNat 64 (4 * n) := by simp [smallnum_eq_inlined]
  let address := addr + 8 + BitVec.ofNat 64 n * 8
  refine ⟨address, itemWord, ?_, itemRun, ?_, ?_⟩
  · change (smallnum (n : Int) : BitVec 64) = _ at encodingIndex
    simp [WordSemStateFiniteExact.wordExp, addrRun, targetIndex, wordShiftHOL, wordOpHOL, wordOp, theWords, address]
    rw [encodingIndex, BitVec.ofNat_mul]
    bv_decide
  · simpa [address, StackRemove.bytesInWord] using inDomain
  · have memoryNew : Memory.memoryRel conf target.be (holThe source.tstamps)
        (sptInsert ref (.valueArray (old.set n item)) source.refs) source.space
        target.store (fun key => if key = address then itemWord else target.memory key) target.mdomain roots := by
      apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps)
        (sptInsert ref (.valueArray (old.set n item)) source.refs) source.space
        (target.store) _ target.mdomain ((item, itemWord) :: (.refPtr bit ref, location) :: roots)
      · intro pair present
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ present)
      · exact result
    rcases related with ⟨ffi, clock, handler, gc, code, oracle, good, shift, stamps, globals, zero,
      names, stackRel, locRel, stackBound, stackMax, stackSize, localsSize, limits, _⟩
    exact ⟨ffi, clock, handler, gc, code, oracle, good, shift, stamps, globals, zero,
      names, stackRel, locRel, stackBound, stackMax, stackSize, localsSize, limits, by simpa [roots] using memoryNew⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
