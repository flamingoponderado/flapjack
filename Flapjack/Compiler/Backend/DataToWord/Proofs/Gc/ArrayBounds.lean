import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.BlockLength
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Bounds64
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ValueArray

/-! Value-array lengths in the 64-bit data-to-word simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- A related value-array reference supplies the count read by the generated
bounds-check code. -/
theorem stateRel64_loadArrayLength {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (name : Nat) (bit : Bool) (ref : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar name source.locals = some (.refPtr bit ref))
    (found : sptLookup ref source.refs = some (.valueArray values)) :
    values.length < 2305843009213693952 ∧
      WordSemStateFiniteExact.wordExp target
        (shiftN .lsr (.load (realAddr conf (adjustVar name))) (64 - conf.lenSize)) =
        some (.word (BitVec.ofNat 64 values.length)) := by
  obtain ⟨location, wordRun⟩ := stateRel64_getVar conf l1 l2 source target none locs related name (.refPtr bit ref) sourceRun
  have member := localPair_mem_joinEnv source.locals target.locals name (.refPtr bit ref) location sourceRun wordRun
  have shiftBound : shiftLength conf < 64 := related.2.2.2.2.2.2.2.1
  have memory := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  let roots := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
    [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
  have focused : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain ((.refPtr bit ref, location) :: roots) := by
    apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain roots
    · intro pair present
      simp only [List.mem_cons] at present
      rcases present with rfl | tail
      · exact List.mem_append_left _ (List.mem_append_left _ member)
      · exact tail
    · simpa [roots] using memory
  obtain ⟨word, addr, header, encoding, _, _, _, _, _, real, mem, domain, decoded, bound⟩ :=
    Memory.memoryRel_valueArrayImp conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain bit ref values location roots ⟨focused, found, Or.inr rfl⟩
  have targetRun : WordSemStateFiniteExact.getVar (adjustVar name) target = some (.word word) := by
    simpa [encoding] using wordRun
  have addrRun := wordExp_realAddr64 conf target (adjustVar name) word addr shiftBound targetRun real
  have load : WordSemStateFiniteExact.wordExp target (.load (realAddr conf (adjustVar name))) = some (.word header) := by
    simp [WordSemStateFiniteExact.wordExp, addrRun, WordSemStateFiniteExact.memLoad, domain, mem]
  have configBound : conf.lenSize ≠ 0 ∧ conf.lenSize + 7 < 64 := by
    obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, rest⟩ := memory
    exact ⟨heapMem.2.2.2.1, heapMem.2.2.2.2.1⟩
  have lengthBound : values.length < 2305843009213693952 := by norm_num at bound; omega
  refine ⟨lengthBound, ?_⟩
  have shiftNat : (BitVec.ofNat 64 (64 - conf.lenSize)).toNat = 64 - conf.lenSize := by
    simp only [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    norm_num
    omega
  have notBig : ¬ 64 ≤ 64 - conf.lenSize := by omega
  simp only [WordGcFunctions.decodeLength] at decoded
  simpa [shiftN, WordSemStateFiniteExact.wordExp, load, wordShiftHOL, shiftNat, notBig] using decoded

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
