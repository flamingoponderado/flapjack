import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.BlockLength
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Bounds64
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordEquality.ByteArray

/-! Byte-array lengths for the 64-bit bounds-check simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- The header shift used by the compiler recovers the byte count plus the
word-sized header. -/
theorem byteHeader_shift64 (conf : Config) (flag : Bool) (len : Nat)
    (configBound : conf.lenSize + 7 < 64)
    (bound : len + 8 < 2 ^ (conf.lenSize + 3)) :
    ((makeByteHeader conf flag len : BitVec 64) >>> (64 - conf.lenSize - 3)) = BitVec.ofNat 64 (len + 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
  by_cases low : i < conf.lenSize + 3
  · have pos : 64 - conf.lenSize - 3 + i = i + (64 - 3 - conf.lenSize) := by omega
    rw [pos]
    simpa using Memory.byteHeaderLengthBit conf flag len i (Or.inr rfl) configBound (by simpa using low)
  · have high : 64 ≤ 64 - conf.lenSize - 3 + i := by omega
    have pow : 2 ^ (conf.lenSize + 3) ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    have bit : (len + 8).testBit i = false := Nat.testBit_lt_two_pow (by omega)
    rw [BitVec.getLsbD_of_ge _ _ high, bit]

/-- A related byte-array local supplies the concrete header length used by
the generated bounds check. -/
theorem stateRel64_loadByteLength {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (name : Nat) (bit flag : Bool) (ref : Nat) (bytes : List (BitVec 8))
    (sourceRun : DataSem.getVar name source.locals = some (.refPtr bit ref))
    (found : sptLookup ref source.refs = some (.byteArray flag bytes)) :
    bytes.length < 2305843009213693952 ∧
      WordSemStateFiniteExact.wordExp target
        (.op .sub [shiftN .lsr (.load (realAddr conf (adjustVar name))) (64 - conf.lenSize - 3), .const 8]) =
        some (.word (BitVec.ofNat 64 bytes.length)) := by
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
  obtain ⟨word, addr, encoding, _, real, _, mem, domain, configBound, headerBound⟩ :=
    Memory.memoryRel_byteArrayHeader conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain bit flag ref bytes location roots focused found (Or.inr rfl)
  have targetRun : WordSemStateFiniteExact.getVar (adjustVar name) target = some (.word word) := by
    simpa [encoding] using wordRun
  have addrRun := wordExp_realAddr64 conf target (adjustVar name) word addr shiftBound targetRun real
  have load : WordSemStateFiniteExact.wordExp target (.load (realAddr conf (adjustVar name))) =
      some (.word (makeByteHeader conf flag bytes.length)) := by
    simp [WordSemStateFiniteExact.wordExp, addrRun, WordSemStateFiniteExact.memLoad, domain, mem]
  have headerBound' : bytes.length + 8 < 2 ^ (conf.lenSize + 3) := by simpa using headerBound
  have lenBits : conf.lenSize + 3 ≤ 61 := by omega
  have power : 2 ^ (conf.lenSize + 3) ≤ 2 ^ 61 := Nat.pow_le_pow_right (by decide) lenBits
  have byteBound : bytes.length < 2305843009213693952 := by norm_num at power; omega
  refine ⟨byteBound, ?_⟩
  have shiftNat : (BitVec.ofNat 64 (64 - conf.lenSize - 3)).toNat = 64 - conf.lenSize - 3 := by
    simp only [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    norm_num
    omega
  have notBig : ¬ 64 ≤ 64 - conf.lenSize - 3 := by omega
  simp [WordSemStateFiniteExact.wordExp, shiftN, load, wordShiftHOL, shiftNat, notBig,
    byteHeader_shift64 conf flag bytes.length configBound headerBound', wordOpHOL, wordOp, theWords,
    BitVec.ofNat_add]
  bv_decide


end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
