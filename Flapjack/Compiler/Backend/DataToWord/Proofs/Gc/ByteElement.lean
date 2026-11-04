import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.ByteBounds
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteLoad

/-! Dynamic byte reads in the production-backed state relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- A related byte-array reference and in-range numeric index provide the
byte at the address computed by the generated load sequence. -/
theorem stateRel64_loadByteElement {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (base index ref n : Nat) (bit flag : Bool) (bytes : List (BitVec 8))
    (baseRun : DataSem.getVar base source.locals = some (.refPtr bit ref))
    (indexRun : DataSem.getVar index source.locals = some (.number (Int.ofNat n)))
    (found : sptLookup ref source.refs = some (.byteArray flag bytes)) (bound : n < bytes.length) :
    ∃ address : BitVec 64,
      WordSemStateFiniteExact.wordExp target
        (.op .add [realAddr conf (adjustVar base),
          .op .add [.const 8, shiftN .lsr (.var (adjustVar index)) 2]]) = some (.word address) ∧
      memLoadByteAuxExact target.memory target.mdomain target.be address = some bytes[n] := by
  obtain ⟨lengthBound, _⟩ := stateRel64_loadByteLength conf l1 l2 source target locs related
    base bit flag ref bytes baseRun found
  have small : smallInt 64 (Int.ofNat n) := by norm_num [smallInt]; omega
  have targetIndex := stateRel64_getSmallNumber conf l1 l2 source target locs related index _ indexRun small
  obtain ⟨location, wordRun⟩ := stateRel64_getVar conf l1 l2 source target none locs related base (.refPtr bit ref) baseRun
  have member := localPair_mem_joinEnv source.locals target.locals base (.refPtr bit ref) location baseRun wordRun
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
  obtain ⟨word, addr, encoding, _, real, _, _, _, _, _⟩ :=
    Memory.memoryRel_byteArrayHeader conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain bit flag ref bytes location roots focused found (Or.inr rfl)
  have targetBase : WordSemStateFiniteExact.getVar (adjustVar base) target = some (.word word) := by
    simpa [encoding] using wordRun
  have addrRun := wordExp_realAddr64 conf target (adjustVar base) word addr shiftBound targetBase real
  have focused' : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain ((.refPtr bit ref, .word word) :: roots) := by
    simpa [encoding] using focused
  have read := Memory.memoryRel_byteArrayLoad64 conf target.be (holThe source.tstamps) source.refs source.space
    target.store target.memory target.mdomain bit flag ref bytes word addr roots n focused' found real bound
  have encoding : (smallnum (Int.ofNat n) : BitVec 64) = BitVec.ofNat 64 (4 * n) := by simp [smallnum_eq_inlined]
  have nSmall : (BitVec.ofNat 64 n).ult 2305843009213693952 = true := by
    simp only [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat]
    have nBound : n < 2 ^ 64 := by norm_num; omega
    rw [Nat.mod_eq_of_lt nBound]
    change n < 2305843009213693952
    omega
  refine ⟨addr + 8 + BitVec.ofNat 64 n, ?_, read⟩
  change (smallnum (n : Int) : BitVec 64) = _ at encoding
  simp [WordSemStateFiniteExact.wordExp, addrRun, shiftN, targetIndex, wordShiftHOL,
    wordOpHOL, wordOp, theWords, BitVec.add_assoc]
  rw [encoding, BitVec.ofNat_mul]
  bv_decide

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
