module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteArray
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BytePacking
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteHeaderEquality

@[expose] public section

/-! String-constant comparisons in the data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataSem Flapjack.Basis.Pure.MlString
open Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- A related byte array satisfies the complete string-constant comparison. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_String_const_test"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_stringConstTest {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (bit : Bool) (index : Nat) (location : WordLocW width) (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (other : List (BitVec 8)) (text : MlString)
    (h : memoryRel conf be next refs space store memory domain ((.refPtr bit index, location) :: vars) ∧
      sptLookup index refs = some (.byteArray true other) ∧ goodDimindex width) :
    let target := MlString.implode other
    (Build.partWords (width := width) conf .ln (.str text) 0 = none → text ≠ target) ∧
    ∀ x res, Build.partWords (width := width) conf .ln (.str text) 0 = some (x,res) →
      ∃ w a, location = .word w ∧ getRealAddr conf store w = some a ∧
        wordMemEq a (res.map (fun x => Build.getWord x.2)) domain memory = some (decide (text = target)) := by
  obtain ⟨word, address, locEq, bitSet, addrEq, simpleEq, memHead, domHead, configBound, byteBound⟩ :=
    memoryRel_byteArrayHeader conf be next refs space store memory domain bit true index other location vars h.1 h.2.1 h.2.2
  have beEq : conf.be = be := by
    obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, _, _⟩ := h.1
    obtain ⟨roots, inv, addresses⟩ := wordInv
    obtain ⟨_, _, _, _, stackInv⟩ := inv
    obtain ⟨f, tf, _, _, _, _, _, same, _⟩ := stackInv
    exact same
  have lenBound : Build.byteLen width other.length < 2 ^ conf.lenSize := by
    rcases h.2.2 with hw | hw <;> subst width <;>
      simp only [Build.byteLen, ↓reduceIte] <;>
      simp only [↓reduceIte, pow_add] at byteBound <;> norm_num at byteBound ⊢ <;> omega
  have lenWide : Build.byteLen width other.length < 2 ^ (width - 4) := by
    have k : conf.lenSize ≤ width - 4 := by omega
    have power : 2 ^ conf.lenSize ≤ 2 ^ (width - 4) := Nat.pow_le_pow_right (by decide) k
    omega
  constructor
  · intro fails same
    subst text
    simp [Build.partWords, lenBound, lenWide] at fails
  · intro x res run
    have bounds : Build.byteLen width text.explode.length < 2 ^ (width - 4) ∧
        Build.byteLen width text.explode.length < 2 ^ conf.lenSize := by
      by_contra notBounds
      simp [Build.partWords, notBounds] at run
    have runFields : x = (true, Build.makePtr conf 0 (0 : BitVec width) (Build.byteLen width text.explode.length)) ∧
        res = ((makeByteHeader conf true text.explode.length ::
          writeBytes text.explode (List.replicate (Build.byteLen width text.explode.length) (0 : BitVec width)) conf.be).map
            (fun w => (false, WordLocW.word w))) := by
      simpa [Build.partWords, bounds] using run.symm
    obtain ⟨rfl, rfl⟩ := runFields
    refine ⟨word, address, locEq, addrEq, ?_⟩
    simp only [List.map_map, Function.comp_def, List.map_cons, Build.getWord]
    have memRel : memoryRel conf be next refs space store memory domain ((.refPtr bit index, .word word) :: vars) := by
      simpa [locEq] using h.1
    obtain ⟨header, frame, headEq, payload, _, countEq⟩ :=
      memoryRel_byteArrayWordsImp conf be next refs space store memory domain bit true index other word address vars
        ⟨memRel, h.2.1, h.2.2, addrEq⟩
    have headerEq : header = makeByteHeader conf true other.length := by
      exact WordLocW.word.inj (headEq.symm.trans memHead)
    subst header
    rw [countEq] at payload
    have countEq2 : other.length / (width / 8) + 1 = Build.byteLen width other.length := by
      rcases h.2.2 with hw | hw <;> subst width <;> rfl
    rw [countEq2] at payload
    rw [← beEq] at payload
    simp only [wordMemEq, domHead, ↓reduceIte, memHead]
    have shiftBound : 2 < width - (if width = 32 then 2 else 3) - conf.lenSize := by
      rcases h.2.2 with hw | hw <;> subst width <;> simp_all <;> omega
    have headerIff := makeByteHeader_eq conf other.length text.explode.length
      ⟨lenBound, lenWide, bounds.2, bounds.1, h.2.2, shiftBound⟩
    by_cases sameLength : other.length = text.explode.length
    · have sameHeader := headerIff.mpr sameLength
      simp only [sameHeader, if_true]
      have counts : Build.byteLen width other.length = Build.byteLen width text.explode.length := by
        rw [sameLength]
      have packedLengths :
          (writeBytes other (List.replicate (Build.byteLen width other.length) (0 : BitVec width)) conf.be).length =
          (writeBytes text.explode (List.replicate (Build.byteLen width text.explode.length) (0 : BitVec width)) conf.be).length := by
        simp [writeBytes_wordCount, counts]
      have packed := wordMemEqThm
        (writeBytes other (List.replicate (Build.byteLen width other.length) (0 : BitVec width)) conf.be)
        (writeBytes text.explode (List.replicate (Build.byteLen width text.explode.length) (0 : BitVec width)) conf.be)
        (address + StackRemove.bytesInWord width) frame memory domain ⟨payload, packedLengths⟩
      have capacity : other.length ≤ (List.replicate (Build.byteLen width other.length) (0 : BitVec width)).length * (width / 8) := by
        rcases h.2.2 with hw | hw <;> subst width <;> simp [Build.byteLen] <;> omega
      have countBound : (List.replicate (Build.byteLen width other.length) (0 : BitVec width)).length ≤
          other.length / (width / 8) + 1 := by
        simp [← countEq2]
      have inj := writeBytesInj conf.be h.2.2
        (List.replicate (Build.byteLen width other.length) (0 : BitVec width)) other text.explode
        ⟨sameLength, capacity, countBound⟩
      have textEq : (other = text.explode) ↔ text = MlString.implode other := by
        cases text; simp [MlString.explode, eq_comm]
      rw [← counts] at packed
      have iff : (writeBytes other (List.replicate (Build.byteLen width other.length) (0 : BitVec width)) conf.be =
          writeBytes text.explode (List.replicate (Build.byteLen width other.length) (0 : BitVec width)) conf.be) ↔
          text = MlString.implode other := inj.trans textEq
      have boolEq : decide (writeBytes other (List.replicate (Build.byteLen width other.length) (0 : BitVec width)) conf.be =
          writeBytes text.explode (List.replicate (Build.byteLen width other.length) (0 : BitVec width)) conf.be) =
          decide (text = MlString.implode other) := decide_eq_decide.mpr iff
      rw [boolEq] at packed
      simpa [counts] using packed
    · have notHead : makeByteHeader (width := width) conf true other.length ≠
          makeByteHeader conf true text.explode.length := fun eq => sameLength (headerIff.mp eq)
      have diff : text ≠ MlString.implode other := by
        intro eq
        subst text
        exact sameLength rfl
      simp [notHead, diff]
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
