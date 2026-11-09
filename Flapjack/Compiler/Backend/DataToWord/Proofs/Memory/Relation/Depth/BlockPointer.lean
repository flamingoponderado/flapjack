module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockEquality
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.RefEquality

@[expose] public section

/-! Uniqueness of source blocks sharing a target word. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem
open Classical
noncomputable section

/-- Bounded pointer encodings retain their heap index regardless of the low
    annotation bits. This is Flapjack bit-vector infrastructure. -/
private theorem getAddr_index_injective {width : Nat} [NeZero width] (conf : DataToWord.Config)
    (i j : Nat) (x y : WordLocW width)
    (boundI : i * 2 ^ shiftLength conf < 2 ^ width) (boundJ : j * 2 ^ shiftLength conf < 2 ^ width)
    (same : getAddr conf i x = getAddr conf j y) : i = j := by
  have shifted := congrArg (fun w : BitVec width => w >>> shiftLength conf) same
  simp only [getAddr, BitVec.ushiftRight_or_distrib, getLowerBits_shiftLength,
    bounded_shift_roundtrip i (shiftLength conf) boundI,
    bounded_shift_roundtrip j (shiftLength conf) boundJ] at shifted
  have factor : 0 < 2 ^ shiftLength conf := Nat.two_pow_pos _
  have iSmall : i < 2 ^ width := by
    have h := Nat.le_mul_of_pos_right i factor
    omega
  have jSmall : j < 2 ^ width := by
    have h := Nat.le_mul_of_pos_right j factor
    omega
  have values := congrArg BitVec.toNat shifted
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt iSmall, Nat.mod_eq_of_lt jSmall] using values

/-- Related source blocks sharing a target location are identical. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Block_ptr_eq"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_blockPtrEq {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (stamp1 tag1 stamp2 tag2 : Nat) (xs ys : List Value) (location : WordLocW width)
    (vars : List (Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain
      ((.block stamp1 tag1 xs, location) :: (.block stamp2 tag2 ys, location) :: vars) ∧
      goodDimindex width → Value.block stamp1 tag1 xs = Value.block stamp2 tag2 ys := by
  rintro ⟨rel, good⟩
  obtain ⟨w, loc, _⟩ := memoryRel_blockImp conf be next refs space store memory domain
    stamp1 tag1 xs location ((.block stamp2 tag2 ys, location) :: vars) ⟨rel, good⟩
  subst location
  obtain ⟨tags, lengths⟩ := memoryRel_blocksSameWord conf be next refs space store memory domain
    stamp1 tag1 stamp2 tag2 xs ys w vars rel good
  by_cases empty1 : xs = []
  · have empty2 : ys = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa [empty1] using lengths.symm
    obtain ⟨p1, e1, c1⟩ := memoryRel_blockImp conf be next refs space store memory domain
      stamp1 tag1 xs (.word w) ((.block stamp2 tag2 ys, .word w) :: vars) ⟨rel, good⟩
    have tail := memoryRel_tail conf be next refs space store memory domain (.block stamp1 tag1 xs, .word w)
      ((.block stamp2 tag2 ys, .word w) :: vars) rel
    obtain ⟨p2, e2, c2⟩ := memoryRel_blockImp conf be next refs space store memory domain
      stamp2 tag2 ys (.word w) vars ⟨tail, good⟩
    simp only [empty1, ↓reduceIte] at c1
    simp only [empty2, ↓reduceIte] at c2
    simp [empty1, empty2, tags, c1.2.2.2, c2.2.2.2]
  · have nonempty2 : ys ≠ [] := by
      intro empty
      have zero : xs.length = 0 := by simpa [empty] using lengths
      exact empty1 (List.eq_nil_of_length_eq_zero zero)
    obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, _, _⟩ := rel
    obtain ⟨roots, inv, addresses⟩ := wordInv
    obtain ⟨_, _, _, _, stackInv⟩ := inv
    obtain ⟨f, tf, _, _, tfInj, _, _, _, unique, values, _⟩ := stackInv
    have ptrBound : ∀ ptr element, heapLookup ptr heap = some element →
        ptr * 2 ^ shiftLength conf < 2 ^ width := by
      intro ptr element found
      have below : ptr < 2 ^ width / 2 ^ shiftLength conf :=
        Nat.lt_of_lt_of_le (heapLookup_less heap ptr element found) heapMem.1
      calc
        ptr * 2 ^ shiftLength conf < (2 ^ width / 2 ^ shiftLength conf) * 2 ^ shiftLength conf :=
          Nat.mul_lt_mul_of_pos_right below (Nat.two_pow_pos _)
        _ ≤ 2 ^ width := Nat.div_mul_le_self _ _
    cases roots with
    | nil => cases values
    | cons root1 rest =>
      cases rest with
      | nil => cases values with | cons _ more => cases more
      | cons root2 rest =>
        cases values with
        | cons value1 more =>
          cases more with
          | cons value2 _ =>
            cases addresses with
            | cons address1 more =>
              cases more with
              | cons address2 _ =>
                obtain ⟨ptr1, children1, _, map1, rootEq1, cell1⟩ :=
                  (valueInv_nonemptyBlock conf stamp1 tag1 xs refs root1 f tf heap empty1).mp value1
                obtain ⟨ptr2, children2, _, map2, rootEq2, cell2⟩ :=
                  (valueInv_nonemptyBlock conf stamp2 tag2 ys refs root2 f tf heap nonempty2).mp value2
                rw [rootEq1] at address1
                rw [rootEq2] at address2
                have encoded := WordLocW.word.inj (address1.trans address2.symm)
                have ptrEq : ptr1 = ptr2 := getAddr_index_injective conf ptr1 ptr2 _ _
                  (ptrBound ptr1 _ cell1) (ptrBound ptr2 _ cell2) encoded
                have stampEq : stamp1 = stamp2 := by
                  apply tfInj.2 stamp1 stamp2 ⟨⟨ptr1, map1⟩, ⟨ptr2, map2⟩⟩
                  rw [holFapply_of_lookup map1, holFapply_of_lookup map2, ptrEq]
                subst stamp2
                have member1 : allValues refs ((.block stamp1 tag1 xs) :: (.block stamp1 tag2 ys) :: vars.map Prod.fst)
                    (.block stamp1 tag1 xs) := by simp [allValues, valueListValues]
                have member2 : allValues refs ((.block stamp1 tag1 xs) :: (.block stamp1 tag2 ys) :: vars.map Prod.fst)
                    (.block stamp1 tag2 ys) := by simp [allValues, valueListValues]
                have same := unique stamp1 tag1 xs tag2 ys ⟨member1, empty1, member2, nonempty2⟩
                simp [same.1, same.2.1]

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
