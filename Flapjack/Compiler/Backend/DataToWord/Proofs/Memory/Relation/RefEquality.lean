import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv.Reference

/-! Equality of comparison references in the abstract heap invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Related pointer-comparison references have equal abstract roots exactly
when their source reference indices are equal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "ref_eq_thm"
  (words_as_type_indexed_bitvec)]
theorem refEqThm {width : Nat} [NeZero width] (conf : Config)
    (p1 p2 : Nat) (stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (r1 r2 : HeapAddress (WordLocW width)) (roots : List (HeapAddress (WordLocW width)))
    (heap : ValueHeap width) (bigEndian : Bool) (a sp sp1 : Nat) (gens : GenState) (limit next : Nat) :
    absMlInv conf (.refPtr true p1 :: .refPtr true p2 :: stack) refs
      (r1 :: r2 :: roots, heap, bigEndian, a, sp, sp1, gens) limit next →
    (p1 = p2 ↔ r1 = r2) ∧ ∃ q1 q2, r1 = .pointer q1 (.word 0) ∧ r2 = .pointer q2 (.word 0) := by
  intro inv
  obtain ⟨_, _, _, _, stackInv⟩ := inv
  obtain ⟨f, tf, inj, _, _, _, _, _, _, values, _⟩ := stackInv
  cases values with
  | cons v1 rest =>
    cases rest with
    | cons v2 _ =>
      obtain ⟨d1, _, _, pos1⟩ := (valueInv_refPtr_true conf p1 refs r1 f tf heap).mp v1
      obtain ⟨d2, _, _, pos2⟩ := (valueInv_refPtr_true conf p2 refs r2 f tf heap).mp v2
      subst r1
      subst r2
      constructor
      · constructor
        · intro equal
          subst p2
          rfl
        · intro equal
          apply inj.2 p1 p2 ⟨d1, d2⟩
          exact (HeapAddress.pointer.inj equal).1
      · exact ⟨holFapply f p1, holFapply f p2, rfl, rfl⟩

/-- A reference to a byte array has the same abstract address for either
comparison flag. This is Flapjack infrastructure for byte-array equality. -/
theorem valueInv_byteRefAddress {width : Nat} [NeZero width] (conf : Config) (bit : Bool) (index : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width)
    (compare : Bool) (bytes : List (BitVec 8))
    (found : sptLookup index refs = some (.byteArray compare bytes))
    (related : valueInv conf (.refPtr bit index) refs (address, f, tf, heap)) :
    address = .pointer (holFapply f index) (.word 0) := by
  rcases (valueInv_refPtr conf bit index refs address f tf heap).mp related with ordinary | thunk | inlined
  · simpa [found, refPtrAnnot] using ordinary.2.2.2
  · obtain ⟨_, _, _, thunkFound, _⟩ := thunk
    rw [found] at thunkFound
    cases thunkFound
  · obtain ⟨_, thunkFound, _⟩ := inlined
    rw [found] at thunkFound
    cases thunkFound

/-- Two references to the same byte array have equal target words. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_RefPtr_EQ_IMP"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_refPtrEqImp {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (b1 b2 : Bool) (index : Nat) (w1 w2 : BitVec width) (compare : Bool) (bytes : List (BitVec 8))
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain
      ((.refPtr b1 index, .word w1) :: (.refPtr b2 index, .word w2) :: vars) ∧
      goodDimindex width ∧ sptLookup index refs = some (.byteArray compare bytes) → w1 = w2 := by
  rintro ⟨⟨heap, limit, a, sp, sp1, gens, _, wordInv, _, _⟩, _, found⟩
  obtain ⟨roots, inv, addresses⟩ := wordInv
  obtain ⟨_, _, _, _, stackInv⟩ := inv
  obtain ⟨f, tf, _, _, _, _, _, _, _, values, _⟩ := stackInv
  cases roots with
  | nil => cases values
  | cons root1 rest =>
    cases rest with
    | nil => cases values with | cons _ tail => cases tail
    | cons root2 rest =>
      cases values with
      | cons first more =>
        cases more with
        | cons second _ =>
          cases addresses with
          | cons addr1 more =>
            cases more with
            | cons addr2 _ =>
              have eq1 := valueInv_byteRefAddress conf b1 index refs root1 f tf heap compare bytes found first
              have eq2 := valueInv_byteRefAddress conf b2 index refs root2 f tf heap compare bytes found second
              rw [eq1] at addr1
              rw [eq2] at addr2
              exact WordLocW.word.inj (addr1.symm.trans addr2)

/-- The natural value of a bounded shifted pointer with its marker bit set.
This is Flapjack bit-vector infrastructure for pointer injectivity. -/
theorem pointerEncoding_toNat {width : Nat} [NeZero width] (n k : Nat)
    (hk : 0 < k) (hn : n * 2 ^ k < 2 ^ width) :
    (((BitVec.ofNat width n <<< k) ||| 1).toNat) = n * 2 ^ k + 1 := by
  have hw : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  have powpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have nle : n ≤ n * 2 ^ k := Nat.le_mul_of_pos_right n powpos
  have nlt : n < 2 ^ width := Nat.lt_of_le_of_lt nle hn
  have kSmall : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt nlt, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hn]
  have one : (1 : BitVec width).toNat = 1 := by simp [BitVec.toNat_one hw]
  rw [one, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt kSmall n, Nat.shiftLeft_eq]

/-- The bounded pointer encoding is injective. This is Flapjack bit-vector
infrastructure for the original reference equality theorem. -/
theorem pointerEncoding_injective {width : Nat} [NeZero width] (n m k : Nat)
    (hn : n * 2 ^ k < 2 ^ width) (hm : m * 2 ^ k < 2 ^ width) (hk : 0 < k)
    (equal : ((BitVec.ofNat width n <<< k) ||| 1) = ((BitVec.ofNat width m <<< k) ||| 1)) : n = m := by
  have values := congrArg BitVec.toNat equal
  rw [pointerEncoding_toNat n k hk hn, pointerEncoding_toNat m k hk hm] at values
  apply Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos k)
  omega

/-- Two related comparison references have equal target words exactly when
their source reference indices are equal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_RefPtr_EQ"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_refPtrEq {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i1 i2 : Nat) (w1 w2 : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain
      ((.refPtr true i1, w1) :: (.refPtr true i2, w2) :: vars) ∧ goodDimindex width →
    ∃ v1 v2 : BitVec width, w1 = .word v1 ∧ w2 = .word v2 ∧ (v1 = v2 ↔ i1 = i2) := by
  rintro ⟨⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, _, _⟩, _⟩
  obtain ⟨roots, inv, addresses⟩ := wordInv
  obtain ⟨_, _, _, _, stackInv⟩ := inv
  obtain ⟨f, tf, inj, _, _, _, _, _, _, values, _⟩ := stackInv
  cases roots with
  | nil => cases values
  | cons root1 rest =>
    cases rest with
    | nil => cases values with | cons _ tail => cases tail
    | cons root2 rest =>
      cases values with
      | cons first more =>
        cases more with
        | cons second _ =>
          cases addresses with
          | cons addr1 more =>
            cases more with
            | cons addr2 _ =>
              obtain ⟨d1, _, _, pos1⟩ := (valueInv_refPtr_true conf i1 refs root1 f tf heap).mp first
              obtain ⟨d2, _, _, pos2⟩ := (valueInv_refPtr_true conf i2 refs root2 f tf heap).mp second
              subst root1
              subst root2
              let p1 := holFapply f i1
              let p2 := holFapply f i2
              have heapBound : heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf := heapMem.1
              have ptrBound : ∀ index, mapDomain f index → holFapply f index * 2 ^ shiftLength conf < 2 ^ width := by
                intro index indexDomain
                obtain ⟨xs, len, data, found⟩ := inj.1 index indexDomain
                have off : holFapply f index < heapLength heap := heapLookup_less heap _ _ found
                have below : holFapply f index < 2 ^ width / 2 ^ shiftLength conf := Nat.lt_of_lt_of_le off heapBound
                calc
                  holFapply f index * 2 ^ shiftLength conf < (2 ^ width / 2 ^ shiftLength conf) * 2 ^ shiftLength conf :=
                    Nat.mul_lt_mul_of_pos_right below (Nat.two_pow_pos _)
                  _ ≤ 2 ^ width := Nat.div_mul_le_self _ _
              have positive : 0 < shiftLength conf := by simp [shiftLength]
              refine ⟨getAddr conf p1 (.word 0), getAddr conf p2 (.word 0), addr1.symm, addr2.symm, ?_⟩
              constructor
              · intro equal
                apply inj.2 i1 i2 ⟨d1, d2⟩
                apply pointerEncoding_injective p1 p2 (shiftLength conf) (ptrBound i1 d1) (ptrBound i2 d2) positive
                simpa [getAddr, getLowerBits] using equal
              · intro equal
                subst i2
                rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
