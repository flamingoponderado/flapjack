import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockHeader
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Number
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordMemoryEquality

/-! Header extraction for heap-allocated integers. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem
open Classical
noncomputable section

/-- Header bits identify a bignum and encode its sign. This is Flapjack
    bit-vector infrastructure for the bignum comparison proof. -/
theorem bignumHeaderBits {width : Nat} [NeZero width] (conf : Config) (value : Int) (len : Nat)
    (good : goodDimindex width) (configBound : conf.lenSize + 7 < width) :
    let tag : BitVec width := ((if value < 0 then 1 else 0) <<< 2) ||| 3
    let header := makeHeader conf tag len
    header.getLsbD 2 = true ∧ header.getLsbD 3 = true ∧ (header.getLsbD 4 = true ↔ value < 0) := by
  have h4 : ¬ (4 : Nat) ≥ width - conf.lenSize := by omega
  rcases good with hw | hw <;> subst width <;>
    by_cases sign : value < 0 <;> simp [makeHeader, h4, sign]

/-- Rearrange a separated cell and preserve all other heap assertions. -/
private theorem bignumExtractStar {α : Type} (p q r s t f : (α → Prop) → Prop) :
    SetSep.star (SetSep.star p (SetSep.star (SetSep.star (SetSep.star q r) s) t)) f =
      SetSep.star q (SetSep.star r (SetSep.star p (SetSep.star s (SetSep.star t f)))) := by
  have : Std.Associative (SetSep.star (α := α)) := ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩
  have : Std.Commutative (SetSep.star (α := α)) := ⟨SetSep.starComm⟩
  ac_rfl

/-- Extract a bignum header, digits, and complete frame from the word heap. -/
private theorem bignumHeap {width : Nat} [NeZero width] (conf : Config)
    (heap : ValueHeap width) (index : Nat) (value : Int) (curr : BitVec width)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (whole : (BitVec width × WordLocW width) → Prop)
    (found : heapLookup index heap = some (bignumRep value))
    (assertion : SetSep.star (wordHeap curr heap conf) frame whole) :
    let digits : List (BitVec width) := Misc.Multiword.n2mw value.natAbs
    let tag : BitVec width := ((if value < 0 then 1 else 0) <<< 2) ||| 3
    ∃ rest, SetSep.star
      (SetSep.one (curr + StackRemove.bytesInWord width * BitVec.ofNat width index,
        WordLocW.word (makeHeader conf tag digits.length)))
      (SetSep.star (Misc.wordList (curr + StackRemove.bytesInWord width * BitVec.ofNat width index +
        StackRemove.bytesInWord width) (digits.map WordLocW.word)) rest) whole ∧
      digits.length < 2 ^ (width - 4) ∧
      WordGcFunctions.decodeLength conf (makeHeader conf tag digits.length) = BitVec.ofNat width digits.length := by
  obtain ⟨before, after, heapEq, indexEq⟩ := heapLookup_split heap index (bignumRep value) found
  subst heap
  subst index
  rw [wordHeapAppend] at assertion
  simp only [wordHeap, wordEl, bignumRep, Misc.Multiword.i2mw, wordPayload, List.isEmpty_nil,
    Bool.true_and, List.length_map, decide_true, Bool.and_true, decide_eq_true_eq, Misc.wordList] at assertion
  have facts := assertion
  obtain ⟨_, _, _, ⟨_, _, _, _, ⟨_, _, _, ⟨_, _, _, _, pure⟩, _⟩⟩, _⟩ := facts
  have bounds := pure.2
  rw [bignumExtractStar] at assertion
  exact ⟨_, assertion, bounds.1, bounds.2.1⟩

/-- A bignum cell contributes its header and validity check to a word heap.
    This is Flapjack separation infrastructure. -/
private theorem wordHeap_bignumHeader {width : Nat} [NeZero width] (conf : Config)
    (heap : ValueHeap width) (index : Nat) (value : Int) (curr : BitVec width)
    (whole : (BitVec width × WordLocW width) → Prop)
    (found : heapLookup index heap = some (bignumRep value))
    (assertion : wordHeap curr heap conf whole) :
    let digits : List (BitVec width) := Misc.Multiword.n2mw value.natAbs
    let tag : BitVec width := ((if value < 0 then 1 else 0) <<< 2) ||| 3
    let header := makeHeader conf tag digits.length
    whole (curr + StackRemove.bytesInWord width * BitVec.ofNat width index, .word header) ∧
      (encodeHeader (width := width) conf tag.toNat digits.length).isSome := by
  obtain ⟨before, after, heapEq, indexEq⟩ := heapLookup_split heap index (bignumRep value) found
  subst heap
  subst index
  rw [wordHeapAppend] at assertion
  obtain ⟨prefixHeap, rest, split1, _, restAssertion⟩ := assertion
  change SetSep.star (wordEl _ (bignumRep value) conf) (wordHeap _ after conf) rest at restAssertion
  obtain ⟨element, suffix, split2, elementAssertion, _⟩ := restAssertion
  simp only [bignumRep, Misc.Multiword.i2mw, wordEl, wordPayload, List.isEmpty_nil,
    List.length_map, Bool.true_and, decide_true, Bool.and_true, decide_eq_true_eq] at elementAssertion
  obtain ⟨listHeap, pureHeap, split3, listAssertion, pureAssertion⟩ := elementAssertion
  obtain ⟨singleton, tailHeap, split4, singletonAssertion, _⟩ := listAssertion
  constructor
  · have member : singleton (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength before),
        .word (makeHeader conf (((if value < 0 then 1 else 0) <<< 2) ||| 3)
          (Misc.Multiword.n2mw (width := width) value.natAbs).length)) := by
      change singleton = (fun entry => entry = _) at singletonAssertion
      rw [singletonAssertion]
    have e := (iff_of_eq (congrFun split4.1 _)).mp (Or.inl member)
    have e := (iff_of_eq (congrFun split3.1 _)).mp (Or.inl e)
    have e := (iff_of_eq (congrFun split2.1 _)).mp (Or.inl e)
    exact (iff_of_eq (congrFun split1.1 _)).mp (Or.inr e)
  · exact pureAssertion.2.2.2

/-- The concrete header of a related bignum is valid and can be read at its
    decoded address. This is a useful consequence of the HOL theorem
    `memory_rel_Number_bignum_header`, but is not tagged as that theorem: the
    HOL statement also existentially quantifies three unused values over
    independent inhabited HOL types, whereas arbitrary Lean types may be empty. -/
theorem memoryRel_bignumHeaderCore {width : Nat} [NeZero width] (conf : Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (value : Int) (location : WordLocW width) (vars : List (Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain ((.number value, location) :: vars) ∧
      ¬ smallInt width value ∧ goodDimindex width →
    ∃ w address : BitVec width,
      location = .word w ∧ getRealAddr conf store w = some address ∧
      let digits : List (BitVec width) := Misc.Multiword.n2mw value.natAbs
      let tag : BitVec width := ((if value < 0 then 1 else 0) <<< 2) ||| 3
      (encodeHeader (width := width) conf tag.toNat digits.length).isSome ∧
      memory address = .word (makeHeader conf tag digits.length) := by
  rintro ⟨⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, _, _⟩, large, good⟩
  obtain ⟨roots, inv, addresses⟩ := wordInv
  obtain ⟨_, _, _, _, stackInv⟩ := inv
  obtain ⟨f, tf, _, _, _, _, _, _, _, values, _⟩ := stackInv
  cases roots with
  | nil => cases values
  | cons root rest =>
    cases values with
    | cons related _ =>
      cases addresses with
      | cons projected _ =>
        have num := (valueInv_number conf value refs root f tf heap).mp related
        simp only [large, ↓reduceIte] at num
        obtain ⟨ptr, rootEq, cell⟩ := num
        rw [rootEq] at projected
        obtain ⟨curr, other, _, _, stored, _, _, _, _, _, _, _, heapAssertion⟩ := heapMem.2.2.2.2.2.2.2
        obtain ⟨active, inactive, split, activeHeap, _⟩ := heapAssertion
        obtain ⟨member, encoded⟩ := wordHeap_bignumHeader conf heap ptr value curr active cell activeHeap
        have graph := (iff_of_eq (congrFun split.1 _)).mp (Or.inl member)
        have facts := (SetSep.fun2SetThm memory _ _ _).mp graph
        have addr := (getRealAddr_getAddr conf store heap ptr _ curr (.word 0)
          ⟨heapMem.1, cell, stored, good⟩).2
        refine ⟨getAddr conf ptr (.word 0), curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr,
          ?_, ?_, encoded, facts.1⟩
        · simpa [wordAddr] using projected.symm
        · simpa [BitVec.mul_comm] using addr

/-- A related bignum exposes its complete separated multiword payload. This
    Flapjack helper is a consequence used toward the original bignum memory
    theorem; it does not claim that theorem's unused polymorphic existential. -/
theorem memoryRel_bignumWords {width : Nat} [NeZero width] (conf : Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (value : Int) (location : WordLocW width) (vars : List (Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain ((.number value, location) :: vars) ∧
      ¬ smallInt width value ∧ goodDimindex width →
    ∃ (w address : BitVec width) (frame : ((BitVec width × WordLocW width) → Prop) → Prop),
      location = .word w ∧ getRealAddr conf store w = some address ∧
      let digits : List (BitVec width) := Misc.Multiword.n2mw value.natAbs
      let tag : BitVec width := ((if value < 0 then 1 else 0) <<< 2) ||| 3
      memory address = .word (makeHeader conf tag digits.length) ∧ domain address = true ∧
      SetSep.star (Misc.wordList (address + StackRemove.bytesInWord width) (digits.map WordLocW.word)) frame
        (SetSep.fun2Set (memory, fun a => domain a = true)) ∧
      digits.length < 2 ^ (width - 4) ∧
      w.getLsbD 0 = true ∧ (makeHeader conf tag digits.length).getLsbD 2 = true ∧
      (makeHeader conf tag digits.length).getLsbD 3 = true ∧
      ((makeHeader conf tag digits.length).getLsbD 4 = true ↔ value < 0) ∧
      WordGcFunctions.decodeLength conf (makeHeader conf tag digits.length) = BitVec.ofNat width digits.length := by
  rintro ⟨⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, _, _⟩, large, good⟩
  obtain ⟨roots, inv, addresses⟩ := wordInv
  obtain ⟨_, _, _, _, stackInv⟩ := inv
  obtain ⟨f, tf, _, _, _, _, _, _, _, values, _⟩ := stackInv
  cases roots with
  | nil => cases values
  | cons root rest =>
    cases values with
    | cons related _ =>
      cases addresses with
      | cons projected _ =>
        have num := (valueInv_number conf value refs root f tf heap).mp related
        simp only [large, ↓reduceIte] at num
        obtain ⟨ptr, rootEq, cell⟩ := num
        rw [rootEq] at projected
        obtain ⟨curr, other, _, _, stored, _, _, _, _, _, _, _, heapAssertion⟩ := heapMem.2.2.2.2.2.2.2
        have addr := (getRealAddr_getAddr conf store heap ptr _ curr (.word 0)
          ⟨heapMem.1, cell, stored, good⟩).2
        obtain ⟨frame, split, bound, decoded⟩ := bignumHeap conf heap ptr value curr _ _ cell heapAssertion
        have preserved := split
        obtain ⟨left, right, partition, singleton, _⟩ := split
        have member : left (curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr,
            .word (makeHeader conf (((if value < 0 then 1 else 0) <<< 2) ||| 3)
              (Misc.Multiword.n2mw (width := width) value.natAbs).length)) := by rw [singleton]
        have graph := (iff_of_eq (congrFun partition.1 _)).mp (Or.inl member)
        have facts := (SetSep.fun2SetThm memory _ _ _).mp graph
        have bits := bignumHeaderBits conf value (Misc.Multiword.n2mw (width := width) value.natAbs).length
          good heapMem.2.2.2.2.1
        refine ⟨getAddr conf ptr (.word 0), curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr,
          SetSep.star frame (SetSep.one (curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr,
            .word (makeHeader conf (((if value < 0 then 1 else 0) <<< 2) ||| 3)
              (Misc.Multiword.n2mw (width := width) value.natAbs).length))),
          ?_, ?_, facts.1, facts.2, ?_, bound, getAddr_zero_lowBit conf ptr, bits.1, bits.2.1, bits.2.2, decoded⟩
        · simpa [wordAddr] using projected.symm
        · simpa [BitVec.mul_comm] using addr
        · rw [SetSep.starComm (SetSep.one _) _] at preserved
          rw [← SetSep.starAssoc] at preserved
          exact preserved

/-- The first concrete bignum payload word contains the low magnitude bits.
    This is Flapjack infrastructure for the original bignum memory theorem. -/
theorem memoryRel_bignumFirstWord {width : Nat} [NeZero width] (conf : Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (value : Int) (location : WordLocW width) (vars : List (Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain ((.number value, location) :: vars) ∧
      ¬ smallInt width value ∧ goodDimindex width →
    ∃ (w address : BitVec width), location = .word w ∧ getRealAddr conf store w = some address ∧
      domain (address + StackRemove.bytesInWord width) = true ∧
      memory (address + StackRemove.bytesInWord width) = .word (BitVec.ofNat width value.natAbs) := by
  rintro ⟨rel, large, good⟩
  have nonzero : value ≠ 0 := by
    intro h
    subst value
    rcases good with hw | hw <;> subst width <;> norm_num [smallInt] at large
  have absNonzero : value.natAbs ≠ 0 := by simpa using nonzero
  have digits : Misc.Multiword.n2mw (width := width) value.natAbs =
      BitVec.ofNat width value.natAbs :: Misc.Multiword.n2mw (value.natAbs / 2 ^ width) := by
    rw [Misc.Multiword.n2mw]
    simp [absNonzero]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  obtain ⟨w, address, frame, loc, addr, _, _, separated, _, _, _, _, _, _⟩ :=
    memoryRel_bignumWords conf be next refs space store memory domain value location vars ⟨rel, large, good⟩
  obtain ⟨payload, rest, partition, payloadAssertion, _⟩ := separated
  have member := wordList_indexMember ((Misc.Multiword.n2mw (width := width) value.natAbs).map WordLocW.word)
    0 (by simp [digits]) (address + StackRemove.bytesInWord width) payload payloadAssertion
  have graph := (iff_of_eq (congrFun partition.1 _)).mp (Or.inl member)
  have facts := (SetSep.fun2SetThm memory _ _ _).mp graph
  refine ⟨w, address, loc, addr, ?_, ?_⟩
  · simpa [digits] using facts.2
  · simpa [digits] using facts.1

/-- Equal-length bignum headers differ only when their sign bits differ. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_bignum_cmp"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_bignumCmp {width : Nat} [NeZero width] (conf : Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i1 i2 : Int) (v1 v2 : WordLocW width) (vars : List (Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain ((.number i1, v1) :: (.number i2, v2) :: vars) ∧
      goodDimindex width ∧ ¬ smallInt width i1 ∧ ¬ smallInt width i2 →
    ∃ w1 w2 a1 a2 x1 x2 : BitVec width,
      v1 = .word w1 ∧ v2 = .word w2 ∧ getRealAddr conf store w1 = some a1 ∧
      getRealAddr conf store w2 = some a2 ∧ memory a1 = .word x1 ∧ memory a2 = .word x2 ∧
      (x1 ≠ x2 → WordGcFunctions.decodeLength conf x1 = WordGcFunctions.decodeLength conf x2 →
        ((16 : BitVec width) &&& x1 = 0) ≠ ((16 : BitVec width) &&& x2 = 0)) := by
  rintro ⟨rel, good, large1, large2⟩
  have tail := memoryRel_tail conf be next refs space store memory domain (.number i1, v1) ((.number i2, v2) :: vars) rel
  obtain ⟨w1, a1, f1, loc1, addr1, mem1, _, _, bound1, _, _, _, sign1, len1⟩ :=
    memoryRel_bignumWords conf be next refs space store memory domain i1 v1 ((.number i2, v2) :: vars) ⟨rel, large1, good⟩
  obtain ⟨w2, a2, f2, loc2, addr2, mem2, _, _, bound2, _, _, _, sign2, len2⟩ :=
    memoryRel_bignumWords conf be next refs space store memory domain i2 v2 vars ⟨tail, large2, good⟩
  refine ⟨w1, w2, a1, a2, _, _, loc1, loc2, addr1, addr2, mem1, mem2, ?_⟩
  intro different decoded sameMask
  have power : 2 ^ (width - 4) ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) (by omega)
  have length1 : (Misc.Multiword.n2mw (width := width) i1.natAbs).length < 2 ^ width := lt_of_lt_of_le bound1 power
  have length2 : (Misc.Multiword.n2mw (width := width) i2.natAbs).length < 2 ^ width := lt_of_lt_of_le bound2 power
  rw [len1, len2] at decoded
  have lens : (Misc.Multiword.n2mw (width := width) i1.natAbs).length =
      (Misc.Multiword.n2mw (width := width) i2.natAbs).length := by
    have h := congrArg BitVec.toNat decoded
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt length1, Nat.mod_eq_of_lt length2] using h
  have maskBit (x : BitVec width) : ((16 : BitVec width) &&& x = 0) ↔ x.getLsbD 4 = false := by
    rcases good with hw | hw <;> subst width <;> bv_decide
  rw [maskBit, maskBit] at sameMask
  have signEq : (i1 < 0 ↔ i2 < 0) := by
    cases b1 : (makeHeader (width := width) conf (((if i1 < 0 then 1 else 0) <<< 2) ||| 3)
      (Misc.Multiword.n2mw (width := width) i1.natAbs).length).getLsbD 4 <;>
    cases b2 : (makeHeader (width := width) conf (((if i2 < 0 then 1 else 0) <<< 2) ||| 3)
      (Misc.Multiword.n2mw (width := width) i2.natAbs).length).getLsbD 4 <;>
    simp_all
    all_goals omega
  apply different
  by_cases neg : i1 < 0
  · have neg' := signEq.mp neg
    simp [neg, neg', lens]
  · have neg' : ¬ i2 < 0 := fun h => neg (signEq.mpr h)
    simp [neg, neg', lens]

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
