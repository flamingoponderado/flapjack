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

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
