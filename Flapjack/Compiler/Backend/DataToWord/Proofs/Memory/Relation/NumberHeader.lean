import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockHeader
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Number

/-! Header extraction for heap-allocated integers. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem
open Classical
noncomputable section

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

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
