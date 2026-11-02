import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberHeader
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordCompare
import Flapjack.Misc.Multiword.Length

/-! Signed comparison of the concrete multiword bignum payloads. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Misc.Multiword
open Classical
noncomputable section

/-- Comparing equal-length magnitude lists in sign-adjusted order yields the
    original integer comparison code. This is Flapjack infrastructure for the
    source memory-relation comparison theorem. -/
theorem bignumMagnitudeCompare {width : Nat} [NeZero width] (i1 i2 : Int)
    (sameSign : (i1 < 0 ↔ i2 < 0))
    (sameLength : (n2mw i1.natAbs : List (BitVec width)).length =
      (n2mw i2.natAbs : List (BitVec width)).length) :
    (match mwCmp (if i1 < 0 then n2mw (width := width) i2.natAbs else n2mw i1.natAbs)
        (if i1 < 0 then n2mw (width := width) i1.natAbs else n2mw i2.natAbs) with
      | none => (1 : BitVec width) | some true => 0 | some false => 2) = wordCmpRes i1 i2 := by
  by_cases negative : i1 < 0
  · have negative2 : i2 < 0 := sameSign.mp negative
    simp only [negative, ↓reduceIte]
    rw [mwCmpThm _ _ sameLength, mw2n_n2mw, mw2n_n2mw]
    cases i1 <;> cases i2 <;> simp_all [wordCmpRes]
    all_goals repeat' first | split | contradiction
    all_goals simp_all <;> omega
  · have nonnegative2 : ¬ i2 < 0 := fun h => negative (sameSign.mpr h)
    simp only [negative, ↓reduceIte]
    rw [mwCmpThm _ _ sameLength.symm, mw2n_n2mw, mw2n_n2mw]
    cases i1 <;> cases i2 <;> simp_all [wordCmpRes]
    all_goals repeat' first | split | contradiction
    all_goals simp_all

/-- Distinct sign/length pairs determine signed bignum ordering. This is
    arithmetic infrastructure for the unequal-header comparison case. -/
theorem bignumDifferentLengthCompare {width : Nat} [NeZero width] (i1 i2 : Int)
    (different : (n2mw i1.natAbs : List (BitVec width)).length ≠
        (n2mw i2.natAbs : List (BitVec width)).length ∨ ((i1 < 0) ≠ (i2 < 0))) :
    wordCmpRes (width := width) i1 i2 =
      if i1 < 0 then
        if i2 < 0 then
          if (n2mw i1.natAbs : List (BitVec width)).length < (n2mw i2.natAbs : List (BitVec width)).length then 2 else 0
        else 0
      else if i2 < 0 then 2 else
        if (n2mw i1.natAbs : List (BitVec width)).length < (n2mw i2.natAbs : List (BitVec width)).length then 0 else 2 := by
  have lengthsOfLe12 : i1.natAbs ≤ i2.natAbs →
      (n2mw i1.natAbs : List (BitVec width)).length ≤ (n2mw i2.natAbs : List (BitVec width)).length :=
    n2mw_length_mono _ _
  have lengthsOfLe21 : i2.natAbs ≤ i1.natAbs →
      (n2mw i2.natAbs : List (BitVec width)).length ≤ (n2mw i1.natAbs : List (BitVec width)).length :=
    n2mw_length_mono _ _
  cases i1 <;> cases i2 <;> simp_all [wordCmpRes]
  all_goals repeat' first | split | contradiction
  all_goals try simp_all
  all_goals omega

/-- The target comparison loop returns the signed integer comparison code
    when both separated magnitude payloads have equal length and sign. -/
theorem bignumWordLoop {width : Nat} [NeZero width] (i1 i2 : Int)
    (frame1 frame2 : ((BitVec width × WordLocW width) → Prop) → Prop)
    (a1 a2 : BitVec width) (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
    (sameSign : (i1 < 0 ↔ i2 < 0))
    (sameLength : (n2mw i1.natAbs : List (BitVec width)).length =
      (n2mw i2.natAbs : List (BitVec width)).length)
    (bound : (n2mw i1.natAbs : List (BitVec width)).length < 2 ^ width)
    (first : SetSep.star (Misc.wordList (a1 + StackRemove.bytesInWord width)
      ((n2mw i1.natAbs : List (BitVec width)).map WordLocW.word)) frame1
      (SetSep.fun2Set (memory, fun a => domain a = true)))
    (second : SetSep.star (Misc.wordList (a2 + StackRemove.bytesInWord width)
      ((n2mw i2.natAbs : List (BitVec width)).map WordLocW.word)) frame2
      (SetSep.fun2Set (memory, fun a => domain a = true))) :
    let count := BitVec.ofNat width (n2mw i1.natAbs : List (BitVec width)).length
    let start1 := a1 + StackRemove.bytesInWord width * count
    let start2 := a2 + StackRemove.bytesInWord width * count
    wordCmpLoop count (if i1 < 0 then start2 else start1) (if i1 < 0 then start1 else start2)
      domain memory = some (wordCmpRes i1 i2) := by
  have correct := bignumMagnitudeCompare (width := width) i1 i2 sameSign sameLength
  by_cases negative : i1 < 0
  · simp only [negative, ↓reduceIte] at correct ⊢
    have bound2 : (n2mw i2.natAbs : List (BitVec width)).length < 2 ^ width := by rw [← sameLength]; exact bound
    have loop := wordCmpLoopThm (n2mw i2.natAbs) (n2mw i1.natAbs) frame2 frame1 a2 a1 domain memory
      ⟨sameLength.symm, bound2, second, first⟩
    rw [← sameLength] at loop
    cases outcome : mwCmp (n2mw (width := width) i2.natAbs) (n2mw i1.natAbs) with
    | none => simpa [outcome] using loop.trans (congrArg some correct)
    | some flag => cases flag <;> simpa [outcome] using loop.trans (congrArg some correct)
  · simp only [negative, ↓reduceIte] at correct ⊢
    have loop := wordCmpLoopThm (n2mw i1.natAbs) (n2mw i2.natAbs) frame1 frame2 a1 a2 domain memory
      ⟨sameLength, bound, first, second⟩
    cases outcome : mwCmp (n2mw (width := width) i1.natAbs) (n2mw i2.natAbs) with
    | none => simpa [outcome] using loop.trans (congrArg some correct)
    | some flag => cases flag <;> simpa [outcome] using loop.trans (congrArg some correct)

/-- Related large integers with identical headers compare correctly through
    the concrete word loop. This is a Flapjack helper for the original number
    comparison theorem, whose unequal-header cases remain separate. -/
theorem memoryRel_bignumEqualHeader {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i1 i2 : Int) (v1 v2 : WordLocW width) (vars : List (DataSem.Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain ((.number i1, v1) :: (.number i2, v2) :: vars) ∧
      goodDimindex width ∧ ¬ smallInt width i1 ∧ ¬ smallInt width i2 →
    ∃ w1 w2 a1 a2 h1 h2 : BitVec width,
      v1 = .word w1 ∧ v2 = .word w2 ∧ getRealAddr conf store w1 = some a1 ∧
      getRealAddr conf store w2 = some a2 ∧ memory a1 = .word h1 ∧ memory a2 = .word h2 ∧
      domain a1 = true ∧ domain a2 = true ∧
      (h1 = h2 →
        let a := if (16 : BitVec width) &&& h1 = 0 then a1 else a2
        let b := if (16 : BitVec width) &&& h1 = 0 then a2 else a1
        wordCmpLoop (WordGcFunctions.decodeLength conf h1)
          (a + StackRemove.bytesInWord width * WordGcFunctions.decodeLength conf h1)
          (b + StackRemove.bytesInWord width * WordGcFunctions.decodeLength conf h2)
          domain memory = some (wordCmpRes i1 i2)) := by
  rintro ⟨rel, good, large1, large2⟩
  have tail := memoryRel_tail conf be next refs space store memory domain (.number i1, v1) ((.number i2, v2) :: vars) rel
  obtain ⟨w1, a1, f1, loc1, addr1, mem1, dom1, words1, bound1, _, _, _, sign1, decoded1⟩ :=
    memoryRel_bignumWords conf be next refs space store memory domain i1 v1 ((.number i2, v2) :: vars) ⟨rel, large1, good⟩
  obtain ⟨w2, a2, f2, loc2, addr2, mem2, dom2, words2, bound2, _, _, _, sign2, decoded2⟩ :=
    memoryRel_bignumWords conf be next refs space store memory domain i2 v2 vars ⟨tail, large2, good⟩
  refine ⟨w1, w2, a1, a2, _, _, loc1, loc2, addr1, addr2, mem1, mem2, dom1, dom2, ?_⟩
  intro sameHeader
  have sameSign : (i1 < 0 ↔ i2 < 0) := by
    rw [← sign1, ← sign2, sameHeader]
  have sameDecoded := decoded1.symm.trans (sameHeader ▸ decoded2)
  have power : 2 ^ (width - 4) ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) (by omega)
  have small1 : (n2mw i1.natAbs : List (BitVec width)).length < 2 ^ width := lt_of_lt_of_le bound1 power
  have small2 : (n2mw i2.natAbs : List (BitVec width)).length < 2 ^ width := lt_of_lt_of_le bound2 power
  have sameLength : (n2mw i1.natAbs : List (BitVec width)).length =
      (n2mw i2.natAbs : List (BitVec width)).length := by
    have h := congrArg BitVec.toNat sameDecoded
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small1, Nat.mod_eq_of_lt small2] using h
  have loop := bignumWordLoop i1 i2 f1 f2 a1 a2 domain memory sameSign sameLength small1 words1 words2
  have maskBit (x : BitVec width) : ((16 : BitVec width) &&& x = 0) ↔ x.getLsbD 4 = false := by
    rcases good with hw | hw <;> subst width <;> bv_decide
  rw [← sameHeader]
  by_cases neg : i1 < 0
  · have bit := sign1.mpr neg
    have maskNe : (16 : BitVec width) &&& (makeHeader (width := width) conf
        (((if i1 < 0 then 1 else 0) <<< 2) ||| 3) (n2mw i1.natAbs : List (BitVec width)).length) ≠ 0 := by
      intro h
      have := (maskBit _).mp h
      simp_all
    simp only [neg, ↓reduceIte] at loop
    simp only [maskNe, ↓reduceIte, decoded1]
    exact loop
  · have bit : (makeHeader (width := width) conf (((if i1 < 0 then 1 else 0) <<< 2) ||| 3)
        (n2mw i1.natAbs : List (BitVec width)).length).getLsbD 4 = false := by
      cases h : (makeHeader (width := width) conf (((if i1 < 0 then 1 else 0) <<< 2) ||| 3)
        (n2mw i1.natAbs : List (BitVec width)).length).getLsbD 4 with
      | false => rfl
      | true => exact (neg (sign1.mp h)).elim
    have maskEq := (maskBit _).mpr bit
    simp only [neg, ↓reduceIte] at loop
    simp only [maskEq, ↓reduceIte, decoded1]
    exact loop

/-- Related large integers with different headers compare by their sign and
    decoded digit lengths. This is Flapjack infrastructure for the original
    number-comparison theorem. -/
theorem memoryRel_bignumDifferentHeader {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i1 i2 : Int) (v1 v2 : WordLocW width) (vars : List (DataSem.Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain ((.number i1, v1) :: (.number i2, v2) :: vars) ∧
      goodDimindex width ∧ ¬ smallInt width i1 ∧ ¬ smallInt width i2 →
    ∃ w1 w2 a1 a2 h1 h2 : BitVec width,
      v1 = .word w1 ∧ v2 = .word w2 ∧ getRealAddr conf store w1 = some a1 ∧
      getRealAddr conf store w2 = some a2 ∧ memory a1 = .word h1 ∧ memory a2 = .word h2 ∧
      domain a1 = true ∧ domain a2 = true ∧
      (h1 ≠ h2 → wordCmpRes (width := width) i1 i2 =
        if h1 &&& 16 = 0 then
          if h2 &&& 16 = 0 then
            if WordGcFunctions.decodeLength conf h1 < WordGcFunctions.decodeLength conf h2 then 0 else 2
          else 2
        else if h2 &&& 16 = 0 then 0 else
          if WordGcFunctions.decodeLength conf h1 < WordGcFunctions.decodeLength conf h2 then 2 else 0) := by
  rintro ⟨rel, good, large1, large2⟩
  have tail := memoryRel_tail conf be next refs space store memory domain (.number i1, v1) ((.number i2, v2) :: vars) rel
  obtain ⟨w1, a1, f1, loc1, addr1, mem1, dom1, _, bound1, _, _, _, sign1, decoded1⟩ :=
    memoryRel_bignumWords conf be next refs space store memory domain i1 v1 ((.number i2, v2) :: vars) ⟨rel, large1, good⟩
  obtain ⟨w2, a2, f2, loc2, addr2, mem2, dom2, _, bound2, _, _, _, sign2, decoded2⟩ :=
    memoryRel_bignumWords conf be next refs space store memory domain i2 v2 vars ⟨tail, large2, good⟩
  refine ⟨w1, w2, a1, a2, _, _, loc1, loc2, addr1, addr2, mem1, mem2, dom1, dom2, ?_⟩
  intro different
  have power : 2 ^ (width - 4) ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) (by omega)
  have small1 : (n2mw i1.natAbs : List (BitVec width)).length < 2 ^ width := lt_of_lt_of_le bound1 power
  have small2 : (n2mw i2.natAbs : List (BitVec width)).length < 2 ^ width := lt_of_lt_of_le bound2 power
  have diffPair : (n2mw i1.natAbs : List (BitVec width)).length ≠
      (n2mw i2.natAbs : List (BitVec width)).length ∨ ((i1 < 0) ≠ (i2 < 0)) := by
    by_contra no
    have len : (n2mw i1.natAbs : List (BitVec width)).length =
        (n2mw i2.natAbs : List (BitVec width)).length := by
      by_contra h
      exact no (Or.inl h)
    have sign : (i1 < 0 ↔ i2 < 0) := by
      have eq : (i1 < 0) = (i2 < 0) := by
        by_contra h
        exact no (Or.inr h)
      exact iff_of_eq eq
    apply different
    by_cases neg : i1 < 0
    · have neg2 := sign.mp neg
      simp [neg, neg2, len]
    · have neg2 : ¬ i2 < 0 := fun h => neg (sign.mpr h)
      simp [neg, neg2, len]
  have maskBit (x : BitVec width) : (x &&& 16 = 0) ↔ x.getLsbD 4 = false := by
    rcases good with hw | hw <;> subst width <;> bv_decide
  have mask1 : (makeHeader (width := width) conf (((if i1 < 0 then 1 else 0) <<< 2) ||| 3)
        (n2mw i1.natAbs : List (BitVec width)).length &&& 16 = 0) ↔ ¬ i1 < 0 := by
    rw [maskBit]
    constructor
    · intro bit neg
      have bit' := sign1.mpr neg
      rw [bit] at bit'
      contradiction
    · intro nonneg
      cases bit : (makeHeader (width := width) conf (((if i1 < 0 then 1 else 0) <<< 2) ||| 3)
        (n2mw i1.natAbs : List (BitVec width)).length).getLsbD 4 with
      | false => rfl
      | true => exact (nonneg (sign1.mp bit)).elim
  have mask2 : (makeHeader (width := width) conf (((if i2 < 0 then 1 else 0) <<< 2) ||| 3)
        (n2mw i2.natAbs : List (BitVec width)).length &&& 16 = 0) ↔ ¬ i2 < 0 := by
    rw [maskBit]
    constructor
    · intro bit neg
      have bit' := sign2.mpr neg
      rw [bit] at bit'
      contradiction
    · intro nonneg
      cases bit : (makeHeader (width := width) conf (((if i2 < 0 then 1 else 0) <<< 2) ||| 3)
        (n2mw i2.natAbs : List (BitVec width)).length).getLsbD 4 with
      | false => rfl
      | true => exact (nonneg (sign2.mp bit)).elim
  have cmp := bignumDifferentLengthCompare (width := width) i1 i2 diffPair
  rw [decoded1, decoded2]
  simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small1, Nat.mod_eq_of_lt small2]
  simp only [mask1, mask2]
  by_cases neg1 : i1 < 0 <;> by_cases neg2 : i2 < 0 <;> simp_all

/-- Complete both-large branch of the target number comparison. This is
    Flapjack induction infrastructure; the source theorem also covers small
    integers and is not asserted here. -/
theorem memoryRel_bothBignumCompare {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i1 i2 : Int) (v1 v2 : WordLocW width) (vars : List (DataSem.Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain ((.number i1, v1) :: (.number i2, v2) :: vars) ∧
      goodDimindex width ∧ ¬ smallInt width i1 ∧ ¬ smallInt width i2 →
    ∃ w1 w2 a1 a2 h1 h2 : BitVec width,
      v1 = .word w1 ∧ v2 = .word w2 ∧ getRealAddr conf store w1 = some a1 ∧
      memory a1 = .word h1 ∧ domain a1 = true ∧ getRealAddr conf store w2 = some a2 ∧
      memory a2 = .word h2 ∧ domain a2 = true ∧
      if h1 = h2 then
        let a := if (16 : BitVec width) &&& h1 = 0 then a1 else a2
        let b := if (16 : BitVec width) &&& h1 = 0 then a2 else a1
        wordCmpLoop (WordGcFunctions.decodeLength conf h1)
          (a + StackRemove.bytesInWord width * WordGcFunctions.decodeLength conf h1)
          (b + StackRemove.bytesInWord width * WordGcFunctions.decodeLength conf h2)
          domain memory = some (wordCmpRes i1 i2)
      else wordCmpRes (width := width) i1 i2 =
        if h1 &&& 16 = 0 then
          if h2 &&& 16 = 0 then
            if WordGcFunctions.decodeLength conf h1 < WordGcFunctions.decodeLength conf h2 then 0 else 2
          else 2
        else if h2 &&& 16 = 0 then 0 else
          if WordGcFunctions.decodeLength conf h1 < WordGcFunctions.decodeLength conf h2 then 2 else 0 := by
  intro assumptions
  obtain ⟨w1, w2, a1, a2, h1, h2, loc1, loc2, addr1, addr2, mem1, mem2, dom1, dom2, equal⟩ :=
    memoryRel_bignumEqualHeader conf be next refs space store memory domain i1 i2 v1 v2 vars assumptions
  obtain ⟨w1', w2', a1', a2', h1', h2', loc1', loc2', addr1', addr2', mem1', mem2', _, _, unequal⟩ :=
    memoryRel_bignumDifferentHeader conf be next refs space store memory domain i1 i2 v1 v2 vars assumptions
  have w1eq : w1 = w1' := WordLocW.word.inj (loc1.symm.trans loc1')
  have w2eq : w2 = w2' := WordLocW.word.inj (loc2.symm.trans loc2')
  subst w1'
  subst w2'
  have a1eq : a1 = a1' := Option.some.inj (addr1.symm.trans addr1')
  have a2eq : a2 = a2' := Option.some.inj (addr2.symm.trans addr2')
  subst a1'
  subst a2'
  have h1eq : h1 = h1' := WordLocW.word.inj (mem1.symm.trans mem1')
  have h2eq : h2 = h2' := WordLocW.word.inj (mem2.symm.trans mem2')
  subst h1'
  subst h2'
  refine ⟨w1, w2, a1, a2, h1, h2, loc1, loc2, addr1, mem1, dom1, addr2, mem2, dom2, ?_⟩
  by_cases h : h1 = h2
  · simp only [h, ↓reduceIte]
    simpa only [h] using equal h
  · simp only [h, ↓reduceIte]
    exact unequal h

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
