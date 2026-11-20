module

public import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers
public import Flapjack.Compiler.Backend.Semantics.WordSem
public import Flapjack.Compiler.Backend.WordGcFunctions
public import Flapjack.HolArb
public import Flapjack.SemanticPrimitivesHOL.Compare
public import Flapjack.Misc.GoodDimindex

@[expose] public section

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- Compare byte sequences one byte at a time, with the original clock and
independently typed result words. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_str_cmp_loop_def"
  (words_as_type_indexed_bitvec)]
def wordStrCmpLoop {width : Nat} {resultWidth1 : Nat} {resultWidth2 : Nat}
    [NeZero width] [NeZero resultWidth1] [NeZero resultWidth2]
    (a1 a2 : BitVec width) (r1 : BitVec resultWidth1) (r2 : BitVec resultWidth2)
    (len : BitVec width) (dm : BitVec width → Bool) (m : BitVec width → WordLocW width)
    (be : Bool) : Nat → Option (BitVec resultWidth1 × BitVec resultWidth2)
  | 0 => none
  | ck + 1 =>
      if len = wordSemBytesInWord then some (r1, r2)
      else
        match memLoadByteAuxExact m dm be a1 with
        | none => none
        | some b1 =>
          match memLoadByteAuxExact m dm be a2 with
          | none => none
          | some b2 =>
            if b1 = b2 then wordStrCmpLoop (a1 + 1) (a2 + 1) r1 r2 (len - 1) dm m be ck
            else some (BitVec.ofNat resultWidth1 b1.toNat, BitVec.ofNat resultWidth2 b2.toNat)

/-- Compare the two length headers before walking their byte payloads. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_str_cmp_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordStrCmp {width : Nat} [NeZero width]
    (b : Bool) (a1 a2 : BitVec width) (dm : BitVec width → Bool)
    (m : BitVec width → WordLocW width) (be : Bool) (c : DataToWord.Config) :
    Option (BitVec width × BitVec width) :=
  let k := width - c.lenSize - Flapjack.wordShiftAmount width
  if dm a1 && dm a2 && wordSemIsWordLoc (m a1) && wordSemIsWordLoc (m a2) then
    let l1 := wordSemTheWord (m a1) >>> k
    let l2 := wordSemTheWord (m a2) >>> k
    if b then
      if l1 ≠ l2 then some (l1, l2)
      else wordStrCmpLoop (a1 + wordSemBytesInWord) (a2 + wordSemBytesInWord)
        l1 l1 l1 dm m be (2 ^ width)
    else
      let len := BitVec.ofNat width (min l1.toNat l2.toNat)
      wordStrCmpLoop (a1 + wordSemBytesInWord) (a2 + wordSemBytesInWord)
        l1 l2 len dm m be (2 ^ width)
  else none

/-- Find the first differing words. HOL pattern completion assigns `ARB` at
    the result-pair type to either unequal-length case. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "find_diff_def"
  (words_as_type_indexed_bitvec)]
noncomputable def findDiff {inputWidth : Nat} {resultWidth1 : Nat} {resultWidth2 : Nat}
    [NeZero inputWidth] [NeZero resultWidth1] [NeZero resultWidth2] :
    List (BitVec inputWidth) → List (BitVec inputWidth) →
      BitVec resultWidth1 → BitVec resultWidth2 → BitVec resultWidth1 × BitVec resultWidth2
  | [], [], r1, r2 => (r1, r2)
  | x :: xs, y :: ys, r1, r2 =>
      if x = y then findDiff xs ys r1 r2
      else (BitVec.ofNat resultWidth1 x.toNat, BitVec.ofNat resultWidth2 y.toNat)
  | _, _, _, _ => holArb _

/-- The byte loop returns the first difference in the requested prefixes. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_str_loop_thm"
  (words_as_type_indexed_bitvec)]
theorem wordStrLoopThm {width : Nat} {resultWidth1 : Nat} {resultWidth2 : Nat}
    [NeZero width] [NeZero resultWidth1] [NeZero resultWidth2]
    (k : Nat) (a1 a2 : BitVec width) (r1 : BitVec resultWidth1) (r2 : BitVec resultWidth2)
    (dm : BitVec width → Bool) (m : BitVec width → WordLocW width) (be : Bool) (d : Nat)
    (vals1 vals2 : List (BitVec 8))
    (load1 : ∀ i (h : i < vals1.length), memLoadByteAuxExact m dm be (a1 + BitVec.ofNat width i) = some vals1[i])
    (load2 : ∀ i (h : i < vals2.length), memLoadByteAuxExact m dm be (a2 + BitVec.ofNat width i) = some vals2[i])
    (bound1 : k ≤ vals1.length) (bound2 : k ≤ vals2.length) (fuel : k < d) (dim : d ≤ 2 ^ width) :
    wordStrCmpLoop a1 a2 r1 r2 (BitVec.ofNat width k + wordSemBytesInWord) dm m be d =
      some (findDiff (vals1.take k) (vals2.take k) r1 r2) := by
  induction k generalizing a1 a2 r1 r2 dm m be d vals1 vals2 with
  | zero =>
    cases d with
    | zero => omega
    | succ d => simp [wordStrCmpLoop, findDiff]
  | succ k ih =>
    cases d with
    | zero => omega
    | succ d =>
      cases vals1 with
      | nil => simp at bound1
      | cons x xs =>
        cases vals2 with
        | nil => simp at bound2
        | cons y ys =>
          have ksmall : k + 1 < 2 ^ width := by omega
          have pos : (BitVec.ofNat width (k + 1) : BitVec width) ≠ 0 := by
            intro h
            have hnum := congrArg BitVec.toNat h
            simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ksmall] at hnum
          have lenNe : (BitVec.ofNat width (k + 1) + wordSemBytesInWord : BitVec width) ≠ wordSemBytesInWord := by
            intro h
            apply pos
            exact (BitVec.add_right_inj (wordSemBytesInWord : BitVec width)).mp (by simpa using h)
          have h1 : memLoadByteAuxExact m dm be a1 = some x := by
            have v := load1 0 (by simp)
            change memLoadByteAuxExact m dm be (a1 + BitVec.ofNat width 0) = some x at v
            simpa using v
          have h2 : memLoadByteAuxExact m dm be a2 = some y := by
            have v := load2 0 (by simp)
            change memLoadByteAuxExact m dm be (a2 + BitVec.ofNat width 0) = some y at v
            simpa using v
          have tl1 : ∀ i (h : i < xs.length), memLoadByteAuxExact m dm be (a1 + 1 + BitVec.ofNat width i) = some xs[i] := by
            intro i hi
            have v := load1 (i+1) (by simp; omega)
            have addr : a1 + BitVec.ofNat width (i + 1) = a1 + 1 + BitVec.ofNat width i := by
              simp only [BitVec.ofNat_add, BitVec.add_assoc]
              rw [BitVec.add_comm (BitVec.ofNat width i)]
              simp only [BitVec.ofNat_eq_ofNat]
            rw [addr] at v
            simpa only [List.getElem_cons_succ] using v
          have tl2 : ∀ i (h : i < ys.length), memLoadByteAuxExact m dm be (a2 + 1 + BitVec.ofNat width i) = some ys[i] := by
            intro i hi
            have v := load2 (i+1) (by simp; omega)
            have addr : a2 + BitVec.ofNat width (i + 1) = a2 + 1 + BitVec.ofNat width i := by
              simp only [BitVec.ofNat_add, BitVec.add_assoc]
              rw [BitVec.add_comm (BitVec.ofNat width i)]
              simp only [BitVec.ofNat_eq_ofNat]
            rw [addr] at v
            simpa only [List.getElem_cons_succ] using v
          simp only [List.take_succ_cons, findDiff]
          rw [wordStrCmpLoop]
          simp only [lenNe, ↓reduceIte, h1, h2]
          split
          · have recurse := ih (a1+1) (a2+1) r1 r2 dm m be d xs ys tl1 tl2 (by simp at bound1; omega) (by simp at bound2; omega) (by omega) (by omega)
            have lenPred : (BitVec.ofNat width (k + 1) + wordSemBytesInWord - 1 : BitVec width) =
                BitVec.ofNat width k + wordSemBytesInWord := by
              simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
              rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat width 1) wordSemBytesInWord,
                ← BitVec.add_assoc, BitVec.add_sub_cancel]
            simpa only [lenPred] using recurse
          · rfl

/-- Removing a shared leading byte preserves string comparison. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "str_cmp_cons"]
theorem strCmpCons (b : Bool) (cmp : Flapjack.Opb)
    (x : Flapjack.Basis.Pure.MlString.HolChar) (xs ys : List Flapjack.Basis.Pure.MlString.HolChar) :
    Flapjack.SemanticPrimitivesHOL.strCmp b cmp (.implode (x :: xs)) (.implode (x :: ys)) = true ↔
      Flapjack.SemanticPrimitivesHOL.strCmp b cmp (.implode xs) (.implode ys) = true := by
  cases b <;> by_cases h : xs.length = ys.length <;> simp [Flapjack.SemanticPrimitivesHOL.strCmp, Flapjack.Basis.Pure.MlString.MlString.explode, compare, compareOfLessAndEq, h]

/-- Bytes fit unchanged in either word width admitted by `goodDimindex`.
This is local support for both HOL string-comparison proofs. -/
private theorem byteToWordMod {width : Nat} [NeZero width] (x : BitVec 8)
    (good : goodDimindex width) : x.toNat % 2 ^ width = x.toNat := by
  apply Nat.mod_eq_of_lt
  rcases good with hw | hw <;> subst width <;> have h := x.isLt <;> simp_all <;> omega

/-- The first differing byte determines fast comparison of equal-length strings. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "find_diff_str_cmp_thm1"
  (words_as_type_indexed_bitvec)]
theorem findDiffStrCmpThm1 {width : Nat} [NeZero width] (vals1 vals2 : List (BitVec 8)) (l : Nat) (cmp : Flapjack.Opb)
    (same : vals1.length = vals2.length) (good : goodDimindex width) :
    ∃ (r1 r2 : BitVec width),
      findDiff vals1 vals2 (BitVec.ofNat width l) (BitVec.ofNat width l) = (r1,r2) ∧
      (strCmp true cmp (.implode (vals1.map (fun x => BitVec.ofNat 8 x.toNat)))
        (.implode (vals2.map (fun x => BitVec.ofNat 8 x.toNat))) = true ↔
       numCmp cmp r1.toNat r2.toNat = true) := by
  induction vals1 generalizing vals2 with
  | nil =>
    cases vals2 with
    | nil =>
      refine ⟨BitVec.ofNat width l, BitVec.ofNat width l, rfl, ?_⟩
      simp [strCmp, numCmp, MlString.explode]
      rfl
    | cons y ys => simp at same
  | cons x xs ih =>
    cases vals2 with
    | nil => simp at same
    | cons y ys =>
      have lens : xs.length = ys.length := by simpa using same
      by_cases h : x = y
      · subst y
        obtain ⟨r1,r2,eq,cmpEq⟩ := ih ys lens
        refine ⟨r1,r2, ?_, ?_⟩
        · simpa [findDiff] using eq
        · simpa using (strCmpCons true cmp x (xs.map (fun x => BitVec.ofNat 8 x.toNat))
            (ys.map (fun x => BitVec.ofNat 8 x.toNat))).trans cmpEq
      · refine ⟨BitVec.ofNat width x.toNat, BitVec.ofNat width y.toNat, ?_, ?_⟩
        · simp [findDiff, h]
        · have hxmod := byteToWordMod (width := width) x good
          have hymod := byteToWordMod (width := width) y good
          have neNum : x.toNat ≠ y.toNat := fun heq => h (BitVec.eq_of_toNat_eq heq)
          cases hc : compare x.toNat y.toNat with
          | lt => simp [strCmp, numCmp, MlString.explode, lens, hxmod, hymod, hc]
          | eq =>
            have heq : x.toNat = y.toNat := Std.compare_eq_iff_eq.mp hc
            exact (neNum heq).elim
          | gt => simp [strCmp, numCmp, MlString.explode, lens, hxmod, hymod, hc]

/-- The first differing prefix determines ordinary string comparison. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "find_diff_str_cmp_thm2"
  (words_as_type_indexed_bitvec)]
theorem findDiffStrCmpThm2 {width : Nat} [NeZero width] (k : Nat) (vals1 vals2 : List (BitVec 8))
    (l1 l2 : Nat) (cmp : Flapjack.Opb)
    (len1 : l1 = vals1.length + 2 ^ Flapjack.wordShiftAmount width)
    (len2 : l2 = vals2.length + 2 ^ Flapjack.wordShiftAmount width)
    (bound1 : k + l1 < 2 ^ width) (bound2 : k + l2 < 2 ^ width) (good : goodDimindex width) :
    ∃ (r1 r2 : BitVec width),
      findDiff (vals1.take (min vals1.length vals2.length))
        (vals2.take (min vals1.length vals2.length)) (BitVec.ofNat width (k + l1))
        (BitVec.ofNat width (k + l2)) = (r1, r2) ∧
      (strCmp false cmp (.implode (vals1.map (fun x => BitVec.ofNat 8 x.toNat)))
        (.implode (vals2.map (fun x => BitVec.ofNat 8 x.toNat))) = true ↔
       numCmp cmp r1.toNat r2.toNat = true) := by
  subst l1
  subst l2
  induction vals1 generalizing vals2 k with
  | nil =>
    cases vals2 with
    | nil =>
      refine ⟨BitVec.ofNat width (k + 2 ^ Flapjack.wordShiftAmount width),
        BitVec.ofNat width (k + 2 ^ Flapjack.wordShiftAmount width), ?_, ?_⟩
      · simp [findDiff]
      · simp [strCmp, numCmp, MlString.explode]
        rfl
    | cons y ys =>
      have hlt : (BitVec.ofNat width (k + ([] : List (BitVec 8)).length + 2 ^ Flapjack.wordShiftAmount width)).toNat <
          (BitVec.ofNat width (k + (y :: ys).length + 2 ^ Flapjack.wordShiftAmount width)).toNat := by
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        have h1 : k + ([] : List (BitVec 8)).length + 2 ^ Flapjack.wordShiftAmount width < 2 ^ width := by simpa [Nat.add_assoc] using bound1
        have h2 : k + (y :: ys).length + 2 ^ Flapjack.wordShiftAmount width < 2 ^ width := by simpa [Nat.add_assoc] using bound2
        rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
        simp only [List.length_nil, List.length_cons]
        omega
      refine ⟨BitVec.ofNat width (k + 2 ^ Flapjack.wordShiftAmount width),
        BitVec.ofNat width (k + ((y :: ys).length + 2 ^ Flapjack.wordShiftAmount width)), ?_, ?_⟩
      · simp [findDiff]
      · simp only [List.length_nil, List.length_cons, Nat.zero_add, Nat.add_assoc, BitVec.toNat_ofNat] at hlt
        simp [strCmp, numCmp, MlString.explode, compare, compareOfLessAndEq, Nat.add_assoc, hlt]
        rfl
  | cons x xs ih =>
    cases vals2 with
    | nil =>
      have hgt : (BitVec.ofNat width (k + ([] : List (BitVec 8)).length + 2 ^ Flapjack.wordShiftAmount width)).toNat <
          (BitVec.ofNat width (k + (x :: xs).length + 2 ^ Flapjack.wordShiftAmount width)).toNat := by
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        have h1 : k + ([] : List (BitVec 8)).length + 2 ^ Flapjack.wordShiftAmount width < 2 ^ width := by simpa [Nat.add_assoc] using bound2
        have h2 : k + (x :: xs).length + 2 ^ Flapjack.wordShiftAmount width < 2 ^ width := by simpa [Nat.add_assoc] using bound1
        rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
        simp only [List.length_nil, List.length_cons]
        omega
      refine ⟨BitVec.ofNat width (k + ((x :: xs).length + 2 ^ Flapjack.wordShiftAmount width)),
        BitVec.ofNat width (k + 2 ^ Flapjack.wordShiftAmount width), ?_, ?_⟩
      · simp [findDiff]
      · simp only [List.length_nil, List.length_cons, Nat.zero_add, Nat.add_assoc, BitVec.toNat_ofNat] at hgt
        simp [strCmp, numCmp, MlString.explode, compare, compareOfLessAndEq,
          Nat.add_assoc, Nat.not_lt_of_ge (Nat.le_of_lt hgt), Nat.ne_of_gt hgt]
        rfl
    | cons y ys =>
      by_cases h : x = y
      · subst y
        have b1 : (k + 1) + (xs.length + 2 ^ Flapjack.wordShiftAmount width) < 2 ^ width := by
          simp only [List.length_cons] at bound1
          omega
        have b2 : (k + 1) + (ys.length + 2 ^ Flapjack.wordShiftAmount width) < 2 ^ width := by
          simp only [List.length_cons] at bound2
          omega
        obtain ⟨r1,r2,eq,cmpEq⟩ := ih (k+1) ys b1 b2
        refine ⟨r1,r2, ?_, ?_⟩
        · simp only [List.length_cons, Nat.succ_min_succ, List.take_succ_cons, findDiff, if_pos]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using eq
        · simpa using (strCmpCons false cmp x (xs.map (fun x => BitVec.ofNat 8 x.toNat))
            (ys.map (fun x => BitVec.ofNat 8 x.toNat))).trans cmpEq
      · refine ⟨BitVec.ofNat width x.toNat, BitVec.ofNat width y.toNat, ?_, ?_⟩
        · simp only [List.length_cons, Nat.succ_min_succ, List.take_succ_cons, findDiff, if_neg h]
        · have hxmod := byteToWordMod (width := width) x good
          have hymod := byteToWordMod (width := width) y good
          have neNum : x.toNat ≠ y.toNat := fun heq => h (BitVec.eq_of_toNat_eq heq)
          cases hc : compare x.toNat y.toNat with
          | lt => simp [strCmp, numCmp, MlString.explode, hxmod, hymod, hc]
          | eq =>
            have heq : x.toNat = y.toNat := Std.compare_eq_iff_eq.mp hc
            exact (neNum heq).elim
          | gt => simp [strCmp, numCmp, MlString.explode, hxmod, hymod, hc]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
