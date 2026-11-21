module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Div
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberCompare
public import Flapjack.Compiler.Backend.DataLive.Proofs.State

@[expose] public section

/-! Supporting lemmas of the data-to-word addition assignment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace AddSupportWitnesses
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end AddSupportWitnesses

/-- Adding a known zero to an optional size is the identity. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "opt_map_plus_zero_id" 9723]
theorem optMapPlusZeroId (n : Option Nat) : wordSemOptionAdd (some 0) n = n := by
  cases n <;> simp [wordSemOptionAdd]

/-- At a good word width, the source small-number range is the immediate range. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "small_num_small_int"
  (word_dimension_as_width := width)]
theorem smallNum_smallInt (width : Nat) [NeZero width] :
    goodDimindex width → DataSem.smallNum (decide (width = 64)) = smallInt width := by
  intro good
  funext i
  rcases good with h | h <;> subst width <;> norm_num [DataSem.smallNum, smallInt]

/-- A related number whose word has its tag bit set is not small. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "memory_rel_small_int"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_smallInt {width : Nat} [NeZero width] (c : Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) (i : Int) (w : BitVec width)
    (vars : List (DataSem.Value × WordLocW width)) :
    memoryRel c be ts refs sp st m dm ((.number i, .word w) :: vars) ∧
      w.getLsbD 0 = true ∧ goodDimindex width → ¬ smallInt width i := by
  rintro ⟨rel, bit, good⟩ small
  have word := WordLocW.word.inj (memoryRel_numberImp c be ts refs sp st m dm i (.word w) vars
    ⟨good, small, rel⟩)
  subst word
  rw [smallnum_lowBit good i] at bit
  contradiction

/-- The state relation ignores the safe-for-space flag and peak heap length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "state_rel_upd_safe_pkheap"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_updSafePkheap {width : Nat} [NeZero width] {C F : Type} :
    ∀ (c : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat)
      (s : Flapjack.Compiler.Backend.DataSem.State C F)
      (lcl : Spt Flapjack.Compiler.Backend.DataSem.Value) (hpk : Nat)
      (r : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat)),
      stateRel c l1 l2 { s with locals := lcl, space := 0, stackMax := none } r none locs ↔
        stateRel c l1 l2
          { s with locals := lcl, stackMax := none, space := 0, safeForSpace := false,
                   peakHeapLength := hpk } r none locs := by
  intro c l1 l2 s lcl hpk r locs
  exact Iff.rfl

/-- The state relation ignores the safe-for-space flag. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "state_rel_ignore_safe_for_space"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_ignoreSafeForSpace {width : Nat} [NeZero width] {C F : Type}
    (c : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat)
    (x : Flapjack.Compiler.Backend.DataSem.State C F) (l : Spt Flapjack.Compiler.Backend.DataSem.Value)
    (s : Nat) (m : Bool) (r : WordSemStateFiniteExact width C F)
    (t : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)))
    (locs : List (Nat × Nat)) :
    stateRel c l1 l2 { x with locals := l, space := s, safeForSpace := m } r t locs ↔
      stateRel c l1 l2 { x with locals := l, space := s } r t locs :=
  Iff.rfl

/-- The state relation ignores the peak heap length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "state_rel_peak_heap_length"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_peakHeapLength {width : Nat} [NeZero width] {C F : Type}
    (c : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat)
    (x : Flapjack.Compiler.Backend.DataSem.State C F) (l : Spt Flapjack.Compiler.Backend.DataSem.Value)
    (s m : Nat) (r : WordSemStateFiniteExact width C F)
    (t : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)))
    (locs : List (Nat × Nat)) :
    stateRel c l1 l2 { x with locals := l, space := s, peakHeapLength := m } r t locs ↔
      stateRel c l1 l2 { x with locals := l, space := s } r t locs :=
  Iff.rfl

/-- Immediate encodings add as their integers when the sum is small. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "small_int_Smallnum_add"
  (words_as_type_indexed_bitvec)]
theorem smallInt_smallnum_add {width : Nat} [NeZero width] (i1 i2 : Int) :
    goodDimindex width ∧ smallInt width (i1 + i2) →
    (smallnum i1 : BitVec width) + smallnum i2 = smallnum (i1 + i2) := by
  intro _
  rw [smallnum_i2w, smallnum_i2w, smallnum_i2w, Int.mul_add, BitVec.ofInt_add]

/-- Four times a small integer lies within the signed word range. HOL's
integer-valued `INT_MIN (:'a)` and `INT_MAX (:'a)` are written out as
`-2 ^ (width - 1)` and `2 ^ (width - 1) - 1`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "small_int_INT_MIN_MAX"
  (word_dimension_as_width := width)]
theorem smallInt_intMinMax (width : Nat) [NeZero width] (i : Int) :
    goodDimindex width ∧ smallInt width i →
    -(2 : Int) ^ (width - 1) ≤ 4 * i ∧ 4 * i ≤ (2 : Int) ^ (width - 1) - 1 := by
  rintro ⟨good, small⟩
  have bounds := smallnum_signedBounds good i small
  omega

/-- Signed values of small immediate encodings add without overflow. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "small_int_w2i_Smallnum_add"
  (words_as_type_indexed_bitvec)]
theorem smallInt_toInt_smallnum_add {width : Nat} [NeZero width] (i1 i2 : Int) :
    goodDimindex width ∧ smallInt width (i1 + i2) ∧ smallInt width i1 ∧ smallInt width i2 →
    ((smallnum i1 : BitVec width) + smallnum i2).toInt =
      (smallnum i1 : BitVec width).toInt + (smallnum i2 : BitVec width).toInt := by
  rintro ⟨good, sum, small1, small2⟩
  have pos : 0 < width := NeZero.pos width
  rw [smallInt_smallnum_add i1 i2 ⟨good, sum⟩]
  have b := smallnum_signedBounds good _ sum
  have b1 := smallnum_signedBounds good _ small1
  have b2 := smallnum_signedBounds good _ small2
  rw [smallnum_i2w, smallnum_i2w, smallnum_i2w,
    BitVec.toInt_ofInt_eq_self pos b.1 b.2, BitVec.toInt_ofInt_eq_self pos b1.1 b1.2,
    BitVec.toInt_ofInt_eq_self pos b2.1 b2.2]
  ring

/-- The state relation fixes the source architecture flag from the word width. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "state_rel_IMP_arch_64_bit"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_arch64Bit {width : Nat} [NeZero width] {C F : Type}
    (c : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat)
    (s : Flapjack.Compiler.Backend.DataSem.State C F) (t : WordSemStateFiniteExact width C F)
    (xs : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)))
    (locs : List (Nat × Nat)) :
    stateRel c l1 l2 s t xs locs → (s.limits.arch64Bit = true ↔ width = 64) := by
  intro related
  have limits := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [limits.2.2.1]
  simp

/-- Cutting an already cut state again changes nothing. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "cut_state_opt_twice"]
theorem cutStateOpt_twice {C F : Type} (namesOpt : Option NumSet) (s x : DataSem.State C F) :
    DataSem.cutStateOpt namesOpt s = some x → DataSem.cutStateOpt namesOpt x = some x := by
  classical
  cases namesOpt with
  | none => intro h; cases h; rfl
  | some names =>
    intro h
    simp only [DataSem.cutStateOpt, DataSem.cutState, Option.map_eq_some_iff] at h ⊢
    obtain ⟨env, cut, rfl⟩ := h
    have lookup := DataLive.cutEnv_lookup names s.locals env cut
    have present : ∀ key, sptMem key names → sptMem key s.locals := by
      intro key member
      unfold DataSem.cutEnv at cut
      split at cut
      · rename_i all
        exact all key member
      · simp at cut
    have envWf : sptWf env = true := by
      unfold DataSem.cutEnv at cut
      split at cut
      · simp only [Option.some.injEq] at cut
        subst env
        exact sptWf_mkWf _
      · rename_i notAll
        exact absurd present notAll
    have envPresent : ∀ key, sptMem key names → sptMem key env := by
      intro key member
      have h := present key member
      simp only [sptMem, sptDomain] at h ⊢
      rw [lookup key, if_pos (by simpa [sptMem, sptDomain] using member)]
      exact h
    refine ⟨env, ?_, rfl⟩
    simp only [DataSem.cutEnv, if_pos envPresent, Option.some.injEq]
    apply (sptEqThm _ _ ⟨sptWf_mkWf _, envWf⟩).mpr
    intro key
    rw [sptLookup_mkWf, sptLookup_sptInterCases, lookup key]
    cases hn : sptLookup key names <;> cases hl : sptLookup key s.locals <;>
      simp [sptMem, sptDomain, hn]

/-- Cutting a state preserves its frame and local sizes. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "cut_state_opt_extra_const"]
theorem cutStateOpt_extraConst {C F : Type} (namesOpt : Option NumSet) (s x : DataSem.State C F) :
    DataSem.cutStateOpt namesOpt s = some x →
      s.stackFrameSizes = x.stackFrameSizes ∧ s.localsSize = x.localsSize := by
  cases namesOpt with
  | none => intro h; cases h; exact ⟨rfl, rfl⟩
  | some names =>
    intro h
    simp only [DataSem.cutStateOpt, DataSem.cutState, Option.map_eq_some_iff] at h
    obtain ⟨env, _, rfl⟩ := h
    exact ⟨rfl, rfl⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
