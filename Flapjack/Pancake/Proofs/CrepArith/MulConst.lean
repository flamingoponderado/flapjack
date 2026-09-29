import Flapjack.Pancake.CrepArith
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
# crep_arith `mul_const` correctness over the exact carriers

Ports of `cakeml/pancake/crep_arithScript.sml`'s `dest_2exp_thm` and
`cakeml/pancake/proofs/crep_arithProofScript.sml`'s `dest_2exp_bound`,
`dest_2exp_bound'` and `eval_mul_const` over the tagged exact
`crepDest2ExpHOL` (`dest_2exp_def`), `crepMulConstHOL` (`mul_const_def`) and
`evalCrepSemHOLExp` (crepSem `eval_def`), with HOL's `'a word` as `BitVec width`
(bead `flapjack-pxn.18.5.4.6`).  The script-level `dest_2exp_lemma` and
`dest_2exp_thm` live beside `dest_2exp_def` in `Flapjack/Pancake/CrepArith.lean`.
-/

namespace Flapjack

namespace CrepArithMulConstFiniteSupport

/-- Same-module canonical witness for the Crep state's finite-support
    translation used by the `eval_mul_const` qualifier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end CrepArithMulConstFiniteSupport

/-- HOL `words$word_log2 w = n2w (LOG2 (w2n w))` (HOL library, outside the CakeML
    submodule, so untagged).  `Nat.log2` agrees with HOL `LOG2` on the positive
    arguments at which the theorems below use it. -/
def holWordLog2 {width : Nat} (w : BitVec width) : BitVec width :=
  BitVec.ofNat width (Nat.log2 w.toNat)

/-- A successful `dest_2exp` has a nonzero argument. -/
private theorem crepDest2ExpHOL_ne_zero {width : Nat} [NeZero width] {i : Nat}
    {w : BitVec width} {n : Nat} (h : crepDest2ExpHOL i w = some n) : w ≠ 0 := by
  intro h0
  rw [crepDest2ExpHOL, if_pos h0] at h
  cases h

/-- The exponent of a successful `dest_2exp` is below the width, and the
    argument is exactly `2 ^ (n - i)`. -/
private theorem crepDest2ExpHOL_value {width : Nat} [NeZero width] {i : Nat}
    {w : BitVec width} {n : Nat} (h : crepDest2ExpHOL i w = some n) :
    i ≤ n ∧ n - i < width ∧ w.toNat = 2 ^ (n - i) := by
  obtain ⟨hle, hw⟩ := crepDest2ExpHOL_lemma i w n h
  have hne := crepDest2ExpHOL_ne_zero h
  have hw1 : 1 < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
  have hone : (1 : BitVec width).toNat = 1 := by
    show (BitVec.ofNat width 1).toNat = 1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw1]
  have hwn : w.toNat = 2 ^ (n - i) % 2 ^ width := by
    rw [hw, BitVec.toNat_shiftLeft, hone, Nat.shiftLeft_eq, Nat.one_mul]
  have hlt : n - i < width := by
    rcases Nat.lt_or_ge (n - i) width with hl | hge
    · exact hl
    · have : 2 ^ (n - i) % 2 ^ width = 0 :=
        Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 hge)
      rw [this] at hwn
      exact absurd (BitVec.eq_of_toNat_eq (by simpa using hwn)) hne
  refine ⟨hle, hlt, ?_⟩
  rw [hwn, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hlt)]

/-- Exact HOL `dest_2exp_bound` (`crep_arithProofScript.sml:10-38`):
    `∀n w m. dest_2exp n w = SOME m ⇒ m ≤ n + w2n (word_log2 w)`. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "dest_2exp_bound"
  (words_as_type_indexed_bitvec)]
theorem crepDest2ExpHOL_bound {width : Nat} [NeZero width] :
    ∀ (n : Nat) (w : BitVec width) (m : Nat), crepDest2ExpHOL n w = some m →
      m ≤ n + (holWordLog2 w).toNat := by
  intro n w m h
  obtain ⟨hle, hlt, hval⟩ := crepDest2ExpHOL_value h
  have hlog : (holWordLog2 w).toNat = m - n := by
    rw [holWordLog2, hval, Nat.log2_two_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    exact Nat.lt_trans hlt (Nat.lt_two_pow_self (n := width))
  rw [hlog]; omega

/-- Exact HOL `dest_2exp_bound'` (`crep_arithProofScript.sml:40-62`):
    `∀n w m. dest_2exp 0 w = SOME m ⇒ m < dimindex(:'a)` (HOL's unused binder
    `n` is kept). -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "dest_2exp_bound'"
  (words_as_type_indexed_bitvec)]
theorem crepDest2ExpHOL_bound' {width : Nat} [NeZero width] :
    ∀ (_n : Nat) (w : BitVec width) (m : Nat), crepDest2ExpHOL 0 w = some m → m < width := by
  intro _ w m h
  simpa using (crepDest2ExpHOL_value h).2.1

/-- Exact HOL `eval_mul_const` (`crep_arithProofScript.sml:70-91`):
    `eval s exp = SOME (Word w) ⇒ eval s (mul_const exp c) = SOME (Word (w * c))`,
    over the exact Crep evaluator (crepSem `eval_def`). -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "eval_mul_const"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem crepEval_mul_const {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) (exp : CrepExpHOL width) (w c : BitVec width),
      evalCrepSemHOLExp s exp = some (.word w) →
      evalCrepSemHOLExp s (crepMulConstHOL exp c) = some (.word (w * c)) := by
  intro s exp w c h
  unfold crepMulConstHOL
  by_cases hc0 : c = 0
  · subst hc0; simp [evalCrepSemHOLExp]
  rw [if_neg hc0]
  by_cases hc1 : c = 1
  · subst hc1; simpa using h
  rw [if_neg hc1]
  cases hd : crepDest2ExpHOL 0 c with
  | none => simp [evalCrepSemHOLExp, h, crepOpCrepWord]
  | some i =>
    obtain ⟨_, hlt, hval⟩ := crepDest2ExpHOL_value hd
    have hi : (BitVec.ofNat width i).toNat = i := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      exact Nat.lt_trans (by simpa using hlt) (Nat.lt_two_pow_self (n := width))
    simp only [Nat.sub_zero] at hval hlt
    have hmul : w <<< i = w * c := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_mul, Nat.shiftLeft_eq, hval]
    have hnot : ¬ (i ≠ 0 ∧ width ≤ i) := by omega
    simp [evalCrepSemHOLExp, h, hi, wordShiftHOL, hnot, hmul]
end Flapjack
