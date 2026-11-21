module

public import Flapjack.Misc.Multiword.Mc.Correct.IDiv

@[expose] public section

/-! Correctness of the machine-code-style integer operation entry point of
HOL's `mc_multiword`, ending with HOL's exported `mc_iop_thm`. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- Flapjack proof of the local HOL lemma `NumABS_LEMMA`, in the form used by
`i2mw`. -/
theorem i2mw_zero_one {width : Nat} [NeZero width] :
    (i2mw 0 : Bool × List (BitVec width)) = (false, []) ∧
      (i2mw 1 : Bool × List (BitVec width)) = (false, [1]) := by
  refine ⟨?_, ?_⟩
  · simp [i2mw, n2mw]
  · simp only [i2mw]
    rw [show (1 : Int).natAbs = 1 from rfl, n2mw_1]
    simp

/-- Flapjack proof of the local HOL lemma `mc_full_cmp_lt`. -/
theorem mcFullCmp_lt {width : Nat} [NeZero width] {s t : Bool} {xs ys zs : List (BitVec width)}
    {l : Nat} :
    ((mcHeader (s, xs) = 0) ↔ xs = []) ∧ mwOk xs ∧ ((mcHeader (t, ys) = 0) ↔ ys = []) ∧
    mwOk ys ∧ xs.length < 2 ^ width / 2 ∧ ys.length < 2 ^ width / 2 ∧
    xs.length + ys.length < zs.length ∧ zs.length < 2 ^ width / 2 ∧ xs.length + 1 ≤ l →
    ∃ zs1 l2,
      mcFullCmpPre (l, 2, mcHeader (s, xs), mcHeader (t, ys), xs, ys, zs) ∧
      mcFullCmp (l, 2, mcHeader (s, xs), mcHeader (t, ys), xs, ys, zs) =
        (l2, mcHeader (mwiOp .lt (s, xs) (t, ys)), xs, ys, (mwiOp .lt (s, xs) (t, ys)).2 ++ zs1) ∧
      ((mwiOp .lt (s, xs) (t, ys)).2 ++ zs1).length = zs.length ∧
      l ≤ l2 + xs.length + 1 := by
  rintro ⟨-, -, -, -, hx, hy, hz, hzw, hl⟩
  have w4 : 4 ≤ 2 ^ width := by omega
  have ne2 : (2 : BitVec width) ≠ 1 := by
    intro h; have := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt (show 2 < 2 ^ width by omega),
      Nat.mod_eq_of_lt (show 1 < 2 ^ width by omega)] at this
  have ne20 : (2 : BitVec width) ≠ 0 := by
    intro h; have := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt (show 2 < 2 ^ width by omega)] at this
  have ne10 : (1 : BitVec width) ≠ 0 := by simp [NeZero.ne]
  obtain ⟨l2, pre, eq, bound⟩ := mcIcompare_thm (s := s) (t := t) (xs := xs) (ys := ys) (l := l)
    ⟨hx, hy, hl⟩
  obtain ⟨z, zs', rfl⟩ : ∃ z zs', zs = z :: zs' := by
    cases zs with
    | nil => simp at hz
    | cons a b => exact ⟨a, b, rfl⟩
  rw [mcFullCmpPre_def, mcFullCmp_def]
  simp only [eq, mcIcmpRes_def, if_true]
  simp only [mwiOp, mwiLt]
  obtain ⟨c, hc⟩ : ∃ c, mwiCompare (s, xs) (t, ys) = c := ⟨_, rfl⟩
  simp only [hc]
  rcases c with _ | _ | _
  · simp only [cmp2w, reduceCtorEq, ne10.symm, ↓reduceIte, i2mw_zero_one.1]
    refine ⟨z :: zs', l2, pre, ?_, by simp, bound⟩
    simp [mcHeader]
  · simp only [cmp2w, ne2, ↓reduceIte]
    refine ⟨z :: zs', l2, pre, ?_, by simp [i2mw, n2mw], bound⟩
    simp [mcHeader, i2mw, n2mw]
  · simp only [cmp2w, if_true, ne10, if_false, i2mw_zero_one.2]
    refine ⟨zs', l2, ⟨pre, by simp⟩, ?_, by simp, bound⟩
    simp [mcHeader]

/-- Comparison for equality (HOL's local `mc_full_cmp_eq`). -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_full_cmp_eq"
  (words_as_type_indexed_bitvec)]
theorem mcFullCmp_eq {width : Nat} [NeZero width] {s t : Bool} {xs ys zs : List (BitVec width)}
    {l : Nat} :
    ((mcHeader (s, xs) = 0) ↔ xs = []) ∧ mwOk xs ∧ ((mcHeader (t, ys) = 0) ↔ ys = []) ∧
    mwOk ys ∧ xs.length < 2 ^ width / 2 ∧ ys.length < 2 ^ width / 2 ∧
    xs.length + ys.length < zs.length ∧ zs.length < 2 ^ width / 2 ∧ xs.length + 1 ≤ l →
    ∃ zs1 l2,
      mcFullCmpPre (l, 3, mcHeader (s, xs), mcHeader (t, ys), xs, ys, zs) ∧
      mcFullCmp (l, 3, mcHeader (s, xs), mcHeader (t, ys), xs, ys, zs) =
        (l2, mcHeader (mwiOp .eq (s, xs) (t, ys)), xs, ys, (mwiOp .eq (s, xs) (t, ys)).2 ++ zs1) ∧
      ((mwiOp .eq (s, xs) (t, ys)).2 ++ zs1).length = zs.length ∧
      l ≤ l2 + xs.length + 1 := by
  rintro ⟨-, -, -, -, hx, hy, hz, hzw, hl⟩
  have w4 : 4 ≤ 2 ^ width := by omega
  have ne32 : (3 : BitVec width) ≠ 2 := by
    intro h; have := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt (show 2 < 2 ^ width by omega),
      Nat.mod_eq_of_lt (show 3 < 2 ^ width by omega)] at this
  have ne20 : (2 : BitVec width) ≠ 0 := by
    intro h; have := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt (show 2 < 2 ^ width by omega)] at this
  have ne10 : (1 : BitVec width) ≠ 0 := by simp [NeZero.ne]
  obtain ⟨l2, pre, eq, bound⟩ := mcIcompare_thm (s := s) (t := t) (xs := xs) (ys := ys) (l := l)
    ⟨hx, hy, hl⟩
  obtain ⟨z, zs', rfl⟩ : ∃ z zs', zs = z :: zs' := by
    cases zs with
    | nil => simp at hz
    | cons a b => exact ⟨a, b, rfl⟩
  rw [mcFullCmpPre_def, mcFullCmp_def]
  simp only [eq, mcIcmpRes_def, ne32, if_false]
  simp only [mwiOp, mwiEq]
  obtain ⟨c, hc⟩ : ∃ c, mwiCompare (s, xs) (t, ys) = c := ⟨_, rfl⟩
  simp only [hc]
  rcases c with _ | _ | _
  · simp only [cmp2w, if_true, ne10, if_false, i2mw_zero_one.2]
    refine ⟨zs', l2, ⟨pre, by simp⟩, ?_, by simp, bound⟩
    simp [mcHeader]
  · simp only [cmp2w, reduceCtorEq, ne20, ↓reduceIte, i2mw_zero_one.1]
    refine ⟨z :: zs', l2, pre, ?_, by simp, bound⟩
    simp [mcHeader]
  · simp only [cmp2w, reduceCtorEq, ne10, ↓reduceIte, i2mw_zero_one.1]
    refine ⟨z :: zs', l2, pre, ?_, by simp, bound⟩
    simp [mcHeader]

/-- Flapjack proof of the local HOL lemma `mc_header_XOR_1`. -/
theorem mcHeader_XOR_1 {width : Nat} [NeZero width] {s : Bool} {xs : List (BitVec width)} :
    mcHeader (s, xs) ^^^ 1 = mcHeader (!s, xs) := by
  have h1 : (1 : Nat) < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
  have ev : ¬ (BitVec.ofNat width (xs.length * 2)).getLsbD 0 = true := by
    rw [BitVec.getLsbD, Nat.testBit_zero, BitVec.toNat_ofNat]
    have dvd : 2 ∣ 2 ^ width := dvd_pow_self 2 (NeZero.ne width)
    rw [Nat.mod_mod_of_dvd _ dvd]
    simp
  cases s
  · simp only [mcHeader, Bool.false_eq_true, if_false, Bool.not_false, if_true]
    have z : BitVec.ofNat width (xs.length * 2) + 0 = BitVec.ofNat width (xs.length * 2) := by
      simp
    rw [z, xor_one_add_one ev]
  · simp only [mcHeader, if_true, Bool.not_true, Bool.false_eq_true, if_false]
    have z : BitVec.ofNat width (xs.length * 2) + 0 = BitVec.ofNat width (xs.length * 2) := by
      simp
    rw [z, add_one_xor_one ev]

/-- The machine-code-style integer operation computes HOL's `mwi_op` for the
arithmetic operations (HOL's `mc_iop_thm`). -/
@[hol "HOL/examples/machine-code/multiword/mc_multiwordScript.sml" "mc_iop_thm"
  (words_as_type_indexed_bitvec)]
theorem mcIop_thm {width : Nat} [NeZero width] {s t : Bool} {xs ys zs : List (BitVec width)}
    {iop : MwOp} {l : Nat} :
    3 < width →
      ((mcHeader (s, xs) = 0) ↔ xs = []) ∧ mwOk xs ∧ ((mcHeader (t, ys) = 0) ↔ ys = []) ∧
      mwOk ys ∧ xs.length + ys.length < zs.length ∧ zs.length < 2 ^ width / 2 ∧
      iop ≠ .lt ∧ iop ≠ .eq ∧ iop ≠ .dec ∧ (iop = .div ∨ iop = .mod → ys ≠ []) ∧
      mcDivMax xs ys zs + 2 * zs.length + 2 ≤ l →
      ∃ zs1 l2,
        mcIopPre (l, mcHeader (s, xs), mcHeader (t, ys), intOpRep iop, xs, ys, zs) ∧
        mcIop (l, mcHeader (s, xs), mcHeader (t, ys), intOpRep iop, xs, ys, zs) =
          (l2, mcHeader (mwiOp iop (s, xs) (t, ys)), xs, ys, (mwiOp iop (s, xs) (t, ys)).2 ++ zs1) ∧
        ((mwiOp iop (s, xs) (t, ys)).2 ++ zs1).length = zs.length ∧
        l ≤ l2 + mcDivMax xs ys zs + 2 * zs.length + 2 := by
  intro hw ⟨h0x, okx, h0y, oky, hz, hzw, hlt, heq, hdec, hdy, hl⟩
  have w16 : 16 ≤ 2 ^ width :=
    calc 16 = 2 ^ 4 := rfl
      _ ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) (by omega)
  have tn : ∀ k : Nat, k < 16 → (BitVec.ofNat width k).toNat = k :=
    fun k hk => ofNat_toNat_of_lt (by omega)
  have hx : xs.length < 2 ^ width / 2 := by omega
  have hy : ys.length < 2 ^ width / 2 := by omega
  have K : xs.length * ys.length ≤ xs.length * (2 ^ width + 2 * ys.length + 4) :=
    Nat.mul_le_mul_left _ (by omega)
  have hmax : mcDivMax xs ys zs =
      2 * ys.length + 2 * zs.length + 5 + width +
        xs.length * (2 ^ width + 2 * ys.length + 4) := rfl
  have lt2 : ∀ k : Nat, k < 16 → (BitVec.ofNat width k < (2 : BitVec width) ↔ k < 2) := by
    intro k hk
    rw [show (2 : BitVec width) = BitVec.ofNat width 2 from rfl,
      ofNat_lt_ofNat (by omega) (by omega)]
  have eqk : ∀ a b : Nat, a < 16 → b < 16 →
      (BitVec.ofNat width a = BitVec.ofNat width b ↔ a = b) :=
    fun a b ha hb => ofNat_inj (by omega) (by omega)
  cases iop with
  | lt => exact absurd rfl hlt
  | eq => exact absurd rfl heq
  | dec => exact absurd rfl hdec
  | add =>
    have c0 : (0 : BitVec width) < 2 := (lt2 0 (by decide)).mpr (by decide)
    obtain ⟨zs1, l2, pre, eq, len, bound⟩ :=
      mcIadd_thm (s := s) (t := t) (xs := xs) (ys := ys) (zs := zs) (l := l)
        ⟨hx, hy, by omega, okx, oky, by omega⟩
    refine ⟨zs1, l2, ?_, ?_, len, by omega⟩
    · rw [mcIopPre_def]; simp only [intOpRep, c0, if_true, mcIsubFlip_def]; exact pre
    · rw [mcIop_def]; simp only [intOpRep, c0, if_true, mcIsubFlip_def, eq, mwiOp]
  | sub =>
    have c1 : (1 : BitVec width) < 2 := (lt2 1 (by decide)).mpr (by decide)
    have n10 : (1 : BitVec width) ≠ 0 := by simp [NeZero.ne]
    obtain ⟨zs1, l2, pre, eq, len, bound⟩ :=
      mcIadd_thm (s := s) (t := !t) (xs := xs) (ys := ys) (zs := zs) (l := l)
        ⟨hx, hy, by omega, okx, oky, by omega⟩
    refine ⟨zs1, l2, ?_, ?_, by simpa [mwiOp, mwiSub] using len, by omega⟩
    · rw [mcIopPre_def]
      simp only [intOpRep, c1, if_true, mcIsubFlip_def, n10, if_false, mcHeader_XOR_1]
      exact pre
    · rw [mcIop_def]
      simp only [intOpRep, c1, if_true, mcIsubFlip_def, n10, if_false, mcHeader_XOR_1, eq,
        mwiOp, mwiSub]
  | mul =>
    have c4 : ¬ (4 : BitVec width) < 2 := by
      rw [show (4 : BitVec width) = BitVec.ofNat width 4 from rfl, lt2 4 (by decide)]; decide
    obtain ⟨zs1, l2, pre, eq, len, bound⟩ :=
      mcImul_thm (s := s) (t := t) (xs := xs) (ys := ys) (zs := zs) (l := l)
        ⟨h0x, h0y, hx, hy, by omega, hzw, by omega⟩
    refine ⟨zs1, l2, ?_, ?_, len, by omega⟩
    · rw [mcIopPre_def]; simp only [intOpRep, c4, if_false, if_true]; exact pre
    · rw [mcIop_def]; simp only [intOpRep, c4, if_false, if_true, eq, mwiOp]
  | div =>
    have c5 : ¬ (5 : BitVec width) < 2 := by
      rw [show (5 : BitVec width) = BitVec.ofNat width 5 from rfl, lt2 5 (by decide)]; decide
    have n54 : (5 : BitVec width) ≠ 4 := by
      rw [show (5 : BitVec width) = BitVec.ofNat width 5 from rfl,
        show (4 : BitVec width) = BitVec.ofNat width 4 from rfl, Ne,
        eqk 5 4 (by decide) (by decide)]; decide
    have s55 : (5 : BitVec width) - 5 = 0 := by simp
    obtain ⟨zs1, l2, pre, eq, len, bound⟩ :=
      mcIdiv_thm (s := s) (t := t) (xs := xs) (ys := ys) (zs := zs) (r3 := 0) (l := l)
        ⟨by omega, hzw, okx, oky, hdy (Or.inl rfl), hl⟩
    simp only [mwiDivmodAlt, if_true] at eq len
    refine ⟨zs1, l2, ?_, ?_, len, bound⟩
    · rw [mcIopPre_def]; simp only [intOpRep, c5, n54, if_false, s55]; exact pre
    · rw [mcIop_def]; simp only [intOpRep, c5, n54, if_false, s55, eq, mwiOp]
  | mod =>
    have c6 : ¬ (6 : BitVec width) < 2 := by
      rw [show (6 : BitVec width) = BitVec.ofNat width 6 from rfl, lt2 6 (by decide)]; decide
    have n64 : (6 : BitVec width) ≠ 4 := by
      rw [show (6 : BitVec width) = BitVec.ofNat width 6 from rfl,
        show (4 : BitVec width) = BitVec.ofNat width 4 from rfl, Ne,
        eqk 6 4 (by decide) (by decide)]; decide
    have s65 : (6 : BitVec width) - 5 = 1 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def, show (6 : BitVec width) = BitVec.ofNat width 6 from rfl,
          show (5 : BitVec width) = BitVec.ofNat width 5 from rfl, tn 6 (by decide),
          tn 5 (by decide)]; decide)]
      rw [show (6 : BitVec width) = BitVec.ofNat width 6 from rfl,
        show (5 : BitVec width) = BitVec.ofNat width 5 from rfl,
        show (1 : BitVec width) = BitVec.ofNat width 1 from rfl, tn 6 (by decide),
        tn 5 (by decide), tn 1 (by decide)]
    have n10 : (1 : BitVec width) ≠ 0 := by simp [NeZero.ne]
    obtain ⟨zs1, l2, pre, eq, len, bound⟩ :=
      mcIdiv_thm (s := s) (t := t) (xs := xs) (ys := ys) (zs := zs) (r3 := 1) (l := l)
        ⟨by omega, hzw, okx, oky, hdy (Or.inr rfl), hl⟩
    simp only [mwiDivmodAlt, n10, if_false] at eq len
    refine ⟨zs1, l2, ?_, ?_, len, bound⟩
    · rw [mcIopPre_def]; simp only [intOpRep, c6, n64, if_false, s65]; exact pre
    · rw [mcIop_def]; simp only [intOpRep, c6, n64, if_false, s65, eq, mwiOp]

end Flapjack.Misc.Multiword
