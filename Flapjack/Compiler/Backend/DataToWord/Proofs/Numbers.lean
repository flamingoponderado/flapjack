import Flapjack.Compiler.Backend.DataToWord.Numbers
import Flapjack.Misc.Multiword

/-! Agreement with Flapjack's former executable immediate-integer encoding. -/
namespace Flapjack.Compiler.Backend.DataToWord

/-- Flapjack-specific equivalence with the previously inlined compiler formula;
it holds for every integer and positive width, not only for small integers. -/
theorem smallnum_eq_inlined {width : Nat} [NeZero width] (i : Int) :
    smallnum (width := width) i =
      (if i < 0 then -(BitVec.ofNat width (4 * i.natAbs)) else BitVec.ofNat width (4 * i.natAbs)) := by
  cases i with
  | ofNat n =>
      have h : ¬ ((n : Int) < 0) := Int.not_lt.mpr (Int.natCast_nonneg n)
      simp [smallnum, h, Int.natAbs, Int.toNat_mul (a := 4) (b := (n : Int)) (by decide) (Int.natCast_nonneg n)]
  | negSucc n =>
      have h : Int.negSucc n < 0 := by omega
      have hn : 0 ≤ (n : Int) + 1 := by omega
      simp [smallnum, h, Int.natAbs, Int.toNat_mul (a := 4) (b := (n : Int) + 1) (by decide) hn]

/-- The previously executed bounded digit traversal, retained as the left
side of the compiler-agreement theorem. -/
private def oldDigits {width : Nat} (fuel n : Nat) : List (BitVec width) :=
  match fuel with
  | 0 => []
  | fuel + 1 => if n == 0 then [] else
      BitVec.ofNat width (n % (2 ^ width)) :: oldDigits fuel (n / (2 ^ width))

/-- Flapjack-specific agreement with the former bounded compiler traversal.
Its original fuel is `n + 1`, which satisfies this sufficient bound. -/
theorem oldDigits_eq_n2mw {width : Nat} [NeZero width] (fuel n : Nat) (bound : n < fuel) :
    oldDigits (width := width) fuel n = Misc.Multiword.n2mw n := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
      by_cases hn : n = 0
      · subst n; simp [oldDigits, Misc.Multiword.n2mw]
      · have hnPos : 0 < n := by omega
        have quotient : n / 2 ^ width < n := Nat.div_lt_self hnPos (Nat.one_lt_two_pow (NeZero.ne width))
        have next : n / 2 ^ width < fuel := by omega
        simp only [oldDigits, beq_iff_eq, hn, ↓reduceIte]
        rw [Misc.Multiword.n2mw]
        simp only [hn, ↓reduceIte]
        rw [ih _ next]

end Flapjack.Compiler.Backend.DataToWord
