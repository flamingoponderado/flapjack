import Flapjack.Misc.Multiword

/-! Length properties of the HOL multiword encoding. -/
namespace Flapjack.Misc.Multiword

/-- Increasing a natural number cannot shorten its multiword representation. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "LENGTH_n2mw_LESS_LENGTH_n2mw"
  (words_as_type_indexed_bitvec)]
theorem n2mw_length_mono {width : Nat} [NeZero width] (m n : Nat) :
    m ≤ n → (n2mw m : List (BitVec width)).length ≤ (n2mw n : List (BitVec width)).length := by
  have eqZero : n2mw (width := width) 0 = [] := by rw [n2mw]; rfl
  induction n using Nat.strongRecOn generalizing m with
  | ind n ih =>
    intro bound
    by_cases zeroN : n = 0
    · have : m = 0 := by omega
      subst m
      simp only [eqZero, List.length_nil, Nat.zero_le]
    · by_cases zeroM : m = 0
      · subst m
        simp only [eqZero, List.length_nil, Nat.zero_le]
      · have eqM : n2mw (width := width) m =
            BitVec.ofNat width (m % 2 ^ width) :: n2mw (m / 2 ^ width) := by
          rw [n2mw, if_neg zeroM]
        have eqN : n2mw (width := width) n =
            BitVec.ofNat width (n % 2 ^ width) :: n2mw (n / 2 ^ width) := by
          rw [n2mw, if_neg zeroN]
        rw [eqM, eqN]
        simp only [List.length_cons, Nat.succ_le_succ_iff]
        apply ih (n / 2 ^ width)
        · exact Nat.div_lt_self (by omega) (Nat.one_lt_two_pow (NeZero.ne width))
        · exact Nat.div_le_div_right bound

end Flapjack.Misc.Multiword
