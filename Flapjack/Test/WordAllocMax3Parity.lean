import Flapjack.Compiler.Backend.WordAlloc.Proofs.Maximum.Max3

namespace Flapjack.Test.WordAllocMax3Parity

/-! Kernel replay of the nine original EVAL observations in
`word_alloc_max3_eq_probe.out`, plus the complete original universal statement. -/
example : ∀ (x y z : Nat), max3HOL x y z = max x (max y z) :=
  WordAlloc.max3Eq

example : max3HOL 0 0 0 = 0 := by decide +kernel
example : max3HOL 9 4 2 = 9 := by decide +kernel
example : max3HOL 2 9 4 = 9 := by decide +kernel
example : max3HOL 4 2 9 = 9 := by decide +kernel
example : max3HOL 2 4 9 = 9 := by decide +kernel
example : max3HOL 9 9 2 = 9 := by decide +kernel
example : max3HOL 9 2 9 = 9 := by decide +kernel
example : max3HOL 2 9 9 = 9 := by decide +kernel
example : max3HOL 18446744073709551617 9 18446744073709551616 =
    18446744073709551617 := by decide +kernel

end Flapjack.Test.WordAllocMax3Parity
