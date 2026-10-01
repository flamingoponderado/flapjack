import Flapjack.Compiler.Backend.WordAlloc.Proofs.LimitVar.Arithmetic

namespace Flapjack.Test.WordAllocLimitArithmeticParity

open Flapjack Flapjack.Compiler.Backend.WordAlloc

/-- Apply the actual unconditional arithmetic infrastructure, with no bound on
register IDs and no premise about a native program or allocation result. -/
example (maximum : Nat) :
    isAllocVar (maximum + (4 - maximum % 4) + 1) ∧
      maximum < maximum + (4 - maximum % 4) + 1 := limitVarArithmetic maximum

example (maximum : Nat) : (maximum + (4 - maximum % 4)) % 4 = 0 :=
  limitVarMultiple maximum

/-- Fresh original `la_0`: result, native class, strict bound and alignment. -/
example : let maximum := 0
    (maximum + (4 - maximum % 4) + 1, isAllocVar (maximum + (4 - maximum % 4) + 1),
      decide (maximum < maximum + (4 - maximum % 4) + 1), (maximum + (4 - maximum % 4)) % 4) =
      (5, true, true, 0) := by decide +kernel

/-- Fresh original `la_1`: result, native class, strict bound and alignment. -/
example : let maximum := 1
    (maximum + (4 - maximum % 4) + 1, isAllocVar (maximum + (4 - maximum % 4) + 1),
      decide (maximum < maximum + (4 - maximum % 4) + 1), (maximum + (4 - maximum % 4)) % 4) =
      (5, true, true, 0) := by decide +kernel

/-- Fresh original `la_2`: result, native class, strict bound and alignment. -/
example : let maximum := 2
    (maximum + (4 - maximum % 4) + 1, isAllocVar (maximum + (4 - maximum % 4) + 1),
      decide (maximum < maximum + (4 - maximum % 4) + 1), (maximum + (4 - maximum % 4)) % 4) =
      (5, true, true, 0) := by decide +kernel

/-- Fresh original `la_3`: result, native class, strict bound and alignment. -/
example : let maximum := 3
    (maximum + (4 - maximum % 4) + 1, isAllocVar (maximum + (4 - maximum % 4) + 1),
      decide (maximum < maximum + (4 - maximum % 4) + 1), (maximum + (4 - maximum % 4)) % 4) =
      (5, true, true, 0) := by decide +kernel

/-- Fresh original `la_4`: result, native class, strict bound and alignment. -/
example : let maximum := 4
    (maximum + (4 - maximum % 4) + 1, isAllocVar (maximum + (4 - maximum % 4) + 1),
      decide (maximum < maximum + (4 - maximum % 4) + 1), (maximum + (4 - maximum % 4)) % 4) =
      (9, true, true, 0) := by decide +kernel

/-- Fresh original `la_7`: result, native class, strict bound and alignment. -/
example : let maximum := 7
    (maximum + (4 - maximum % 4) + 1, isAllocVar (maximum + (4 - maximum % 4) + 1),
      decide (maximum < maximum + (4 - maximum % 4) + 1), (maximum + (4 - maximum % 4)) % 4) =
      (9, true, true, 0) := by decide +kernel

/-- Fresh original `la_8`: result, native class, strict bound and alignment. -/
example : let maximum := 8
    (maximum + (4 - maximum % 4) + 1, isAllocVar (maximum + (4 - maximum % 4) + 1),
      decide (maximum < maximum + (4 - maximum % 4) + 1), (maximum + (4 - maximum % 4)) % 4) =
      (13, true, true, 0) := by decide +kernel

/-- Fresh original `la_15`: result, native class, strict bound and alignment. -/
example : let maximum := 15
    (maximum + (4 - maximum % 4) + 1, isAllocVar (maximum + (4 - maximum % 4) + 1),
      decide (maximum < maximum + (4 - maximum % 4) + 1), (maximum + (4 - maximum % 4)) % 4) =
      (17, true, true, 0) := by decide +kernel

/-- Fresh original `la_16`: result, native class, strict bound and alignment. -/
example : let maximum := 16
    (maximum + (4 - maximum % 4) + 1, isAllocVar (maximum + (4 - maximum % 4) + 1),
      decide (maximum < maximum + (4 - maximum % 4) + 1), (maximum + (4 - maximum % 4)) % 4) =
      (21, true, true, 0) := by decide +kernel

/-- Fresh original `la_1208925819614629174706176`: result, native class, strict bound and alignment. -/
example : let maximum := 1208925819614629174706176
    (maximum + (4 - maximum % 4) + 1, isAllocVar (maximum + (4 - maximum % 4) + 1),
      decide (maximum < maximum + (4 - maximum % 4) + 1), (maximum + (4 - maximum % 4)) % 4) =
      (1208925819614629174706181, true, true, 0) := by decide +kernel

/-- Fresh original `la_1208925819614629174706177`: result, native class, strict bound and alignment. -/
example : let maximum := 1208925819614629174706177
    (maximum + (4 - maximum % 4) + 1, isAllocVar (maximum + (4 - maximum % 4) + 1),
      decide (maximum < maximum + (4 - maximum % 4) + 1), (maximum + (4 - maximum % 4)) % 4) =
      (1208925819614629174706181, true, true, 0) := by decide +kernel

/-- Fresh original `la_1208925819614629174706178`: result, native class, strict bound and alignment. -/
example : let maximum := 1208925819614629174706178
    (maximum + (4 - maximum % 4) + 1, isAllocVar (maximum + (4 - maximum % 4) + 1),
      decide (maximum < maximum + (4 - maximum % 4) + 1), (maximum + (4 - maximum % 4)) % 4) =
      (1208925819614629174706181, true, true, 0) := by decide +kernel

/-- Fresh original `la_1208925819614629174706179`: result, native class, strict bound and alignment. -/
example : let maximum := 1208925819614629174706179
    (maximum + (4 - maximum % 4) + 1, isAllocVar (maximum + (4 - maximum % 4) + 1),
      decide (maximum < maximum + (4 - maximum % 4) + 1), (maximum + (4 - maximum % 4)) % 4) =
      (1208925819614629174706181, true, true, 0) := by decide +kernel

end Flapjack.Test.WordAllocLimitArithmeticParity
