import Flapjack.Compiler.Backend.WordToStack.ProductionLocations

namespace Flapjack.Test.ProductionLocations
open Flapjack RiscV RiscV.CakeRegAlloc

/-! Kernel fixtures for actual operand locations. No HOL simulation or
executed lowering equivalence is asserted by these tests. -/
example : cakeColourLocation 3 5 4 = .register 2 := by rfl
example : cakeColourLocation 3 5 5 = .register 2 := by rfl
example : cakeColourLocation 3 5 6 = .stack 4 := by rfl
example : cakeColourLocation 3 5 14 = .stack 0 := by rfl
example : cakeColourLocation 3 0 30 = .stack 0 := by rfl

-- Repeated source names do not require an extra uniqueness premise.
example : lookupNatInfo 2
    (cakeColourWordSpillState 3 [2, 2] (.skip : WordProg (BitVec 64)) [(2, 2)]).locations =
      some (.register 2) := by
  rw [cakeColourWordSpillState_lookup]
  simp [wordProgVariables, CakeAlloc.totalColour, CakeAlloc.spDefault,
    cakeColourLocation]

-- Names outside parameters and the real final program stay absent.
example : lookupNatInfo 99
    (cakeColourWordSpillState 3 [2, 2] (.skip : WordProg (BitVec 64)) [(2, 2)]).locations =
      none := by
  rw [cakeColourWordSpillState_lookup]
  simp [wordProgVariables, wordProgReadVars, wordProgWriteVars]

example (k frame colour : Nat) :
    cakeColourLocation k frame colour =
      match Compiler.Backend.WordToStackRegFormat.formatVar k (some (colour / 2)) with
      | .inl register => .register register
      | .inr slot => .stack (frame - 1 - (slot - k)) :=
  cakeColourLocation_formatVar k frame colour

end Flapjack.Test.ProductionLocations
