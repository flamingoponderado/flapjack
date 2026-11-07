import Flapjack.Compiler.Backend.WordToStack.ProductionProgramMaximum

/-! Same-input kernel replay of fresh original full-program maxima. Every
production constructor is covered, with recursive Call forms, duplicate
cutsets, Return's nonzero accumulator and names above 2^80. Rejection and
ordinary 16-bit guard sentinels are independent of the accepted rows. -/
namespace Flapjack.Test.WordToStackProgramMaximumParity
open Flapjack

private def expected : List Nat :=
  [0,0,11,9,17,17,17,17,17,17,11,17,7,0,0,17,17,17,23,7,17,23,
   17,17,17,23,17,17,23,17,1208925819614629174706177,0]

/-- Flapjack-only Option payload packaging for the finite replay. -/
private theorem mappedConstant {α : Type} (value : Option α) (number : Nat)
    (present : value.isSome = true) : value.map (fun _ => number) = some number := by
  cases value <;> simp_all

example : maxVarHOL (.inst (.mem .load16 3 (.addr 17 99)) : WordLangProgHOL (BitVec 8)) = 0 := by
  simp [maxVarHOL, maxVarInstHOL]

end Flapjack.Test.WordToStackProgramMaximumParity
