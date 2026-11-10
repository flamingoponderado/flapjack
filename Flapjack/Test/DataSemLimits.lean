module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Limits

@[expose] public section

/-! Data-language representation-limit boundaries. -/
namespace Flapjack.Test.DataSemLimits
open Flapjack.Compiler.Backend
open DataSem

private def limits : Limits := ⟨1000, 3, 1000, true, false, false⟩

example : limSafe limits (.memOp .refArray) [.number 7, .number 0] := by
  simp [limSafe, limits, archSize]

example : ¬limSafe limits (.memOp .refArray) [.number 8, .number 0] := by
  simp [limSafe, limits, archSize]

example : ¬limSafe limits (.memOp .refArray) [.number (-1), .number 0] := by
  simp [limSafe, limits, archSize]

/-- A malformed argument list uses the source's permissive fallback. -/
example : limSafe limits (.memOp .refArray) [.number (-1)] := by
  simp [limSafe]

example : ¬limSafe limits (.wordOp (.fpCmp .equal)) [] := by
  simp [limSafe, limits]

example : ¬limSafe limits (.blockOp (.cons (2 ^ 60))) [] := by
  simp [limSafe, limits, archSize]

example : limSafePart limits (.con 1 []) := by
  simp [limSafePart, limits, archSize]

end Flapjack.Test.DataSemLimits
