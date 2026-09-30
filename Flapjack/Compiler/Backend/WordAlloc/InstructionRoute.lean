import Flapjack.Compiler.Backend.WordAlloc.Instructions

namespace Flapjack.WordAlloc

/-- Flapjack carrier embedding; the separate five-register primitive is absent
from the exact HOL asm carrier and handled explicitly by the executed route. -/
private def arithToHOL {α : Type u} : WordArith α → Option (WordLangArith α)
  | .longMul a b c d => some (.longMul a b c d)
  | .longDiv a b c d e => some (.longDiv a b c d e)
  | .addCarry _ _ _ _ _ => none
  | .cakeAddCarry a b c d => some (.addCarry a b c d)
  | .div a b c => some (.div a b c)
  | .binOp op a b c => some (.binop op a b c)
  | .shift op a b c => some (.shift op a b c)

private def arithFromHOL {α : Type u} : WordLangArith α → Option (WordArith α)
  | .longMul a b c d => some (.longMul a b c d)
  | .longDiv a b c d e => some (.longDiv a b c d e)
  | .addCarry a b c d => some (.cakeAddCarry a b c d)
  | .div a b c => some (.div a b c)
  | .binop op a b c => some (.binOp op a b c)
  | .shift op a b c => some (.shift op a b c)
  | .addOverflow _ _ _ _ => none
  | .subOverflow _ _ _ _ => none

/-- Execute the reviewed recursion for every shared arithmetic constructor.
Five-register AddCarry retains its distinct Flapjack semantics; it is not a
HOL four-register AddCarry port. -/
def applyColourArithExecutable {α : Type u} (f : Nat → Nat) (a : WordArith α) : WordArith α :=
  match a with
  | .addCarry a b c d e => .addCarry (f a) (f b) (f c) (f d) (f e)
  | _ => match arithToHOL a with
    | none => a
    | some exact => match applyColourInstCore f (.arith exact) with
      | .arith coloured => (arithFromHOL coloured).getD a
      | _ => a

/-- Production memory without an offset carries no word value, so its adapter
uses Unit; offset-bearing instructions retain their original word payload.
Both paths call the same generic recursion as the tagged instruction port. -/
def applyColourInstExecutable {α : Type u} (f : Nat → Nat) : WordInst α → WordInst α
  | .const r w => match applyColourInstCore f (.const r w) with
    | .const r w => .const r w
    | _ => .const r w
  | .arith a => .arith (applyColourArithExecutable f a)
  | .mem op r a => match applyColourInstCore f (.mem op r (.addr a ())) with
    | .mem op r (.addr a _) => .mem op r a
    | _ => .mem op r a
  | .memOffset op r a w => match applyColourInstCore f (.mem op r (.addr a w)) with
    | .mem op r (.addr a w) => .memOffset op r a w
    | _ => .memOffset op r a w

/-- All memory operators, including the two untouched 16-bit catchall cases,
retain precisely the registers returned by the reviewed recursion. -/
theorem applyColourInstExecutable_mem {α : Type u} (f : Nat → Nat)
    (op : WordMemOp) (r a : Nat) :
    applyColourInstExecutable (α := α) f (.mem op r a) =
      (match op with
      | .load16 | .store16 => .mem op r a
      | _ => .mem op (f r) (f a)) := by
  cases op <;> rfl

end Flapjack.WordAlloc
