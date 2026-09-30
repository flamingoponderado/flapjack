import Flapjack.Pancake.LoopLang
import Flapjack.LoopSemantics

namespace Flapjack

/--
Flapjack-specific broad Nat arithmetic helper, not an exact HOL port.

HOL `loop_arith_def` LDiv uses signed fixed-width word_quot; this helper uses
unsigned unbounded Nat division and has no width binder. Its successful
positive examples do not establish signed-word correspondence. The exact
width-aware semantics live in Pancake/Semantics/LoopSemStateExact.lean.
-/
def loopArithDiv (destination dividend divisor : Nat) (locals : Nat → Option Nat) :
    Option (Nat → Option Nat) :=
  match locals divisor, locals dividend with
  | some q, some dividendValue =>
      if q = 0 then none
      else some (updateLoopLocal locals destination (dividendValue / q))
  | _, _ => none

/--
Faithful port of the `LLongMul` branch of `loop_arith`.

The original writes the high word first as an inner update and the low word as
the outer update, so the low word wins when both destinations coincide
(`loopSemScript.sml:127-132`).
-/
def loopArithLongMul (width destinationLeft destinationRight sourceLeft sourceRight : Nat)
    (locals : Nat → Option Nat) : Option (Nat → Option Nat) :=
  match locals sourceLeft, locals sourceRight with
  | some leftValue, some rightValue =>
      let base := 2 ^ width
      let product := leftValue * rightValue
      let withHigh := updateLoopLocal locals destinationLeft (product / base % base)
      some (updateLoopLocal withHigh destinationRight (product % base))
  | _, _ => none

/--
Faithful port of the `LLongDiv` branch of `loop_arith`.

The original writes the remainder as the inner update and the quotient as the
outer update, so the quotient wins when both destinations coincide.
-/
def loopArithLongDiv (width destinationLeft destinationRight sourceLeft sourceRight quotient :
    Nat) (locals : Nat → Option Nat) : Option (Nat → Option Nat) :=
  match locals sourceLeft, locals sourceRight, locals quotient with
  | some high, some low, some divisor =>
      let base := 2 ^ width
      let numerator := high * base + low
      let result := numerator / divisor
      if divisor ≠ 0 ∧ result < base then
        let withRemainder := updateLoopLocal locals destinationRight (numerator % divisor)
        some (updateLoopLocal withRemainder destinationLeft result)
      else none
  | _, _, _ => none

/-- Faithful port of `loop_arith` covering `LDiv`, `LLongMul`, and `LLongDiv`. -/
def loopArith (width : Nat) : LoopArith → (Nat → Option Nat) → Option (Nat → Option Nat)
  | .div destination dividend divisor, locals =>
      loopArithDiv destination dividend divisor locals
  | .longMul destinationLeft destinationRight sourceLeft sourceRight, locals =>
      loopArithLongMul width destinationLeft destinationRight sourceLeft sourceRight locals
  | .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient, locals =>
      loopArithLongDiv width destinationLeft destinationRight sourceLeft sourceRight quotient locals

theorem loopArithDiv_some_implies_divisor_nonzero
    (destination dividend divisor : Nat) (locals : Nat → Option Nat)
    (result : Nat → Option Nat)
    (heval : loopArithDiv destination dividend divisor locals = some result) :
    ∃ divisorValue, locals divisor = some divisorValue ∧ divisorValue ≠ 0 := by
  cases hdivisor : locals divisor with
  | none =>
      simp [loopArithDiv, hdivisor] at heval
  | some divisorValue =>
      cases hdividend : locals dividend with
      | none =>
          simp [loopArithDiv, hdivisor, hdividend] at heval
      | some dividendValue =>
          simp [loopArithDiv, hdivisor, hdividend] at heval
          refine ⟨divisorValue, rfl, ?_⟩
          exact heval.1

end Flapjack
