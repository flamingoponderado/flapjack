import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Compiler.Backend.Semantics.WordSem.State

/-! Source-matched CodeBufferWrite/DataBufferWrite clauses of
stackSemScript.sml evaluate_def:928-944. This is a partial dispatch helper, not
a second evaluator: the outer NONE means this module does not handle the
constructor, so it never substitutes Error for an unported clause. The
CodeBufferWrite clause reads two Word registers and calls the exact
`wordSemScript.sml` `buffer_write_def` port `wordSemBufferWrite`, truncating the
byte with `w2w`; the DataBufferWrite clause additionally enforces `use_stack`.
No HOL tag applies to this extra Option-shaped fragment; the total evaluator is
assembled in Evaluate.lean. -/

namespace Flapjack.StackSemBufferWrites
open StackSemStateOps
open Compiler.Backend.StackLang

/-- The HOL `evaluate (CodeBufferWrite r1 r2, s)` and
`evaluate (DataBufferWrite r1 r2, s)` branches. Both reject non-Word operands
and a `buffer_write` miss with `Error` and the original state; DataBufferWrite
rejects `use_stack = F` first. -/
def evaluateBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (s : StackSemStateFiniteExact width C F) :
    Option (Option (StackSemResult width) × StackSemStateFiniteExact width C F) :=
  match program with
  | .codeBufferWrite r1 r2 =>
      some (match getVar r1 s, getVar r2 s with
        | some (.word w1), some (.word w2) =>
            match wordSemBufferWrite s.codeBuffer w1 (w2.setWidth 8) with
            | some newCb => (none, { s with codeBuffer := newCb })
            | none => (some .error, s)
        | _, _ => (some .error, s))
  | .dataBufferWrite r1 r2 =>
      some (if ¬s.useStack then (some .error, s) else
        match getVar r1 s, getVar r2 s with
        | some (.word w1), some (.word w2) =>
            match wordSemBufferWrite s.dataBuffer w1 w2 with
            | some newDb => (none, { s with dataBuffer := newDb })
            | none => (some .error, s)
        | _, _ => (some .error, s))
  | _ => none

/-- Flapjack assembly equation for the source CodeBufferWrite clause, preserving
the `w2w` byte truncation and the exact buffer_write failure return. -/
theorem evaluateBufferWrite_codeBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluateBufferWrite (.codeBufferWrite r1 r2) s =
      some (match getVar r1 s, getVar r2 s with
        | some (.word w1), some (.word w2) =>
            match wordSemBufferWrite s.codeBuffer w1 (w2.setWidth 8) with
            | some newCb => (none, { s with codeBuffer := newCb })
            | none => (some .error, s)
        | _, _ => (some .error, s)) := rfl

/-- Flapjack assembly equation for the source DataBufferWrite clause, preserving
the `use_stack` guard, the full-width data word, and the failure return. -/
theorem evaluateBufferWrite_dataBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluateBufferWrite (.dataBufferWrite r1 r2) s =
      some (if ¬s.useStack then (some .error, s) else
        match getVar r1 s, getVar r2 s with
        | some (.word w1), some (.word w2) =>
            match wordSemBufferWrite s.dataBuffer w1 w2 with
            | some newDb => (none, { s with dataBuffer := newDb })
            | none => (some .error, s)
        | _, _ => (some .error, s)) := rfl

end Flapjack.StackSemBufferWrites
