import Flapjack.Compiler.Backend.Semantics.StackSem.Control
import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps

/-! A source-shaped `evaluate_def` JumpLower case fragment over the exact
StackSem state/result carriers. It is deliberately untagged: this partial case
helper is not the total HOL `evaluate_def` definition, and the recursive evaluator is an explicit parameter so the
recursive measure stays explicit without an import cycle. The total evaluator
is assembled in Evaluate.lean and supplies its checked recursive calls. -/

namespace Flapjack.StackSemJumpLower

open StackSemControl StackSemStateOps Compiler.Backend.StackLang

/-- The HOL `evaluate (JumpLower r1 r2 dest, s)` branch
(`cakeml/compiler/backend/semantics/stackSemScript.sml:838-849`): read two Word
registers, compare them with the unsigned assembler `Lower` comparison, look the
target up with `INL find_code`, time out on a zero clock, and otherwise recurse
on the found program with a decremented clock, mapping a bad function return to
`Error`. The recursive sub-evaluation is the explicit `evaluate` parameter. -/
def evaluateJumpLower {width : Nat} [NeZero width] {C F : Type}
    (evaluate : HolProg width → StackSemStateFiniteExact width C F →
      Option (StackSemResult width) × StackSemStateFiniteExact width C F)
    (r1 r2 dest : Nat) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  match getVar r1 s, getVar r2 s with
  | some (.word x), some (.word y) =>
      if Compiler.Encoders.Asm.wordCmpHOL .lower x y then
        match findCode (.inl dest) s.regs s.code with
        | none => (some .error, s)
        | some prog =>
            if s.clock = 0 then (some .timeOut, emptyEnv s)
            else
              match evaluate prog (decClock s) with
              | (res, s') => if badFunReturn res then (some .error, s') else (res, s')
      else (none, s)
  | _, _ => (some .error, s)

end Flapjack.StackSemJumpLower
