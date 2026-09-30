import Flapjack.Compiler.Backend.Semantics.StackSem.Control
import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps

/-! A source-shaped `evaluate_def` RawCall case fragment over the exact
StackSem state/result carriers. It is deliberately untagged: this partial case
helper is not the total HOL `evaluate_def` definition, and because no total
recursive `evaluate` exists yet the eventual evaluator is an explicit parameter
so the recursive measure stays explicit. The assembled evaluator route is
tracked by `flapjack-y19g`. -/

namespace Flapjack.StackSemRawCall

open StackSemControl StackSemStateOps Compiler.Backend.StackLang

/-- The HOL `evaluate (RawCall dest, s)` branch
(`cakeml/compiler/backend/semantics/stackSemScript.sml:849-861`): look `dest` up
directly in `s.code` with the sptree lookup (`none` -> `Error`), decompose the
found program with `dest_Seq` (`none` -> `Error`), time out on a zero clock with
an emptied environment, and otherwise recurse on the body with a decremented
clock, mapping a bad function return to `Error`. The recursive sub-evaluation is
the explicit `evaluate` parameter. -/
def evaluateRawCall {width : Nat} [NeZero width] {C F : Type}
    (evaluate : HolProg width → StackSemStateFiniteExact width C F →
      Option (StackSemResult width) × StackSemStateFiniteExact width C F)
    (dest : Nat) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  match sptLookup dest s.code with
  | none => (some .error, s)
  | some prog =>
      match destSeqHOL prog with
      | some (_, body) =>
          if s.clock = 0 then (some .timeOut, emptyEnv s)
          else
            match evaluate body (decClock s) with
            | (res, s') => if badFunReturn res then (some .error, s') else (res, s')
      | none => (some .error, s)

end Flapjack.StackSemRawCall
