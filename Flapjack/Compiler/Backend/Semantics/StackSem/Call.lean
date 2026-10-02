import Flapjack.Compiler.Backend.Semantics.StackSem.Control
import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps

/-! A source-shaped `evaluate_def` Call case fragment over the exact
StackSem state/result carriers. It is deliberately untagged: this partial case
helper is not the total HOL `evaluate_def` definition, and the recursive evaluator is an explicit parameter so the
recursive measure stays explicit without an import cycle. The total evaluator
is assembled in Evaluate.lean and supplies its checked recursive calls. -/

namespace Flapjack.StackSemCall

open StackSemControl StackSemStateOps Compiler.Backend.StackLang

/-- The HOL `evaluate (Call ret dest handler, s)` branch
(`cakeml/compiler/backend/semantics/stackSemScript.sml:861-892`). The `ret = none`
tail-call arm looks `dest` up with `find_code` (`none` -> `Error`), rejects a
present handler with `Error`, times out on a zero clock with an emptied
environment, and otherwise recurses on the found program after decrementing the
clock and clamping the returned clock, mapping a bad function return to `Error`.
The `ret = some (ret_handler, link_reg, l1, l2)` returning arm looks `dest` up
after erasing `link_reg` from the registers, stores the return `Loc l1 l2` in
`link_reg`, recurses with the decremented and clamped clock, validates the
returned `Result`/`Exception` location, and either dispatches to `ret_handler`,
the present exception handler, or the source `Error` arms for a missing handler
location match, `none`, and `Break`/`Continue`. The recursive sub-evaluation is
the explicit `evaluate` parameter. -/
def evaluateCall {width : Nat} [NeZero width] {C F : Type}
    (evaluate : HolProg width → StackSemStateFiniteExact width C F →
      Option (StackSemResult width) × StackSemStateFiniteExact width C F)
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  match ret with
  | none =>
      match findCode dest s.regs s.code with
      | none => (some .error, s)
      | some prog =>
          match handler with
          | some _ => (some .error, s)
          | none =>
              if s.clock = 0 then (some .timeOut, emptyEnv s)
              else
                match fixClock (decClock s) (evaluate prog (decClock s)) with
                | (res, s2) =>
                    if badFunReturn res then (some .error, s2) else (res, s2)
  | some (ret_handler, link_reg, l1, l2) =>
      match findCode dest (s.regs.eraseEq link_reg) s.code with
      | none => (some .error, s)
      | some prog =>
          if s.clock = 0 then (some .timeOut, emptyEnv s)
          else
            let s' := setVar link_reg (.loc l1 l2) s
            match fixClock (decClock s') (evaluate prog (decClock s')) with
            | (some (.result x), s2) =>
                if x ≠ .loc l1 l2 then (some .error, s2)
                else evaluate ret_handler s2
            | (some (.exception x), s2) =>
                match handler with
                | none => (some (.exception x), s2)
                | some (h, hl1, hl2) =>
                    if x ≠ .loc hl1 hl2 then (some .error, s2)
                    else evaluate h s2
            | (none, s2) => (some .error, s2)
            | (some (.break _), s2) => (some .error, s2)
            | (some (.continue _), s2) => (some .error, s2)
            | (res, s2) => (res, s2)

end Flapjack.StackSemCall
