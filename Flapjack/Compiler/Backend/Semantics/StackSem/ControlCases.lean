import Flapjack.Compiler.Backend.Semantics.StackSem.Control
import Flapjack.Compiler.Backend.Semantics.StackSem.Measure
import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors

/-! Untagged, source-shaped fragments of the structured-control clauses of HOL
`evaluate_def` (`cakeml/compiler/backend/semantics/stackSemScript.sml:811-837`):

```
(evaluate (Seq c1 c2,s) =
   let (res,s1) = fix_clock s (evaluate (c1,s)) in
     if res = NONE then evaluate (c2,s1) else (res,s1)) /\
(evaluate (If cmp r1 ri c1 c2,s) =
  (case (get_var r1 s,get_var_imm ri s) of
   | SOME x,SOME y =>
    (case wordSem$word_cmp cmp x y of
     | SOME T => evaluate (c1,s)
     | SOME F => evaluate (c2,s)
     | NONE => (SOME Error,s))
   | _ => (SOME Error,s))) /\
(evaluate (Loop c1,s) =
  (let (res,s1) = fix_clock s (evaluate (c1,s)) in
     if cont_loop res then
       (if s1.clock = 0 then (SOME TimeOut, empty_env s1) else
          evaluate (STOP (Loop c1), dec_clock s1))
     else (exit_loop res,s1)))
```

`STOP` is the identity (`stackSemScript.sml:663-664`), and `If` uses the
option-valued `wordSem$word_cmp` (tagged Lean `wordSemWordCmp`), not the
asm-level Boolean comparison. The recursive sub-evaluation is threaded as an
explicit `evaluate` parameter so these fragments stay non-recursive, exactly as
in the sibling `LeafTransfers`/`Call`/`JumpLower` fragments. The decrease facts
for the dispatcher's recursive call sites are stated using the untagged clock
certificate of `Flapjack.StackSemMeasure` (`flapjack-y19g.17`).

Every declaration here is UNTAGGED: these are partial case fragments, not the
whole HOL `evaluate_def`; the total 34-constructor evaluator assembly is tracked
by bead `flapjack-y19g.18` (parent `flapjack-y19g`). -/

namespace Flapjack.StackSemControlCases

open Flapjack.StackSemControl Flapjack.StackSemStateOps Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- The HOL `evaluate (Seq c1 c2, s)` branch
(`cakeml/compiler/backend/semantics/stackSemScript.sml:811-814`): clamp the
first sub-evaluation's returned clock to the input clock, then run the second
program on the clamped state only when the first produced `NONE`; otherwise
propagate the first result and state. `res = NONE` is the definitional
`none`/`some` case split, so no `DecidableEq` instance is required. -/
def evaluateSeq {width : Nat} [NeZero width] {C F : Type}
    (evaluate : HolProg width → StackSemStateFiniteExact width C F →
      Option (StackSemResult width) × StackSemStateFiniteExact width C F)
    (first second : HolProg width) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  match fixClock s (evaluate first s) with
  | (none, s1) => evaluate second s1
  | (res, s1) => (res, s1)

/-- Unfolding equation for the `Seq` fragment. -/
theorem evaluateSeq_def {width : Nat} [NeZero width] {C F : Type}
    (evaluate : HolProg width → StackSemStateFiniteExact width C F →
      Option (StackSemResult width) × StackSemStateFiniteExact width C F)
    (first second : HolProg width) (s : StackSemStateFiniteExact width C F) :
    evaluateSeq evaluate first second s =
      (match fixClock s (evaluate first s) with
       | (none, s1) => evaluate second s1
       | (res, s1) => (res, s1)) := rfl

/-- The HOL `evaluate (If cmp r1 ri c1 c2, s)` branch
(`cakeml/compiler/backend/semantics/stackSemScript.sml:825-832`): look up the
register and the register/immediate operand, apply the option-valued
`wordSem$word_cmp`, run `c1` on `SOME T`, `c2` on `SOME F`, and return `Error`
with the original state on `NONE` or a missing operand. The `If` payload uses
the exact `HolRegImm` carrier, transported to the tagged `getVarImm` mirror by
the untagged `HolRegImm.toWordRegImm` codec. -/
def evaluateIf {width : Nat} [NeZero width] {C F : Type}
    (evaluate : HolProg width → StackSemStateFiniteExact width C F →
      Option (StackSemResult width) × StackSemStateFiniteExact width C F)
    (cmp : Cmp) (r1 : Nat) (ri : HolRegImm width)
    (first second : HolProg width) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  match getVar r1 s, StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri) s with
  | some x, some y =>
      match wordSemWordCmp cmp x y with
      | some true => evaluate first s
      | some false => evaluate second s
      | none => (some .error, s)
  | _, _ => (some .error, s)

/-- Unfolding equation for the `If` fragment. -/
theorem evaluateIf_def {width : Nat} [NeZero width] {C F : Type}
    (evaluate : HolProg width → StackSemStateFiniteExact width C F →
      Option (StackSemResult width) × StackSemStateFiniteExact width C F)
    (cmp : Cmp) (r1 : Nat) (ri : HolRegImm width)
    (first second : HolProg width) (s : StackSemStateFiniteExact width C F) :
    evaluateIf evaluate cmp r1 ri first second s =
      (match getVar r1 s, StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri) s with
       | some x, some y =>
           match wordSemWordCmp cmp x y with
           | some true => evaluate first s
           | some false => evaluate second s
           | none => (some .error, s)
       | _, _ => (some .error, s)) := rfl

/-- The HOL `evaluate (Loop c1, s)` branch
(`cakeml/compiler/backend/semantics/stackSemScript.sml:833-837`): clamp the
body's returned clock; when the body result satisfies `contLoop` and the
clamped clock is nonzero, re-enter on `STOP (Loop c1)` (the identity `STOP`
makes this `Loop c1`) with the decremented clock; when the clamped clock is
zero, return `TimeOut` with the emptied environment; otherwise propagate
`exitLoop` of the body result. The re-entry call uses the explicit `evaluate`
parameter. -/
def evaluateLoop {width : Nat} [NeZero width] {C F : Type}
    (evaluate : HolProg width → StackSemStateFiniteExact width C F →
      Option (StackSemResult width) × StackSemStateFiniteExact width C F)
    (body : HolProg width) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  match fixClock s (evaluate body s) with
  | (res, s1) =>
      if contLoop res then
        (if s1.clock = 0 then (some .timeOut, emptyEnv s1)
         else evaluate (.loop body) (decClock s1))
      else (StackSemControl.exitLoop res, s1)

/-- Unfolding equation for the `Loop` fragment. -/
theorem evaluateLoop_def {width : Nat} [NeZero width] {C F : Type}
    (evaluate : HolProg width → StackSemStateFiniteExact width C F →
      Option (StackSemResult width) × StackSemStateFiniteExact width C F)
    (body : HolProg width) (s : StackSemStateFiniteExact width C F) :
    evaluateLoop evaluate body s =
      (match fixClock s (evaluate body s) with
       | (res, s1) =>
           if contLoop res then
             (if s1.clock = 0 then (some .timeOut, emptyEnv s1)
              else evaluate (.loop body) (decClock s1))
           else (StackSemControl.exitLoop res, s1)) := rfl

/-- Dispatcher decrease fact for the `Seq` second-program call site: the clamped
clock is at most the input clock, so with a strictly smaller second-program size
the lexicographic measure strictly decreases. `hsize` is the structural-subterm
obligation the dispatcher discharges. -/
theorem evaluateSeq_decreasing {width : Nat} [NeZero width] {C F : Type}
    (evaluate : HolProg width → StackSemStateFiniteExact width C F →
      Option (StackSemResult width) × StackSemStateFiniteExact width C F)
    (first second : HolProg width) (s : StackSemStateFiniteExact width C F)
    (hsize : sizeOf second < sizeOf (.seq first second : HolProg width)) :
    LexNat ((fixClock s (evaluate first s)).2.clock, sizeOf second)
      (s.clock, sizeOf (.seq first second : HolProg width)) :=
  lexNat_of_le_of_size_lt (fixClock_clock_le s _) hsize

/-- Dispatcher decrease fact for the `If` branch call sites: both branches run on
the same state, so the measure decreases through a strictly smaller branch size.
`hsize` is the structural-subterm obligation the dispatcher discharges. -/
theorem evaluateIf_decreasing {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (r1 : Nat) (ri : HolRegImm width)
    (first second : HolProg width) (s : StackSemStateFiniteExact width C F)
    (hsize : sizeOf first < sizeOf (.ite cmp r1 ri first second : HolProg width)) :
    LexNat (s.clock, sizeOf first) (s.clock, sizeOf (.ite cmp r1 ri first second : HolProg width)) :=
  lexNat_of_clock_eq_of_size_lt hsize

/-- Dispatcher decrease fact for the `Loop` re-entry site: the body's clamped
clock is at most the input clock, and in the re-entry branch the clamped clock
is nonzero, so the decremented clock is strictly below the input clock. -/
theorem evaluateLoop_decreasing {width : Nat} [NeZero width] {C F : Type}
    (evaluate : HolProg width → StackSemStateFiniteExact width C F →
      Option (StackSemResult width) × StackSemStateFiniteExact width C F)
    (body : HolProg width) (s : StackSemStateFiniteExact width C F)
    (hne : (fixClock s (evaluate body s)).2.clock ≠ 0) :
    LexNat ((decClock (fixClock s (evaluate body s)).2).clock, sizeOf (.loop body : HolProg width))
      (s.clock, sizeOf (.loop body : HolProg width)) :=
  lexNat_of_clock_lt
    (Nat.lt_of_lt_of_le (decClock_clock_lt _ hne) (fixClock_clock_le s _))

end Flapjack.StackSemControlCases
