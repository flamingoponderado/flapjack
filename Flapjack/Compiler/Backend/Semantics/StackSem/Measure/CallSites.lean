import Flapjack.Compiler.Backend.Semantics.StackSem.Measure

/-! Concrete termination facts for the recursive sites of
`stackSemScript.sml:811-892,1022-1027`. These are untagged Lean infrastructure:
Lean's generated `sizeOf` need not equal HOL's `prog_size (K 0)` numerically,
but both make constructor subprograms strictly smaller. Clock-decreasing calls
permit an arbitrary next program. No evaluator or HOL correspondence is assumed.
-/

namespace Flapjack.StackSemMeasure

open StackSemControl StackSemStateOps Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Lean termination measure implementing HOL's clock-first lexicographic order.
The second component is Lean structural size, not a claimed port of `prog_size`.
-/
noncomputable def stackSemMeasure {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) : Nat × Nat :=
  (s.clock, sizeOf p)

theorem seq_first_size_lt {width : Nat} [NeZero width] (a b : HolProg width) :
    sizeOf a < sizeOf (.seq a b : HolProg width) := by simp; omega

theorem seq_second_size_lt {width : Nat} [NeZero width] (a b : HolProg width) :
    sizeOf b < sizeOf (.seq a b : HolProg width) := by simp; omega

theorem if_first_size_lt {width : Nat} [NeZero width]
    (cmp : HolCmp) (r : Nat) (ri : HolRegImm width)
    (a b : HolProg width) :
    sizeOf a < sizeOf (.ite cmp r ri a b : HolProg width) := by simp; omega

theorem if_second_size_lt {width : Nat} [NeZero width]
    (cmp : HolCmp) (r : Nat) (ri : HolRegImm width)
    (a b : HolProg width) :
    sizeOf b < sizeOf (.ite cmp r ri a b : HolProg width) := by simp; omega

theorem loop_body_size_lt {width : Nat} [NeZero width] (body : HolProg width) :
    sizeOf body < sizeOf (.loop body : HolProg width) := by simp

theorem seq_first_measure_lt {width : Nat} [NeZero width] {C F : Type}
    (a b : HolProg width) (s : StackSemStateFiniteExact width C F) :
    LexNat (stackSemMeasure a s) (stackSemMeasure (.seq a b) s) :=
  lexNat_of_clock_eq_of_size_lt (seq_first_size_lt a b)

theorem if_first_measure_lt {width : Nat} [NeZero width] {C F : Type}
    (cmp : HolCmp) (r : Nat) (ri : HolRegImm width) (a b : HolProg width)
    (s : StackSemStateFiniteExact width C F) :
    LexNat (stackSemMeasure a s) (stackSemMeasure (.ite cmp r ri a b) s) :=
  lexNat_of_clock_eq_of_size_lt (if_first_size_lt cmp r ri a b)

theorem if_second_measure_lt {width : Nat} [NeZero width] {C F : Type}
    (cmp : HolCmp) (r : Nat) (ri : HolRegImm width) (a b : HolProg width)
    (s : StackSemStateFiniteExact width C F) :
    LexNat (stackSemMeasure b s) (stackSemMeasure (.ite cmp r ri a b) s) :=
  lexNat_of_clock_eq_of_size_lt (if_second_size_lt cmp r ri a b)

theorem loop_body_measure_lt {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (s : StackSemStateFiniteExact width C F) :
    LexNat (stackSemMeasure body s) (stackSemMeasure (.loop body) s) :=
  lexNat_of_clock_eq_of_size_lt (loop_body_size_lt body)

/-- The second Seq evaluation may keep the input clock, but its program is smaller.
The callback can return any clock: the source `fix_clock` supplies the bound.
-/
theorem seq_second_measure_lt {width : Nat} [NeZero width] {C F R : Type}
    (a b : HolProg width) (s : StackSemStateFiniteExact width C F)
    (returned : R × StackSemStateFiniteExact width C F) :
    LexNat (stackSemMeasure b (fixClock s returned).2)
      (stackSemMeasure (.seq a b) s) :=
  lexNat_of_le_of_size_lt (fixClock_clock_le s returned) (seq_second_size_lt a b)

/-- Loop reentry decreases the clamped clock even though its program is unchanged.
`STOP` is identity in HOL; no structural-size decrease is required at this site.
-/
theorem loop_reentry_measure_lt {width : Nat} [NeZero width] {C F R : Type}
    (body : HolProg width) (s : StackSemStateFiniteExact width C F)
    (returned : R × StackSemStateFiniteExact width C F)
    (hne : (fixClock s returned).2.clock ≠ 0) :
    LexNat (stackSemMeasure (.loop body) (decClock (fixClock s returned).2))
      (stackSemMeasure (.loop body) s) :=
  lexNat_of_clock_lt
    (Nat.lt_of_lt_of_le (decClock_clock_lt _ hne) (fixClock_clock_le s returned))

/-- Found code may have any size: calls and jumps decrease the original clock.
-/
theorem callee_measure_lt {width : Nat} [NeZero width] {C F : Type}
    (callee parent : HolProg width) (s : StackSemStateFiniteExact width C F)
    (hne : s.clock ≠ 0) :
    LexNat (stackSemMeasure callee (decClock s)) (stackSemMeasure parent s) :=
  lexNat_decClock s _ _ hne

/-- Call return and exception continuations run after the callee's clock is
clamped to a decremented input. This clock is strictly below the outer clock,
so no continuation-size premise is necessary. `setVar` preserves that clock.
-/
theorem call_continuation_measure_lt {width : Nat} [NeZero width] {C F R : Type}
    (continuation parent : HolProg width) (s : StackSemStateFiniteExact width C F)
    (link label entry : Nat) (returned : R × StackSemStateFiniteExact width C F)
    (hne : s.clock ≠ 0) :
    LexNat (stackSemMeasure continuation
      (fixClock (decClock (setVar link (.loc label entry) s)) returned).2)
      (stackSemMeasure parent s) := by
  apply lexNat_of_clock_lt
  apply Nat.lt_of_le_of_lt (fixClock_clock_le _ returned)
  simpa only [decClock, setVar] using decClock_clock_lt s hne

end Flapjack.StackSemMeasure
