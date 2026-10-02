import Flapjack.Compiler.Backend.Semantics.StackSem.Control
import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps

/-! Untagged recursion/clock certificate for the total StackSem
`evaluate_def` dispatcher assembled in Evaluate.lean.

HOL defines `evaluate` with the termination measure
`inv_image (measure I LEX measure (prog_size (K 0)))
             (\(xs,(s:('a,'c,'ffi) stackSem$state)). (s.clock,xs))`
and discharges the decrease obligation from `fix_clock_IMP` plus arithmetic
(`cakeml/compiler/backend/semantics/stackSemScript.sml:1022-1027`). This module
exposes the clock half of that certificate over the accepted
`StackSemStateFiniteExact` carrier, together with the lexicographic-combination
lemmas the recursive call sites need. The program half is a structural-subterm
fact discharged by the dispatcher's `decreasing_by` obligation. It introduces
no evaluator, no dispatch, and no `@[hol]` tag. -/

namespace Flapjack.StackSemMeasure

open Flapjack.StackSemControl Flapjack.StackSemStateOps

/-- The lexicographic product order used by HOL's termination measure
`measure I LEX measure (prog_size (K 0))`. -/
abbrev LexNat : Nat × Nat → Nat × Nat → Prop :=
  Prod.Lex (fun a b => a < b) (fun a b => a < b)

/-- `fix_clock` returns the pointwise minimum clock (`fix_clock_def`). -/
theorem fixClock_clock_eq {width returnedWidth : Nat} [NeZero width] [NeZero returnedWidth]
    {C F ReturnedC ReturnedF R : Type}
    (s : StackSemStateFiniteExact width C F)
    (x : R × StackSemStateFiniteExact returnedWidth ReturnedC ReturnedF) :
    (fixClock s x).2.clock = min s.clock x.2.clock := rfl

/-- HOL `fix_clock_IMP` as a direct clock bound on the returned state. -/
theorem fixClock_clock_le {width returnedWidth : Nat} [NeZero width] [NeZero returnedWidth]
    {C F ReturnedC ReturnedF R : Type}
    (s : StackSemStateFiniteExact width C F)
    (x : R × StackSemStateFiniteExact returnedWidth ReturnedC ReturnedF) :
    (fixClock s x).2.clock ≤ s.clock := by
  rw [fixClock_clock_eq]
  exact Nat.min_le_left _ _

/-- `dec_clock` strictly decreases a nonzero clock. -/
theorem decClock_clock_lt {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (h : s.clock ≠ 0) :
    (decClock s).clock < s.clock := by
  simp only [decClock]
  omega

/-- `dec_clock` never increases the clock. -/
theorem decClock_clock_le {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) :
    (decClock s).clock ≤ s.clock := by
  simp only [decClock]
  omega

/-- Lexicographic strict decrease from a strictly smaller clock. -/
theorem lexNat_of_clock_lt {a c b d : Nat} (h : a < c) :
    LexNat (a, b) (c, d) :=
  Prod.Lex.left _ _ h

/-- Lexicographic strict decrease from an equal clock and a strictly smaller
program size. -/
theorem lexNat_of_clock_eq_of_size_lt {a b d : Nat} (h : b < d) :
    LexNat (a, b) (a, d) :=
  Prod.Lex.right _ h

/-- The `Seq` recursive call site: after `fix_clock` the returned clock is at
most the input clock and the second program is a proper subterm, so the measure
strictly decreases. HOL's `evaluate (Seq c1 c2, s)` recurses on `(c2, s1)` with
`(res, s1) = fix_clock s (evaluate (c1, s))`
(`stackSemScript.sml:812-814`). `hsize` is the structural-subterm obligation the
dispatcher's `decreasing_by` discharges. -/
theorem lexNat_of_le_of_size_lt {s1clock parentClock sizeSecond sizeParent : Nat}
    (hle : s1clock ≤ parentClock) (hsize : sizeSecond < sizeParent) :
    LexNat (s1clock, sizeSecond) (parentClock, sizeParent) := by
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exact Prod.Lex.left _ _ hlt
  · rw [heq]
    exact Prod.Lex.right _ hsize

/-- The direct `dec_clock` call site (call, jump, raw-call and `Loop` reentry):
a nonzero clock that is bounded by the outer clock decrements strictly, so the
measure strictly decreases regardless of the program component. HOL's
`RawCall`/`Call`/`JumpLower` recurse on `(body, dec_clock s)`
(`stackSemScript.sml:838-892`) and `Loop` on `(STOP (Loop c1), dec_clock s1)`
(`:833-837`). -/
theorem lexNat_decClock {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (b d : Nat) (h : s.clock ≠ 0) :
    LexNat ((decClock s).clock, b) (s.clock, d) :=
  Prod.Lex.left _ _ (decClock_clock_lt s h)

end Flapjack.StackSemMeasure
