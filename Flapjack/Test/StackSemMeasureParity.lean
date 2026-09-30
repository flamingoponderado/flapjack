import Flapjack.Compiler.Backend.Semantics.StackSem.Measure

/-! Kernel replay of the untagged recursion/clock certificate for the
forthcoming total StackSem `evaluate_def` dispatcher
(`Flapjack/Compiler/Backend/Semantics/StackSem/Measure.lean`). These are
internal termination facts, not HOL-tagged declarations; the examples pin the
clock bounds and the lexicographic-combination lemmas the recursive call sites
consume. -/

namespace Flapjack.Test.StackSemMeasureParity

open Flapjack Flapjack.StackSemMeasure

/-- `dec_clock` strictly decreases a nonzero clock. -/
example {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (h : s.clock ≠ 0) :
    (StackSemStateOps.decClock s).clock < s.clock :=
  decClock_clock_lt s h

/-- `dec_clock` never increases the clock. -/
example {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) :
    (StackSemStateOps.decClock s).clock ≤ s.clock :=
  decClock_clock_le s

/-- `fix_clock` bounds the returned clock by the input clock. -/
example {width : Nat} [NeZero width] {C F R : Type}
    (s : StackSemStateFiniteExact width C F)
    (x : R × StackSemStateFiniteExact width C F) :
    (StackSemControl.fixClock s x).2.clock ≤ s.clock :=
  fixClock_clock_le s x

/-- A strictly smaller clock gives a lexicographic decrease. -/
example : LexNat (2, 5) (3, 0) := lexNat_of_clock_lt (by omega)

/-- An equal clock with a strictly smaller program size decreases. -/
example : LexNat (3, 5) (3, 9) := lexNat_of_clock_eq_of_size_lt (by omega)

/-- The `Seq` site: a bounded-and-smaller pair decreases. -/
example : LexNat (2, 0) (3, 9) :=
  lexNat_of_le_of_size_lt (show 2 ≤ 3 by omega) (by omega)

/-- The `dec_clock` site with an arbitrary program-size component. -/
example {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (h : s.clock ≠ 0) :
    LexNat ((StackSemStateOps.decClock s).clock, 7) (s.clock, 0) :=
  lexNat_decClock s 7 0 h

def runChecks : IO Bool := do
  IO.println "PASS StackSem recursion/clock certificate lemmas (untagged)"
  return true

end Flapjack.Test.StackSemMeasureParity
