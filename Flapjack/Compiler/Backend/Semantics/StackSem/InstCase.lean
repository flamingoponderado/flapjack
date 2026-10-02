import Flapjack.Compiler.Backend.Semantics.StackSem.Inst

/-! Source-matched `Inst` clause of `stackSemScript.sml` `evaluate_def`
(lines 789-792): a successful primitive `inst i s = SOME s1` continues with
`(NONE, s1)` and a failed one returns `(SOME Error, s)` with the original state.
This is a partial dispatch helper, not a second evaluator: the outer `none` means
this module does not handle the constructor, so it never substitutes `Error` for
an unported clause. The clause calls the reviewed exact `instHOL` (`inst_def`)
over the owning `StackSemStateFiniteExact` carrier. No HOL tag applies to this
Option-shaped fragment; the total evaluator is assembled in Evaluate.lean. -/

namespace Flapjack.StackSemInstCase
open Compiler.Backend.StackLang Compiler.Encoders.Asm StackSemInst

/-- The HOL `evaluate (Inst i, s)` branch. -/
noncomputable def evaluateInst {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (s : StackSemStateFiniteExact width C F) :
    Option (Option (StackSemResult width) × StackSemStateFiniteExact width C F) :=
  match program with
  | .inst i =>
      some (match instHOL i s with
        | some s1 => (none, s1)
        | none => (some .error, s))
  | _ => none

/-- Flapjack assembly equation for the source `Inst` clause. -/
theorem evaluateInst_inst {width : Nat} [NeZero width] {C F : Type}
    (i : HolInst width) (s : StackSemStateFiniteExact width C F) :
    evaluateInst (.inst i) s =
      some (match instHOL i s with
        | some s1 => (none, s1)
        | none => (some .error, s)) := rfl

/-- The clause preserves the clock in both branches (from `instHOL_clock_eq`). -/
theorem evaluateInst_clock {width : Nat} [NeZero width] {C F : Type}
    (i : HolInst width) (s : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F)
    (h : evaluateInst (.inst i) s = some (r, t)) : t.clock = s.clock := by
  rw [evaluateInst_inst] at h
  cases hi : instHOL i s with
  | none => simp [hi] at h; rw [← h.2]
  | some s1 =>
      simp [hi] at h
      rw [← h.2]
      exact instHOL_clock_eq i s s1 hi

end Flapjack.StackSemInstCase
