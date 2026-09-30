import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps

/-! Source-matched leaf clauses of stackSemScript.sml evaluate_def:774-823.
This is a partial dispatch helper, not a second evaluator: the outer NONE
means this module does not handle the constructor. In particular it never
substitutes Error for an unported clause. Full assembly is tracked by y19g.
No HOL tag applies to this extra Option-shaped fragment or its factoring
theorems; they are Flapjack-specific assembly infrastructure. -/
namespace Flapjack.StackSemLeafTransfers
open StackSemStateOps
open Compiler.Backend.StackLang

def evaluateLeaf {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (s : StackSemStateFiniteExact width C F) :
    Option (Option (StackSemResult width) × StackSemStateFiniteExact width C F) :=
  match program with
  | .skip => some (none, s)
  | .halt register =>
      match getVar register s with
      | some value => some (some (.halt value), emptyEnv s)
      | none => some (some .error, s)
  | .tick =>
      if s.clock = 0 then some (some .timeOut, emptyEnv s)
      else some (none, decClock s)
  | .ret register =>
      match getVar register s with
      | some (.loc first second) => some (some (.result (.loc first second)), s)
      | _ => some (some .error, s)
  | .raise register =>
      match getVar register s with
      | some (.loc first second) => some (some (.exception (.loc first second)), s)
      | _ => some (some .error, s)
  | .break label => some (some (.break label), s)
  | .continue label => some (some (.continue label), s)
  | _ => none

/-- Flapjack assembly equation for the source Skip clause. -/
theorem evaluateLeaf_skip {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) : evaluateLeaf .skip s = some (none, s) := rfl

/-- Flapjack assembly equation for the source Halt clause, including Loc payloads. -/
theorem evaluateLeaf_halt {width : Nat} [NeZero width] {C F : Type} (n : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateLeaf (.halt n) s = some (match getVar n s with
      | some w => (some (.halt w), emptyEnv s)
      | none => (some .error, s)) := by
  simp only [evaluateLeaf]
  cases getVar n s <;> rfl

/-- Flapjack assembly equation for the source Tick timeout and clock decrement. -/
theorem evaluateLeaf_tick {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) :
    evaluateLeaf .tick s = some (if s.clock = 0 then (some .timeOut, emptyEnv s)
      else (none, decClock s)) := by by_cases h : s.clock = 0 <;> simp [evaluateLeaf, h]

/-- Flapjack assembly equation for Return's Loc-only successful branch. -/
theorem evaluateLeaf_ret {width : Nat} [NeZero width] {C F : Type} (n : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateLeaf (.ret n) s = some (match getVar n s with
      | some (.loc a b) => (some (.result (.loc a b)), s)
      | _ => (some .error, s)) := by
  simp only [evaluateLeaf]
  cases getVar n s with
  | none => rfl
  | some value => cases value <;> rfl

/-- Flapjack assembly equation for Raise's Loc-only successful branch. -/
theorem evaluateLeaf_raise {width : Nat} [NeZero width] {C F : Type} (n : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateLeaf (.raise n) s = some (match getVar n s with
      | some (.loc a b) => (some (.exception (.loc a b)), s)
      | _ => (some .error, s)) := by
  simp only [evaluateLeaf]
  cases getVar n s with
  | none => rfl
  | some value => cases value <;> rfl

/-- Flapjack assembly equation preserving the source Break label and state. -/
theorem evaluateLeaf_break {width : Nat} [NeZero width] {C F : Type} (n : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateLeaf (.break n) s = some (some (.break n), s) := rfl

/-- Flapjack assembly equation preserving the source Continue label and state. -/
theorem evaluateLeaf_continue {width : Nat} [NeZero width] {C F : Type} (n : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateLeaf (.continue n) s = some (some (.continue n), s) := rfl

/-- Assembly certificate: every handled leaf returns a clock no larger than
its input, without assuming any evaluator simulation or clock bound. -/
theorem evaluateLeaf_clock_le {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (s : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F)
    (h : evaluateLeaf program s = some (result, t)) : t.clock ≤ s.clock := by
  cases program <;> simp only [evaluateLeaf] at h
  all_goals try contradiction
  all_goals repeat' (split at h)
  all_goals cases h
  all_goals try simp only [emptyEnv, decClock]
  all_goals omega

end Flapjack.StackSemLeafTransfers
