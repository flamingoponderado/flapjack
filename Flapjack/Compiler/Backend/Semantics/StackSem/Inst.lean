import Flapjack.Compiler.Backend.Semantics.StackSem.IntegerInstructions

/-! Integer-only native StackSem primitive instruction operation.
The outer instruction families are Skip, Const, Arith and Mem. The result is
an Option state, with none representing instruction failure. The restricted
carrier intentionally differs from the HOL instruction datatype. -/
namespace Flapjack.StackSemInst
open Compiler.Encoders.Asm StackSemIntegerInstructions

/-- Canonical codec for the actual imported native owning state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Execute the restricted integer and memory instructions. -/
noncomputable def instHOL {width : Nat} [NeZero width] {C F : Type}
    (instruction : HolInst width) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemStateFiniteExact width C F) :=
  match instruction with
  | _ => (instInteger instruction s).join

/-- Generic structural coverage: exactly one reviewed fragment handles each
outer instruction constructor. The outer Option is always present, including
when the original operation returns semantic NONE. Flapjack infrastructure. -/
theorem instHOL_coverage {width : Nat} [NeZero width] {C F : Type}
    (instruction : HolInst width) (s : StackSemStateFiniteExact width C F) :
    (match instruction with
     | _ => instInteger instruction s) = some (instHOL instruction s) := by
  cases instruction with
  | skip => rfl
  | const register word => rfl
  | arith operation => rfl
  | mem operation register address => rfl
/-- Clock preservation derived from actual primitive execution. This is
Flapjack support for the full source clock-neutral theorem, with no supplied
post-state relation. -/
theorem instHOL_clock_eq {width : Nat} [NeZero width] {C F : Type}
    (instruction : HolInst width) (s t : StackSemStateFiniteExact width C F)
    (h : instHOL instruction s = some t) : t.clock = s.clock := by
  have covered := instHOL_coverage instruction s
  rw [h] at covered
  cases instruction with
  | skip => exact instInteger_clock_eq .skip s t covered
  | const register word => exact instInteger_clock_eq (.const register word) s t covered
  | arith operation => exact instInteger_clock_eq (.arith operation) s t covered
  | mem operation register address =>
      exact instInteger_clock_eq (.mem operation register address) s t covered

end Flapjack.StackSemInst
