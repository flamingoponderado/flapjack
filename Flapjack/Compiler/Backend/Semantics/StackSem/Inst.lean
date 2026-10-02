import Flapjack.Compiler.Backend.Semantics.StackSem.IntegerInstructions
import Flapjack.Compiler.Backend.Semantics.StackSem.FpInstructions

/-! Native StackSem primitive instruction operation. All five outer constructors
and sixteen FP opcodes are covered using the original source clause bodies.
The result is HOL's single Option state: NONE is instruction failure, never an
unhandled assembly fragment. This is inst_def, not the clocked evaluator.
Inherited reals_as_rational_cuts remains the external SOUNDNESS item 8
assumption; pure Lean sqrt agreement is not HOL-to-Lean equivalence. -/
namespace Flapjack.StackSemInst
open Compiler.Encoders.Asm StackSemIntegerInstructions StackSemFpInstructions

/-- Canonical codec for the actual imported native owning state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Full original primitive instruction operation. The integer fragment covers
Skip/Const/Arith/Mem and the FP operation covers every original FP opcode.
No successful evaluation, simulation law or callback is an input. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "inst_def" 409
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
noncomputable def instHOL {width : Nat} [NeZero width] {C F : Type}
    (instruction : HolInst width) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemStateFiniteExact width C F) :=
  match instruction with
  | .fp operation => instFp operation s
  | _ => (instInteger instruction s).join

/-- Generic structural coverage: exactly one reviewed fragment handles each
outer instruction constructor. The outer Option is always present, including
when the original operation returns semantic NONE. Flapjack infrastructure. -/
theorem instHOL_coverage {width : Nat} [NeZero width] {C F : Type}
    (instruction : HolInst width) (s : StackSemStateFiniteExact width C F) :
    (match instruction with
     | .fp _ => StackSemFpRegisterInstructions.instFpRegister instruction s
     | _ => instInteger instruction s) = some (instHOL instruction s) := by
  cases instruction with
  | skip => rfl
  | const register word => rfl
  | arith operation => rfl
  | mem operation register address => rfl
  | fp operation => exact instFpRegister_complete operation s

/-- Clock preservation derived from actual primitive execution. This is
Flapjack support for the full source clock-neutral theorem, with no supplied
post-state relation. -/
theorem instHOL_clock_eq {width : Nat} [NeZero width] {C F : Type}
    (instruction : HolInst width) (s t : StackSemStateFiniteExact width C F)
    (h : instHOL instruction s = some t) : t.clock = s.clock := by
  have covered := instHOL_coverage instruction s
  rw [h] at covered
  cases instruction with
  | fp operation => exact (instFp_frame operation s t h).1
  | skip => exact instInteger_clock_eq .skip s t covered
  | const register word => exact instInteger_clock_eq (.const register word) s t covered
  | arith operation => exact instInteger_clock_eq (.arith operation) s t covered
  | mem operation register address =>
      exact instInteger_clock_eq (.mem operation register address) s t covered

end Flapjack.StackSemInst
