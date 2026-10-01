import Flapjack.Compiler.Backend.Semantics.StackSem.FpRegisterInstructions

/-! Complete FP constructor branch for native StackSem instruction assembly.
This operation accepts every HolFp opcode and returns HOL's single Option state.
It reuses the source-reviewed clause bodies without exposing the assembly-only
outer Option. The complete branch was source-compared under flapjack-i81m against clauses
519–636 and original full carrier types. It makes no whole inst_def or evaluator
claim. The inherited real renderings retain reals_as_rational_cuts, SOUNDNESS
item 8; the pure Lean sqrt agreement does not prove HOL-to-Lean equivalence. -/
namespace Flapjack.StackSemFpInstructions
open Flapjack.StackSemFpRegisterInstructions Flapjack.Compiler.Encoders.Asm

/-- Same-module codec witness for the actual imported state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Complete FP branch, with exactly the primitive instruction result shape.
The outer dispatcher Option cannot be absent for any FP opcode, as proved below.
No callback, successful target evaluation or other law is an input. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "inst_def" 409
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
noncomputable def instFp {width : Nat} [NeZero width] {C F : Type}
    (operation : HolFp) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemStateFiniteExact width C F) :=
  (instFpRegister (.fp operation) s).join

/-- Structural coverage certificate for all sixteen FP constructors. -/
theorem instFpRegister_complete {width : Nat} [NeZero width] {C F : Type}
    (operation : HolFp) (s : StackSemStateFiniteExact width C F) :
    instFpRegister (.fp operation) s = some (instFp operation s) := by
  cases operation <;> simp only [instFp, instFpRegister, Option.join_some]

/-- Frame preservation derived from the actual successful transition. This is
Flapjack assembly infrastructure, without a separately tagged HOL original. -/
theorem instFp_frame {width : Nat} [NeZero width] {C F : Type}
    (operation : HolFp) (s t : StackSemStateFiniteExact width C F)
    (h : instFp operation s = some t) :
    t.clock = s.clock ∧ t.stack = s.stack ∧ t.memory = s.memory := by
  apply instFpRegister_frame (.fp operation) s t
  rw [instFpRegister_complete, h]

end Flapjack.StackSemFpInstructions
