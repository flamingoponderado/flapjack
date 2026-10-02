import Flapjack.Compiler.Backend.StackRemove.Proofs.InstructionSimulation.Atoms

namespace Flapjack.Compiler.Backend.StackRemove.InstructionSimulation.FloatingPoint
open Flapjack Compiler.Encoders.Asm

/-- Canonical actual-state codec witness, Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Complete genuine FP case of the original instruction theorem, all sixteen
opcodes. The native sqrt/conversions retain the inherited reals_as_rational_cuts
assumption; no new assumption about FP results, NaNs, rounding or target runs is
introduced. Width-dependent transfers and ordered aliased updates are preserved. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_inst"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelInstFp {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (operation : HolFp) (source target postSource : StackSemStateFiniteExact width C F)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      StackProps.regBoundInst (.fp operation : HolInst width) pointer ∧
      StackSemInst.instHOL (.fp operation) source = some postSource) :
    ∃ postTarget, StackSemInst.instHOL (.fp operation) target = some postTarget ∧
      stateRelHOL jump bounds pointer postSource postTarget := by
  rcases hypothesis with ⟨relation, bound, run⟩
  have fpEq : ∀ register, StackSemStateOps.getFpVar register target =
      StackSemStateOps.getFpVar register source := fun register =>
    (StateUpdates.stateRelGetFpVar jump bounds pointer register source target relation).symm
  cases operation <;> simp only [StackProps.regBoundInst] at bound
  all_goals simp only [StackSemInst.instHOL, StackSemFpInstructions.instFp,
    StackSemFpRegisterInstructions.instFpRegister,
    StackSemFpRegisterInstructions.instFpSqrt,
    StackSemFpRegisterInstructions.instFpToInt,
    StackSemFpRegisterInstructions.instFpFromInt, Option.join_some] at run ⊢
  all_goals try simp only [fpEq]
  case fpMovFromReg destination first second =>
    have firstEq := RelationLaws.stateRelGetVar jump bounds pointer first source target
      ⟨relation, bound.1⟩
    have secondEq := RelationLaws.stateRelGetVar jump bounds pointer second source target
      ⟨relation, bound.2⟩
    rw [← firstEq, ← secondEq]
    clear fpEq firstEq secondEq
    repeat' (split at run)
    all_goals try contradiction
    all_goals simp_all
    all_goals try subst postSource
    all_goals apply StateUpdates.stateRelSetFpVar
    all_goals exact relation
  all_goals clear fpEq
  all_goals repeat' (split at run)
  all_goals try contradiction
  all_goals simp_all
  all_goals try subst postSource
  all_goals repeat' (first | exact relation |
    apply StateUpdates.stateRelSetFpVar |
    (apply StateUpdates.stateRelSetVar; constructor) | omega)

end Flapjack.Compiler.Backend.StackRemove.InstructionSimulation.FloatingPoint
