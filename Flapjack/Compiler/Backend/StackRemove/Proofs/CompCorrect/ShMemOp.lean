import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Control
import Flapjack.Compiler.Backend.StackRemove.Proofs.StateUpdates
import Flapjack.Compiler.Backend.StackRemove.Proofs.ExpressionSimulation

namespace Flapjack.Compiler.Backend.StackRemove.CompCorrect.ShMemOp
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps StackSemShMem

/-- Flapjack infrastructure for the shared-memory case: replacing the common
FFI state preserves every conjunct of the original relation. There is no
standalone HOL declaration for this field-update factoring. -/
theorem stateRelFfi {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) (ffi : HolFfiState F)
    (relation : stateRelHOL jump bounds pointer source target) :
    stateRelHOL jump bounds pointer {source with ffi := ffi} {target with ffi := ffi} := by
  simp only [stateRelHOL] at relation ⊢
  rcases relation with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩
  exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,True.intro,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩

/-- Flapjack factoring of the eight original shared-memory cases. Source
execution determines the target execution; it is not a target-run premise. -/
private def simulationPost {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (result : Option (StackSemResult width))
    (source target : StackSemStateFiniteExact width C F) : Prop :=
  match result with
  | some (.halt _) | some .timeOut | some (.finalFFI _) => target.ffi = source.ffi
  | _ => stateRelHOL jump bounds pointer source target

theorem shMemOpSimulation {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer register : Nat)
    (op : WordMemOp) (address : BitVec width)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (relation : stateRelHOL jump bounds pointer source target)
    (below : register < pointer)
    (sourceRun : shMemOp op register address source = (result, postSource))
    (notError : result ≠ some .error) :
    ∃ postTarget, shMemOp op register address target = (result, postTarget) ∧
      simulationPost jump bounds pointer result postSource postTarget := by
  have readEq := (RelationLaws.stateRelGetVar jump bounds pointer register source target
    ⟨relation, below⟩).symm
  have domainEq : target.shMdomain = source.shMdomain :=
    (RelationLaws.stateRelConst jump bounds pointer source target relation).2.1
  have ffiEq : target.ffi = source.ffi :=
    (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
  cases op <;> simp only [shMemOp, shMemLoad, shMemStore, shMemLoadByte,
    shMemStoreByte, shMemLoad16, shMemStore16, shMemLoad32, shMemStore32] at sourceRun ⊢
  all_goals simp only [readEq, domainEq, ffiEq]
  all_goals repeat' split at sourceRun
  all_goals simp only [Prod.mk.injEq] at sourceRun
  all_goals rcases sourceRun with ⟨rfl, rfl⟩
  all_goals try contradiction
  all_goals simp_all only [simulationPost]
  all_goals refine ⟨_, rfl, ?_⟩
  all_goals first
    | exact ffiEq
    | simpa only [domainEq] using stateRelFfi jump bounds pointer source target _ relation
    | simpa only [domainEq, setVar] using
        stateRelFfi jump bounds pointer (setVar register _ source)
          (setVar register _ target) _
          (StateUpdates.stateRelSetVar jump bounds pointer register _ source target ⟨relation, below⟩)

/-- Canonical state codec, re-exported locally for the representation qualifier.
This is Flapjack infrastructure, with no standalone HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original ShMemOp case (1998–2022). All eight operations use the
actual native evaluator and FFI transition. The target address and run follow
from the original four premises; zero clock addition suffices, including the
original timeout and terminal FFI cases. No target execution is assumed. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectShMemOp {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (register base : Nat) (offset : BitVec width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : evaluate (.shMemOp op register (.addr base offset), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.shMemOp op register (.addr base offset) : HolProg width) pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer (.shMemOp op register (.addr base offset)),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  change register < pointer ∧ base < pointer at bound
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [evaluate_shMemOp] at sourceRun
  cases addressRun : StackSemExpressions.wordExp source (.op .add [.var base, .const offset]) with
  | none =>
    simp only [addressRun] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some address =>
    have targetAddress := ExpressionSimulation.stateRelWordExp jump bounds pointer source target
      (.op .add [.var base, .const offset]) address
      ⟨relation, by simpa [StackProps.regBoundExp] using bound.2, addressRun⟩
    simp only [addressRun] at sourceRun
    by_cases zero : source.clock = 0
    · simp only [zero, ite_true] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
      subst result
      subst postSource
      refine ⟨0, emptyEnv target, ?_, ?_⟩
      · simpa only [comp, Nat.zero_add] using
          (evaluate_shMemOp op register base offset target).trans
            (by simp only [targetAddress, clocks, zero, ite_true])
      · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
    · simp only [zero, ite_false] at sourceRun
      obtain ⟨postTarget, targetRun, postRelation⟩ := shMemOpSimulation jump bounds pointer register
        op address (decClock source) (decClock target) postSource result
        (RelationLaws.stateRelDecClock jump bounds pointer source target relation)
        bound.1 sourceRun notError
      refine ⟨0, postTarget, ?_, ?_⟩
      · simpa only [comp, Nat.zero_add] using
          (evaluate_shMemOp op register base offset target).trans
            (by simp only [targetAddress, clocks, zero, ite_false]; exact targetRun)
      · cases result with
        | none => exact postRelation
        | some outcome => cases outcome <;> exact postRelation

end Flapjack.Compiler.Backend.StackRemove.CompCorrect.ShMemOp
