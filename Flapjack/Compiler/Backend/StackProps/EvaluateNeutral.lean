import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock
import Flapjack.Compiler.Backend.StackProps.ClockSupport

namespace Flapjack.Compiler.Backend.StackProps.EvaluateNeutral
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackProps.EvaluateAddClock

/-- Flapjack structural infrastructure: the original neutral-program predicate
implies full clock update commutation and unchanged post-clock. Neither property
is assumed for subprograms; both are proved by structural induction. -/
private theorem neutralClockFree {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (neutral : clockNeutralHOL p) : ClockFree (C := C) (F := F) p := by
  cases programEq : p
  all_goals rw [programEq] at neutral
  case skip => exact clockFree_of_ctor .skip rfl
  case inst instruction => exact clockFree_inst instruction
  case halt register => exact clockFree_of_ctor (.halt register) rfl
  case locValue register label entry => exact clockFree_of_ctor (.locValue register label entry) rfl
  case seq first second =>
    obtain ⟨neutralFirst, neutralSecond⟩ := neutral
    have firstFree := neutralClockFree (C := C) (F := F) first neutralFirst
    have secondFree := neutralClockFree (C := C) (F := F) second neutralSecond
    intro source clock
    cases firstRun : evaluate (first, source) with
    | mk result post =>
      have postClock := (firstFree source clock).2
      rw [firstRun] at postClock
      dsimp only at postClock
      have commute := (firstFree source clock).1
      rw [firstRun] at commute
      dsimp only at commute
      have fixed : fixClock source (result, post) = (result, post) := by
        change (result, {post with clock := min source.clock post.clock}) = (result, post)
        rw [← postClock, Nat.min_self]
      have fixedChanged : fixClock {source with clock := clock}
          (result, {post with clock := clock}) = (result, {post with clock := clock}) := by
        simp [fixClock]
      rw [evaluate_seq, evaluate_seq, firstRun, commute, fixed, fixedChanged]
      cases result with
      | none => exact ⟨(secondFree post clock).1, (secondFree post clock).2.trans postClock⟩
      | some value => exact ⟨rfl, postClock⟩
  case ite comparison register immediate first second =>
    obtain ⟨neutralFirst, neutralSecond⟩ := neutral
    have firstFree := neutralClockFree (C := C) (F := F) first neutralFirst
    have secondFree := neutralClockFree (C := C) (F := F) second neutralSecond
    intro source clock
    have immediateSame : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm immediate)
        {source with clock := clock} = StackSemStateOps.getVarImm (HolRegImm.toWordRegImm immediate) source := by
      cases immediate <;> rfl
    simp only [evaluate_ite, immediateSame, StackSemStateOps.getVar]
    repeat' (first | split | dsimp only)
    all_goals first | exact firstFree source clock | exact secondFree source clock | exact ⟨rfl, rfl⟩
  all_goals simp [clockNeutralHOL] at neutral

termination_by sizeOf p
decreasing_by all_goals simp_all <;> omega

/-- Canonical imported state codec witness; representation infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Full original clock-neutral evaluator theorem. All arbitrary program,
source/result/post-state and replacement-clock binders are retained. The only
premises are source evaluation and the original neutrality predicate; target
execution and post-clock constancy are derived. The evaluator closure inherits
reals_as_rational_cuts (SOUNDNESS item 8); no new floating-point agreement is asserted. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_clock_neutral"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateClockNeutral {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (clock : Nat)
    (hypothesis : evaluate (program, source) = (result, post) ∧ clockNeutralHOL program) :
    evaluate (program, {source with clock := clock}) = (result, {post with clock := clock}) := by
  have commute := (neutralClockFree (C := C) (F := F) program hypothesis.2 source clock).1
  rw [hypothesis.1] at commute
  exact commute

/-- Flapjack structural infrastructure: on the original neutral programs, FFI
update commutes with evaluation. Proved by structural induction; nothing about
subprograms is assumed. -/
private theorem neutralFfiFree {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (neutral : clockNeutralHOL p)
    (source : StackSemStateFiniteExact width C F) (k : HolFfiState F) :
    evaluate (p, {source with ffi := k}) =
      ((evaluate (p, source)).1, {(evaluate (p, source)).2 with ffi := k}) := by
  cases programEq : p
  all_goals rw [programEq] at neutral
  case skip => simp only [evaluate_skip]
  case halt register =>
    simp only [evaluate_halt, getVar]
    split <;> rfl
  case locValue register label entry =>
    simp only [evaluate_locValue]
    split <;> rfl
  case inst instruction =>
    simp only [evaluate_inst]
    cases h : StackSemInst.instHOL instruction source with
    | none =>
      rw [(StackPropsInstructionConstants.instClockNeutralFfi instruction source source k).2 h]
    | some t =>
      rw [(StackPropsInstructionConstants.instClockNeutralFfi instruction source t k).1 h]
  case seq first second =>
    obtain ⟨neutralFirst, neutralSecond⟩ := neutral
    rw [evaluate_seq, evaluate_seq,
      neutralFfiFree (C := C) (F := F) first neutralFirst source k]
    cases firstRun : evaluate (first, source) with
    | mk result post =>
      simp only [fixClock]
      cases result with
      | none =>
        exact neutralFfiFree (C := C) (F := F) second neutralSecond
          {post with clock := min source.clock post.clock} k
      | some value => rfl
  case ite comparison register immediate first second =>
    obtain ⟨neutralFirst, neutralSecond⟩ := neutral
    have immediateSame : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm immediate)
        {source with ffi := k} = StackSemStateOps.getVarImm (HolRegImm.toWordRegImm immediate) source := by
      cases immediate <;> rfl
    simp only [evaluate_ite, immediateSame, StackSemStateOps.getVar]
    repeat' (first | split | dsimp only)
    all_goals first
      | exact neutralFfiFree (C := C) (F := F) first neutralFirst source k
      | exact neutralFfiFree (C := C) (F := F) second neutralSecond source k
  all_goals simp [clockNeutralHOL] at neutral

termination_by sizeOf p
decreasing_by all_goals simp_all <;> omega

/-- Full original FFI-neutral evaluator theorem (`stackPropsScript.sml:694-705`).
All arbitrary program, source/result/post-state and replacement-FFI binders are
retained; HOL's record update keeps the FFI type, as here. The only premises
are source evaluation and the original neutrality predicate; the updated
evaluation is derived. The evaluator closure inherits reals_as_rational_cuts
(SOUNDNESS item 8); no new floating-point agreement is asserted. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_ffi_neutral"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateFfiNeutral {width : Nat} [NeZero width] {C : Type} {F : Type}
    (program : HolProg width) (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (ffi : HolFfiState F)
    (hypothesis : evaluate (program, source) = (result, post) ∧ clockNeutralHOL program) :
    evaluate (program, {source with ffi := ffi}) = (result, {post with ffi := ffi}) := by
  rw [neutralFfiFree (C := C) (F := F) program hypothesis.2 source ffi, hypothesis.1]

end Flapjack.Compiler.Backend.StackProps.EvaluateNeutral
