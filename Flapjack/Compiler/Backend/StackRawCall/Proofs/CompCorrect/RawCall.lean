import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Loop
import Flapjack.Compiler.Backend.StackProps.EvaluateMono

namespace Flapjack.Compiler.Backend.StackRawCall.RawCallCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open IfCase

/-- Frame preservation derived from actual evaluation. Flapjack infrastructure. -/
theorem stateOk_afterEvaluate {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (program : HolProg width)
    (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (frames : stateOk info source.code)
    (execution : StackSemEvaluate.evaluate (program, source) = (result, post)) :
    stateOk info post.code := by
  have mono := (StackProps.EvaluateMono.evaluateMono program source post result execution).2
  intro key size entry
  obtain ⟨body, lookup⟩ := frames key size entry
  exact ⟨body, (sptSubsptLookup source.code post.code).mp mono key _ lookup⟩

/-- Outer frame information affects only its explicit stateOk obligation.
Flapjack infrastructure retaining the per-entry compilation witnesses. -/
theorem stateRel_changeInfo {width : Nat} [NeZero width] {C F : Type}
    (oldInfo newInfo : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel oldInfo source target) (frames : stateOk newInfo source.code) :
    stateRel newInfo source target := by
  obtain ⟨code, domain, equality, _, entries⟩ := relation
  exact ⟨code, domain, equality, frames, entries⟩

/-- Actual compiled callee lookup derived from the literal relation.
Flapjack infrastructure with no target evaluation premise. -/
theorem rawCallEntry {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (dest : Nat) (first body : HolProg width)
    (lookup : sptLookup dest source.code = some (.seq first body)) :
    ∃ entryInfo : Spt Nat,
      stateRel entryInfo source target ∧
      sptLookup dest target.code = some (.seq (comp entryInfo first) (comp entryInfo body)) := by
  obtain ⟨code, domain, equality, frames, entries⟩ := relation
  obtain ⟨entryInfo, entryFrames, compiled⟩ := entries dest _ lookup
  refine ⟨entryInfo, ⟨code, domain, equality, entryFrames, entries⟩, ?_⟩
  subst target
  simpa only [compTop] using compiled

/-- Actual evaluate_ind callee hypothesis at the fixed recursive source.
Only the comp component of the paired original motive is used. -/
abbrev CalleeIH {width : Nat} [NeZero width] (C F : Type) (dest : Nat)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ first body, sptLookup dest source.code = some (.seq first body) →
    source.clock ≠ 0 → ProgramIH C F body (decClock source)

/-- Canonical roundtrip of the actual imported evaluator state; representation
infrastructure, without a duplicate carrier or an assumed relation. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Genuine RawCall simulation with the original three premises and actual
callee induction hypothesis. Both original existential conclusions remain.
The unused compTop component of the paired callee motive is omitted. Native
compTop preserves the leading Seq, so target dispatch selects the compiled
callee body directly. Frame preservation is derived from evaluateMono.
The full evaluator inherits SOUNDNESS item 8 reals_as_rational_cuts; this
case introduces no real rendering or cross-language equivalence claim. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectRawCall {width : Nat} [NeZero width] {C F : Type}
    (dest : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : CalleeIH C F dest source)
    (hypothesis : StackSemEvaluate.evaluate (.rawCall dest, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.rawCall dest)) info target resultState result ∧
    SimulationResult (comp info (.rawCall dest)) info target resultState result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  change SimulationResult (.rawCall dest) info target resultState result ∧
    SimulationResult (.rawCall dest) info target resultState result
  suffices simulation : SimulationResult (.rawCall dest) info target resultState result by
    exact ⟨simulation, simulation⟩
  rw [StackSemEvaluate.evaluate_rawCall] at execution
  cases lookup : sptLookup dest source.code with
  | none => simp [lookup] at execution; exact False.elim (nonerror execution.1.symm)
  | some program =>
    rw [lookup] at execution
    cases program <;> simp only [destSeq] at execution
    all_goals try (exact False.elim (nonerror (Prod.mk.inj execution).1.symm))
    rename_i first body
    obtain ⟨entryInfo, entryRelation, targetLookup⟩ :=
      rawCallEntry info source target relation dest first body lookup
    have clockEq := LoopCase.stateRel_clock info source target relation
    by_cases zero : source.clock = 0
    · simp only [zero, if_true, Prod.mk.injEq] at execution
      obtain ⟨rfl, rfl⟩ := execution
      refine ⟨0, emptyEnv target, (emptyEnv target).stackSpace,
        LoopCase.stateRel_emptyEnv info source target relation, ?_, ?_⟩
      · simp only [Nat.add_zero, StackSemEvaluate.evaluate_rawCall, targetLookup,
          destSeq]
        have tz : target.clock = 0 := clockEq.trans zero
        simp only [tz, if_true]
        have update : { target with clock := 0 } = target := by
          rw [← tz]
        rw [update]
      · simp
    · simp only [zero, if_false] at execution
      rcases bodyExecution : StackSemEvaluate.evaluate (body, decClock source) with
        ⟨bodyResult, bodyPost⟩
      rw [bodyExecution] at execution
      by_cases bad : badFunReturn bodyResult = true
      · simp only [bad, if_true, Prod.mk.injEq] at execution
        exact False.elim (nonerror execution.1.symm)
      · simp only [bad, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        obtain ⟨clock, targetState, stackSpace, postRelation, targetExecution, guard⟩ :=
          calleeIH first body lookup zero entryInfo (decClock target) bodyPost bodyResult
            ⟨bodyExecution, nonerror,
              LoopCase.stateRel_decClock entryInfo source target entryRelation⟩
        have frames : stateOk info source.code := by
          obtain ⟨_, _, _, frames, _⟩ := relation
          exact frames
        have postFrames := stateOk_afterEvaluate info body (decClock source) bodyPost
          bodyResult frames bodyExecution
        refine ⟨clock, targetState, stackSpace,
          stateRel_changeInfo entryInfo info bodyPost targetState postRelation postFrames,
          ?_, guard⟩
        have targetNonzero : target.clock ≠ 0 := by omega
        have addedNonzero : target.clock + clock ≠ 0 := by omega
        simp only [StackSemEvaluate.evaluate_rawCall, targetLookup, destSeq,
          addedNonzero, if_false,
          StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero,
          targetExecution, bad, Bool.false_eq_true, if_false]

end Flapjack.Compiler.Backend.StackRawCall.RawCallCase
