import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.RawCall

namespace Flapjack.Compiler.Backend.StackRawCall.CallCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open IfCase RawCallCase

/-- Actual direct or indirect callee lookup through the literal code relation.
Flapjack infrastructure: no target evaluation is a premise. -/
theorem callEntry {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (dest : Sum Nat Nat)
    (program : HolProg width)
    (lookup : findCode dest source.regs source.code = some program) :
    ∃ entryInfo : Spt Nat, stateRel entryInfo source target ∧
      findCode dest target.regs target.code = some (compTop entryInfo program) := by
  obtain ⟨code, domain, equality, frames, entries⟩ := relation
  subst target
  have entry : ∀ label, sptLookup label source.code = some program →
      ∃ entryInfo : Spt Nat,
        stateRel entryInfo source {source with code := code} ∧
        sptLookup label code = some (compTop entryInfo program) := by
    intro label found
    obtain ⟨entryInfo, entryFrames, compiled⟩ := entries label program found
    exact ⟨entryInfo, ⟨code, domain, rfl, entryFrames, entries⟩, compiled⟩
  cases dest with
  | inl label => simpa only [findCode] using entry label lookup
  | inr reg =>
      cases value : source.regs.lookup reg with
      | none => simp [findCode, value] at lookup
      | some word =>
          cases word with
          | word bits => simp [findCode, value] at lookup
          | loc label offset =>
              cases offset with
              | zero =>
                  have found : sptLookup label source.code = some program := by
                    simpa only [findCode, value] using lookup
                  simpa only [findCode, value] using entry label found
              | succ offset => simp [findCode, value] at lookup

/-- The original tail-call callee induction hypothesis at its fixed recursive
source, guarded by actual lookup and nonzero clock. Only its compTop component
is used; the unused comp component of the paired motive is omitted. -/
abbrev TailCalleeIH {width : Nat} [NeZero width] (C F : Type)
    (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (source : StackSemStateFiniteExact width C F) : Prop :=
  handler = none → ∀ program, findCode dest source.regs source.code = some program →
    source.clock ≠ 0 →
    ∀ (info : Spt Nat) (target post : StackSemStateFiniteExact width C F)
      (result : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (program, decClock source) = (result, post) ∧
        result ≠ some .error ∧ stateRel info (decClock source) target →
    SimulationResult (compTop info program) info target post result

/-- Canonical roundtrip for the actual imported evaluator state. Flapjack
representation infrastructure with no separate HOL declaration. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Genuine NONE-return Call branch of comp_correct409-446, including arbitrary
direct/indirect lookup, invalid handlers, zero clock and all callee outcomes.
The three original source premises and guarded callee IH establish both
existential simulations. Inherits reals_as_rational_cuts, SOUNDNESS item8. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectCallTail {width : Nat} [NeZero width] {C F : Type}
    (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : TailCalleeIH C F dest handler source)
    (hypothesis : StackSemEvaluate.evaluate (.call none dest handler, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.call none dest handler)) info target post result ∧
    SimulationResult (comp info (.call none dest handler)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  change SimulationResult (.call none dest handler) info target post result ∧
    SimulationResult (.call none dest handler) info target post result
  suffices simulation : SimulationResult (.call none dest handler) info target post result by
    exact ⟨simulation, simulation⟩
  rw [StackSemEvaluate.evaluate_call] at execution
  cases lookup : findCode dest source.regs source.code with
  | none => simp [lookup] at execution; exact False.elim (nonerror execution.1.symm)
  | some program =>
      rw [lookup] at execution
      cases handler with
      | some handler =>
          simp only [Prod.mk.injEq] at execution
          exact False.elim (nonerror execution.1.symm)
      | none =>
          obtain ⟨entryInfo, entryRelation, targetLookup⟩ :=
            callEntry info source target relation dest program lookup
          have clockEq := LoopCase.stateRel_clock info source target relation
          by_cases zero : source.clock = 0
          · simp only [zero, if_true, Prod.mk.injEq] at execution
            obtain ⟨rfl, rfl⟩ := execution
            refine ⟨0, emptyEnv target, (emptyEnv target).stackSpace,
              LoopCase.stateRel_emptyEnv info source target relation, ?_, ?_⟩
            · have targetZero : target.clock = 0 := clockEq.trans zero
              simp only [Nat.add_zero, StackSemEvaluate.evaluate_call, targetLookup,
                targetZero, if_true]
              have update : {target with clock := 0} = target := by rw [← targetZero]
              rw [update]
            · simp
          · simp only [zero, if_false, StackSemEvaluateClock.fixClockEvaluate] at execution
            rcases bodyExecution : StackSemEvaluate.evaluate (program, decClock source) with
              ⟨bodyResult, bodyPost⟩
            rw [bodyExecution] at execution
            by_cases bad : badFunReturn bodyResult = true
            · simp only [bad, if_true, Prod.mk.injEq] at execution
              exact False.elim (nonerror execution.1.symm)
            · simp only [bad, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
              obtain ⟨rfl, rfl⟩ := execution
              obtain ⟨clock, targetPost, space, postRelation, targetExecution, guard⟩ :=
                calleeIH rfl program lookup zero entryInfo (decClock target) bodyPost bodyResult
                  ⟨bodyExecution, nonerror,
                    LoopCase.stateRel_decClock entryInfo source target entryRelation⟩
              have frames : stateOk info source.code := by
                obtain ⟨_, _, _, frames, _⟩ := relation
                exact frames
              have postFrames := stateOk_afterEvaluate info program (decClock source)
                bodyPost bodyResult frames bodyExecution
              refine ⟨clock, targetPost, space,
                stateRel_changeInfo entryInfo info bodyPost targetPost postRelation postFrames,
                ?_, guard⟩
              have targetNonzero : target.clock ≠ 0 := by omega
              have addedNonzero : target.clock + clock ≠ 0 := by omega
              rw [StackSemEvaluate.evaluate_call]
              simp only [targetLookup, addedNonzero, if_false]
              rw [StackSemEvaluateClock.fixClockEvaluate]
              simp only [StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero,
                targetExecution, bad, Bool.false_eq_true, if_false]

end Flapjack.Compiler.Backend.StackRawCall.CallCase
