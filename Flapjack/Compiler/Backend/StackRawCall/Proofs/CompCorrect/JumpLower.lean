import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.RawCall

namespace Flapjack.Compiler.Backend.StackRawCall.JumpLowerCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open IfCase RawCallCase

/-- Actual arbitrary callee lookup and its independent frame information,
derived from stateRel. Flapjack infrastructure, not a supplied target run. -/
theorem calleeEntry {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (dest : Nat) (program : HolProg width)
    (lookup : sptLookup dest source.code = some program) :
    ∃ entryInfo : Spt Nat, stateRel entryInfo source target ∧
      sptLookup dest target.code = some (compTop entryInfo program) := by
  obtain ⟨code, domain, equality, _, entries⟩ := relation
  obtain ⟨entryInfo, frames, compiled⟩ := entries dest program lookup
  refine ⟨entryInfo, ⟨code, domain, equality, frames, entries⟩, ?_⟩
  subst target
  exact compiled

/-- The compTop component of the original paired recursive motive.
Flapjack notation; the unused comp component is omitted for this case. -/
abbrev TopProgramIH {width : Nat} [NeZero width] (C F : Type) (program : HolProg width)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (info : Spt Nat) (target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)),
    StackSemEvaluate.evaluate (program, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target →
    SimulationResult (compTop info program) info target post result

/-- Actual selected-callee evaluate_ind hypothesis at the fixed decClock
source. Operand reads, the unsigned comparison, code lookup and nonzero clock
are precisely the guards of the original recursive call. -/
abbrev JumpIH {width : Nat} [NeZero width] (C F : Type) (r1 r2 dest : Nat)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (left right : BitVec width) (program : HolProg width),
    StackSemStateOps.getVar r1 source = some (.word left) →
    StackSemStateOps.getVar r2 source = some (.word right) →
    Compiler.Encoders.Asm.wordCmpHOL .lower left right = true →
    sptLookup dest source.code = some program →
    source.clock ≠ 0 → TopProgramIH C F program (decClock source)

/-- Canonical roundtrip of the actual imported evaluator state; representation
infrastructure, without a duplicate carrier or an assumed relation. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Genuine original JumpLower case, preserving both original existential
conclusions and the actual selected-callee induction hypothesis. The unused
comp component of the paired callee motive is omitted; actual target code
entries contain compTop. Source nonError derives callee nonError and valid
return dispatch. Full evaluateMono derives the outer frame-info postcondition.
The full native evaluator inherits reals_as_rational_cuts (SOUNDNESS item 8);
this case introduces no real rendering or HOL-to-Lean equivalence claim. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectJumpLower {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 dest : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : JumpIH C F r1 r2 dest source)
    (hypothesis : StackSemEvaluate.evaluate (.jumpLower r1 r2 dest, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.jumpLower r1 r2 dest)) info target post result ∧
    SimulationResult (comp info (.jumpLower r1 r2 dest)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  change SimulationResult (.jumpLower r1 r2 dest) info target post result ∧
    SimulationResult (.jumpLower r1 r2 dest) info target post result
  suffices simulation : SimulationResult (.jumpLower r1 r2 dest) info target post result by
    exact ⟨simulation, simulation⟩
  rw [StackSemEvaluate.evaluate_jumpLower] at execution
  split at execution
  · rename_i left right firstRead secondRead
    split at execution
    · rename_i lower
      simp only [findCode] at execution
      cases lookup : sptLookup dest source.code with
      | none =>
        simp only [lookup, Prod.mk.injEq] at execution
        exact False.elim (nonerror execution.1.symm)
      | some program =>
        rw [lookup] at execution
        obtain ⟨entryInfo, entryRelation, targetLookup⟩ :=
          calleeEntry info source target relation dest program lookup
        have clockEq := LoopCase.stateRel_clock info source target relation
        by_cases zero : source.clock = 0
        · simp only [zero, if_true, Prod.mk.injEq] at execution
          obtain ⟨rfl, rfl⟩ := execution
          refine ⟨0, emptyEnv target, (emptyEnv target).stackSpace,
            LoopCase.stateRel_emptyEnv info source target relation, ?_, ?_⟩
          · simp only [Nat.add_zero, StackSemEvaluate.evaluate_jumpLower,
              getVar_targetClock info source target relation, firstRead, secondRead,
              lower, if_true, findCode, targetLookup]
            have tz : target.clock = 0 := clockEq.trans zero
            simp only [tz, if_true]
            have update : { target with clock := 0 } = target := by rw [← tz]
            rw [update]
          · simp
        · simp only [zero, if_false] at execution
          rcases bodyExecution : StackSemEvaluate.evaluate (program, decClock source) with
            ⟨bodyResult, bodyPost⟩
          rw [bodyExecution] at execution
          by_cases bad : badFunReturn bodyResult = true
          · simp only [bad, if_true, Prod.mk.injEq] at execution
            exact False.elim (nonerror execution.1.symm)
          · simp only [bad, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
            obtain ⟨rfl, rfl⟩ := execution
            obtain ⟨clock, targetState, stackSpace, postRelation, targetExecution, guard⟩ :=
              calleeIH left right program firstRead secondRead lower lookup zero
                entryInfo (decClock target) bodyPost bodyResult
                ⟨bodyExecution, nonerror,
                  LoopCase.stateRel_decClock entryInfo source target entryRelation⟩
            have frames : stateOk info source.code := by
              obtain ⟨_, _, _, frames, _⟩ := relation
              exact frames
            have postFrames := stateOk_afterEvaluate info program (decClock source) bodyPost
              bodyResult frames bodyExecution
            refine ⟨clock, targetState, stackSpace,
              stateRel_changeInfo entryInfo info bodyPost targetState postRelation postFrames,
              ?_, guard⟩
            have targetNonzero : target.clock ≠ 0 := by omega
            have addedNonzero : target.clock + clock ≠ 0 := by omega
            simp only [StackSemEvaluate.evaluate_jumpLower,
              getVar_targetClock info source target relation, firstRead, secondRead,
              lower, if_true, findCode, targetLookup, addedNonzero, if_false,
              StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero,
              targetExecution, bad, Bool.false_eq_true, if_false]
    · rename_i notLower
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      refine ⟨0, target, target.stackSpace, relation, ?_, fun _ => rfl⟩
      simp only [StackSemEvaluate.evaluate_jumpLower,
        getVar_targetClock info source target relation, firstRead, secondRead,
        notLower, Bool.false_eq_true, if_false]
      have update : { target with clock := target.clock + 0 } = target := by
        cases target
        simp
      rw [update]
  · exact False.elim (nonerror (Prod.mk.inj execution).1.symm)

end Flapjack.Compiler.Backend.StackRawCall.JumpLowerCase
