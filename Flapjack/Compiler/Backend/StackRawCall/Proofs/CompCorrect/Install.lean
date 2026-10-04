import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.AllocationStore

namespace Flapjack.Compiler.Backend.StackRawCall.InstallCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps
open IfCase

/-- Flapjack infrastructure: Install's old-code-left-biased union preserves
every frame allocation already witnessed in the original code. -/
theorem stateOk_union {width : Nat} [NeZero width] (info : Spt Nat)
    (old added : Spt (HolProg width)) (frames : stateOk info old) :
    stateOk info (sptUnion old added) := by
  intro n v entry
  obtain ⟨body, lookup⟩ := frames n v entry
  refine ⟨body, ?_⟩
  simp only [sptLookup_sptUnion, lookup]

/-- Flapjack infrastructure for the actual Install update. Old entries retain
their original frame witness; newly visible entries use empty information.
Equal old domains ensure that a new source entry is also new on the target.
The result is a relation on the full updated state, not an evaluation premise. -/
theorem stateRel_union {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target updated : StackSemStateFiniteExact width C F)
    (added : Spt (HolProg width)) (relation : stateRel info source target)
    (codeEq : updated.code = sptUnion source.code added) :
    stateRel info updated { updated with code := sptUnion target.code added } := by
  obtain ⟨code, domain, targetEq, frames, entries⟩ := relation
  subst target
  refine ⟨sptUnion code added, ?_, rfl, ?_, ?_⟩
  · simp only [codeEq, sptDomain_sptUnion, domain]
  · rw [codeEq]
    exact stateOk_union info source.code added frames
  · intro n body entry
    rw [codeEq, sptLookup_sptUnion] at entry
    cases old : sptLookup n source.code with
    | some oldBody =>
        simp only [old, Option.some.injEq] at entry
        subst oldBody
        obtain ⟨entryInfo, entryFrames, targetEntry⟩ := entries n body old
        refine ⟨entryInfo, ?_, ?_⟩
        · rw [codeEq]
          exact stateOk_union entryInfo source.code added entryFrames
        · simp only [sptLookup_sptUnion, targetEntry]
    | none =>
        have targetNone : sptLookup n code = none := by
          have sameDomain := congrFun domain n
          simp only [sptDomain, old, Option.isSome_none, Bool.false_eq_true] at sameDomain
          cases found : sptLookup n code <;> simp_all
        refine ⟨.ln, stateOk_empty updated.code, ?_⟩
        simpa only [sptLookup_sptUnion, targetNone, old, (compLn info body).1] using entry

/-- Flapjack infrastructure deriving Install's actual target execution and
full postrelation from the source execution. Every buffer, oracle, compiler,
register and error branch is retained; no target outcome is assumed. -/
theorem evaluateInstall_stateRel {width : Nat} [NeZero width] {C F : Type}
    (ptr len dptr dlen ret : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (.install ptr len dptr dlen ret, source) =
      (result, post)) (nonerror : result ≠ some .error)
    (relation : stateRel info source target) :
    ∃ targetPost, stateRel info post targetPost ∧
      StackSemEvaluate.evaluate (.install ptr len dptr dlen ret, target) =
        (result, targetPost) := by
  classical
  obtain ⟨code, domain, targetEq, frames, entries⟩ := relation
  subst target
  have originalRelation : stateRel info source {source with code := code} :=
    ⟨code, domain, rfl, frames, entries⟩
  simp only [StackSemEvaluate.evaluate_install, getVar] at execution ⊢
  split at execution <;> try simp_all
  split at execution <;> try simp_all
  split at execution <;> try simp_all
  split at execution <;> try simp_all
  obtain ⟨rfl, rfl⟩ := execution
  exact stateRel_union info source _ _ _ originalRelation rfl

/-- Canonical roundtrip of the imported evaluator state. Representation
infrastructure; no separate HOL declaration or duplicate state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original Install case520-539: the original three premises imply both
existential simulations, including actual native oracle/compiler/buffer updates.
Old entries win the union; newly visible entries use empty frame information.
Configuration equality is internal classical decidability, not an extra source
premise. Inherits reals_as_rational_cuts, SOUNDNESS item8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectInstall {width : Nat} [NeZero width] {C F : Type}
    (ptr len dptr dlen ret : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.install ptr len dptr dlen ret, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.install ptr len dptr dlen ret)) info target post result ∧
    SimulationResult (comp info (.install ptr len dptr dlen ret)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  obtain ⟨targetPost, postRelation, targetExecution⟩ :=
    evaluateInstall_stateRel ptr len dptr dlen ret info source target post result
      execution nonerror relation
  have clockSelf : { target with clock := target.clock + 0 } = target := by
    cases target
    simp
  have stackSelf : { targetPost with stackSpace := targetPost.stackSpace } = targetPost := by
    cases targetPost
    rfl
  constructor <;>
    refine ⟨0, targetPost, targetPost.stackSpace, postRelation, ?_, fun _ => rfl⟩ <;>
    simpa only [clockSelf, stackSelf, compTop, comp] using targetExecution

end Flapjack.Compiler.Backend.StackRawCall.InstallCase
