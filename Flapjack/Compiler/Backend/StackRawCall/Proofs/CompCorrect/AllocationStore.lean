import Mathlib.Tactic.ByContra
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.MemoryFfi

namespace Flapjack.Compiler.Backend.StackRawCall.AllocationStoreCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps
open IfCase

/-- Flapjack infrastructure: actual GC cannot observe the code field. All
collector inputs and outcomes are retained, including failed decoding. -/
theorem gc_codeUpdate {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (code : Spt (HolProg width)) :
    StackSemAllocation.gc { source with code := code } =
      (StackSemAllocation.gc source).map (fun post => { post with code := code }) := by
  simp only [StackSemAllocation.gc]
  split_ifs <;> simp_all
  all_goals repeat' (first | rfl | (split <;> try simp_all))

/-- A successful original optional stub check yields the target stub through
stateRel's actual per-entry compilation witness. It is not invariant under an
arbitrary code replacement. Flapjack constructor infrastructure. -/
theorem checkStoreConstsOpt_target {width : Nat} [NeZero width] {C F : Type}
    (first second : Nat) (stub : Option Nat) (info : Spt Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target)
    (checked : StackSemStoreConstsGuard.checkStoreConstsOpt first second stub source.code = true) :
    StackSemStoreConstsGuard.checkStoreConstsOpt first second stub target.code = true := by
  obtain ⟨code, _, targetEq, _, entries⟩ := relation
  subst target
  cases stub with
  | none => rfl
  | some label =>
      have lookup := (StackSemStoreConstsGuard.checkStoreConstsOpt_some_iff first second label source.code).mp checked
      obtain ⟨entryInfo, _, compiledLookup⟩ := entries label _ lookup
      apply (StackSemStoreConstsGuard.checkStoreConstsOpt_some_iff first second label code).mpr
      simpa [compTop, comp] using compiledLookup


/-- Actual allocation code transport, including GC failure, post-GC errors and
Halt Word1 after environment clearing. Flapjack infrastructure. -/
theorem alloc_codeUpdate {width : Nat} [NeZero width] {C F : Type}
    (amount : BitVec width) (source : StackSemStateFiniteExact width C F)
    (code : Spt (HolProg width)) :
    StackSemAllocation.alloc amount { source with code := code } =
      let outcome := StackSemAllocation.alloc amount source
      (outcome.1, { outcome.2 with code := code }) := by
  simp only [StackSemAllocation.alloc, setStore]
  have transport := gc_codeUpdate (setStore .allocSize (.word amount) source) code
  dsimp only [setStore] at transport
  rw [transport]
  cases h : StackSemAllocation.gc (setStore .allocSize (.word amount) source) <;>
    simp only [setStore] at h
  all_goals simp only [h, Option.map_none, Option.map_some]
  all_goals repeat' (first | rfl | (split <;> try simp_all [emptyEnv]))

/-- Unconditional actual Alloc evaluator transport. -/
theorem evaluateAlloc_codeUpdate {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (source : StackSemStateFiniteExact width C F)
    (code : Spt (HolProg width)) :
    StackSemEvaluate.evaluate (.alloc register, { source with code := code }) =
      let outcome := StackSemEvaluate.evaluate (.alloc register, source)
      (outcome.1, { outcome.2 with code := code }) := by
  simp only [StackSemEvaluate.evaluate_alloc, getVar]
  split <;> try rfl
  split <;> try rfl
  exact alloc_codeUpdate _ source code

/-- Actual store-constant execution transport independent of the optional
code guard; preserves copy failure and unset-register behavior. -/
theorem storeConstSem_codeUpdate {width : Nat} [NeZero width] {C F : Type}
    (first second : Nat) (source : StackSemStateFiniteExact width C F)
    (code : Spt (HolProg width)) :
    StackSemStoreConsts.storeConstSem (resultWidth := width) first second { source with code := code } =
      let outcome := StackSemStoreConsts.storeConstSem (resultWidth := width) first second source
      (outcome.1, { outcome.2 with code := code }) := by
  simp only [StackSemStoreConsts.storeConstSem, getVar, setVar]
  all_goals repeat' (first | rfl | (split <;> try simp_all))

/-- Real code equality and postrelation derived from unconditional operation
transport. Flapjack infrastructure; final case theorems derive transport from
native clauses rather than assume a target execution. -/
theorem postRelationOfTransport {width : Nat} [NeZero width] {C F : Type}
    (operation : StackSemStateFiniteExact width C F →
      Option (StackSemResult width) × StackSemStateFiniteExact width C F)
    (source target post : StackSemStateFiniteExact width C F) (info : Spt Nat)
    (result : Option (StackSemResult width))
    (transport : ∀ code, operation { source with code := code } =
      let outcome := operation source
      (outcome.1, { outcome.2 with code := code }))
    (execution : operation source = (result, post))
    (relation : stateRel info source target) :
    ∃ targetPost, stateRel info post targetPost ∧ operation target = (result, targetPost) := by
  have self := transport source.code
  have unchanged : { source with code := source.code } = source := by cases source; rfl
  rw [unchanged, execution] at self
  have codeEq : post.code = source.code := congrArg (fun outcome => outcome.2.code) self
  obtain ⟨code, domain, targetEq, frames, entries⟩ := relation
  subst target
  refine ⟨{ post with code := code }, ⟨code, ?_, rfl, ?_, ?_⟩, ?_⟩
  · simpa only [codeEq] using domain
  · simpa only [codeEq] using frames
  · simpa only [codeEq] using entries
  · rw [transport code, execution]

/-- Actual successful source StoreConsts dispatch supplies all guards. The
compiled optional stub guard is independently derived from stateRel. -/
theorem evaluateStoreConsts_stateRel {width : Nat} [NeZero width] {C F : Type}
    (first second : Nat) (stub : Option Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (.storeConsts first second stub, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    ∃ targetPost, stateRel info post targetPost ∧
      StackSemEvaluate.evaluate (.storeConsts first second stub, target) = (result, targetPost) := by
  have useStore : ¬ (¬ source.useStore) := by
    intro h
    rw [StackSemEvaluate.evaluate_storeConsts, if_pos h] at execution
    exact nonerror (Prod.mk.inj execution).1.symm
  have useAlloc : ¬ (¬ source.useAlloc ∧ stub.isSome) := by
    intro h
    rw [StackSemEvaluate.evaluate_storeConsts, if_neg useStore, if_pos h] at execution
    exact nonerror (Prod.mk.inj execution).1.symm
  have checked : StackSemStoreConstsGuard.checkStoreConstsOpt first second stub source.code = true := by
    by_contra h
    rw [StackSemEvaluate.evaluate_storeConsts, if_neg useStore, if_neg useAlloc, if_pos h] at execution
    exact nonerror (Prod.mk.inj execution).1.symm
  have targetChecked := checkStoreConstsOpt_target first second stub info source target relation checked
  have sourceBody : StackSemStoreConsts.storeConstSem (resultWidth := width) first second source = (result, post) := by
    simpa only [StackSemEvaluate.evaluate_storeConsts, if_neg useStore, if_neg useAlloc,
      checked, Bool.true_eq, not_true_eq_false, if_false] using execution
  obtain ⟨targetPost, postRelation, targetBody⟩ := postRelationOfTransport
    (StackSemStoreConsts.storeConstSem (resultWidth := width) first second)
    source target post info result (storeConstSem_codeUpdate first second source) sourceBody relation
  refine ⟨targetPost, postRelation, ?_⟩
  obtain ⟨code, _, targetEq, _, _⟩ := relation
  subst target
  simpa only [StackSemEvaluate.evaluate_storeConsts, if_neg useStore, if_neg useAlloc,
    targetChecked, Bool.true_eq, not_true_eq_false, if_false] using targetBody

/-- Canonical roundtrip of the actual imported evaluator state; representation
infrastructure, without a duplicate carrier or an assumed relation. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness



/-- Full original Alloc case153-163: original three source premises and both
existential simulations. Native GC/store-copy outcomes and the target optional
stub guard are derived. Inherits reals_as_rational_cuts, SOUNDNESS item8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectAlloc {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.alloc register, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.alloc register)) info target post result ∧
    SimulationResult (comp info (.alloc register)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  obtain ⟨targetPost, postRelation, targetExecution⟩ := postRelationOfTransport (fun state => StackSemEvaluate.evaluate (.alloc register, state))
      source target post info result (evaluateAlloc_codeUpdate register source) execution relation
  have clockSelf : { target with clock := target.clock + 0 } = target := by
    cases target
    simp
  have stackSelf : { targetPost with stackSpace := targetPost.stackSpace } = targetPost := by
    cases targetPost
    rfl
  constructor <;>
    refine ⟨0, targetPost, targetPost.stackSpace, postRelation, ?_, fun _ => rfl⟩ <;>
    simpa only [clockSelf, stackSelf, compTop, comp] using targetExecution

/-- Full original StoreConsts case153-163: original three source premises and both
existential simulations. Native GC/store-copy outcomes and the target optional
stub guard are derived. Inherits reals_as_rational_cuts, SOUNDNESS item8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStoreConsts {width : Nat} [NeZero width] {C F : Type}
    (first second : Nat) (stub : Option Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.storeConsts first second stub, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.storeConsts first second stub)) info target post result ∧
    SimulationResult (comp info (.storeConsts first second stub)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  obtain ⟨targetPost, postRelation, targetExecution⟩ := evaluateStoreConsts_stateRel first second stub info source target post result
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
end Flapjack.Compiler.Backend.StackRawCall.AllocationStoreCase
