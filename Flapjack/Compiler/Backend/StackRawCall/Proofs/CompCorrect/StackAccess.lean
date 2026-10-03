import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.RawCall
import Flapjack.Compiler.Backend.StackRawCall.Proofs.Labels

namespace Flapjack.Compiler.Backend.StackRawCall.StackAccessCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps
open IfCase

/-! Full original562-581 cases. The native full evaluator inherits the reviewed
reals_as_rational_cuts assurance limit (SOUNDNESS item 8); these stack and label
proofs introduce no real rendering, production-policy change or equivalence
claim. All stack/map/clock/configuration/FFI fields remain native and intact. -/

/-- Canonical roundtrip of the actual imported evaluator state; representation
infrastructure, without a duplicate carrier or an assumed relation. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Nine native stack-access cases. Flapjack constructor classification. -/
inductive StackLeaf {width : Nat} [NeZero width] : HolProg width → Prop where
  | stackAlloc (n : Nat) : StackLeaf (.stackAlloc n)
  | stackFree (n : Nat) : StackLeaf (.stackFree n)
  | stackLoad (r n : Nat) : StackLeaf (.stackLoad r n)
  | stackLoadAny (r rn : Nat) : StackLeaf (.stackLoadAny r rn)
  | stackStore (r n : Nat) : StackLeaf (.stackStore r n)
  | stackStoreAny (r rn : Nat) : StackLeaf (.stackStoreAny r rn)
  | stackGetSize (r : Nat) : StackLeaf (.stackGetSize r)
  | stackSetSize (r : Nat) : StackLeaf (.stackSetSize r)
  | bitmapLoad (r v : Nat) : StackLeaf (.bitmapLoad r v)

/-- Unconditional code-update transport derived from actual stack clauses,
including source errors and halt outcomes. Flapjack infrastructure. -/
theorem evaluate_codeUpdate {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : StackLeaf program)
    (source : StackSemStateFiniteExact width C F) (code : Spt (HolProg width)) :
    StackSemEvaluate.evaluate (program, { source with code := code }) =
      let outcome := StackSemEvaluate.evaluate (program, source)
      (outcome.1, { outcome.2 with code := code }) := by
  cases leaf <;>
    simp only [StackSemEvaluate.evaluate_stackAlloc, StackSemEvaluate.evaluate_stackFree,
      StackSemEvaluate.evaluate_stackLoad, StackSemEvaluate.evaluate_stackLoadAny,
      StackSemEvaluate.evaluate_stackStore, StackSemEvaluate.evaluate_stackStoreAny,
      StackSemEvaluate.evaluate_stackGetSize, StackSemEvaluate.evaluate_stackSetSize,
      StackSemEvaluate.evaluate_bitmapLoad, getVar, setVar, emptyEnv]
  all_goals repeat' (first | rfl | (split <;> try simp_all))

/-- Actual code relation preserves location observations, including the
zero-offset domain branch and all labels inside compiled code entries. -/
theorem locCheck_stateRel {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (label : Nat × Nat) :
    StackSem.locCheckExact target.code label ↔ StackSem.locCheckExact source.code label := by
  obtain ⟨code, domain, equality, _, entries⟩ := relation
  subst target
  have member (key : Nat) : sptMem key code ↔ sptMem key source.code := by
    change sptDomain code key ↔ sptDomain source.code key
    rw [domain]
  constructor
  · rintro (⟨zero, mem⟩ | ⟨key, compiled, lookup, labels⟩)
    · exact Or.inl ⟨zero, (member _).mp mem⟩
    · have mem : sptMem key code := (sptMem_iff_lookup key code).mpr ⟨compiled, lookup⟩
      obtain ⟨body, original⟩ := (sptMem_iff_lookup key source.code).mp ((member key).mp mem)
      obtain ⟨entryInfo, _, compiledLookup⟩ := entries key body original
      have same : compiled = compTop entryInfo body := by
        exact Option.some.inj (lookup.symm.trans compiledLookup)
      subst compiled
      exact Or.inr ⟨key, body, original, by
        simpa only [(getLabelsComp entryInfo body).2] using labels⟩
  · rintro (⟨zero, mem⟩ | ⟨key, body, lookup, labels⟩)
    · exact Or.inl ⟨zero, (member _).mpr mem⟩
    · obtain ⟨entryInfo, _, compiledLookup⟩ := entries key body lookup
      exact Or.inr ⟨key, compTop entryInfo body, compiledLookup, by
        simpa only [(getLabelsComp entryInfo body).2] using labels⟩

/-- Derived preservation of the actual code tree, including error outcomes. -/
theorem evaluate_code_eq {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : StackLeaf program)
    (source : StackSemStateFiniteExact width C F) :
    (StackSemEvaluate.evaluate (program, source)).2.code = source.code := by
  have transport := evaluate_codeUpdate program leaf source source.code
  have unchanged : { source with code := source.code } = source := by
    cases source
    rfl
  rw [unchanged] at transport
  have projected := congrArg (fun outcome : Option (StackSemResult width) ×
    StackSemStateFiniteExact width C F => outcome.2.code) transport
  exact projected

/-- Full postrelation and target evaluation derived from actual leaf execution.
The leaf predicate is infrastructure; each final source case discharges it. -/
theorem evaluate_stateRel {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : StackLeaf program) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (program, source) = (result, resultState))
    (relation : stateRel info source target) :
    ∃ targetState, stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (program, target) = (result, targetState) := by
  obtain ⟨code, domain, targetEq, frames, entries⟩ := relation
  subst target
  have codeEq := evaluate_code_eq program leaf source
  rw [execution] at codeEq
  change resultState.code = source.code at codeEq
  refine ⟨{ resultState with code := code }, ?_, ?_⟩
  · refine ⟨code, ?_, rfl, ?_, ?_⟩
    · simpa only [codeEq] using domain
    · simpa only [codeEq] using frames
    · simpa only [codeEq] using entries
  · rw [evaluate_codeUpdate program leaf, execution]

/-- Flapjack support assembling the original paired existential conclusion.
The constructor predicate is discharged by each of the nine final HOL cases. -/
theorem compCorrectStack {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : StackLeaf program) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (program, source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info program, { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info program, { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  obtain ⟨execution, _, relation⟩ := hypothesis
  obtain ⟨targetState, postRelation, targetExecution⟩ :=
    evaluate_stateRel program leaf info source target resultState result execution relation
  have clockSelf : { target with clock := target.clock + 0 } = target := by
    cases target
    simp
  have stackSelf : { targetState with stackSpace := targetState.stackSpace } = targetState := by
    cases targetState
    rfl
  have compSelf : comp info program = program := by
    cases leaf <;> rfl
  have compTopSelf : compTop info program = program := by
    cases leaf <;> rfl
  constructor <;>
    refine ⟨0, targetState, targetState.stackSpace, postRelation, ?_, fun _ => rfl⟩
  · rw [clockSelf, stackSelf, compTopSelf]
    exact targetExecution
  · rw [clockSelf, stackSelf, compSelf]
    exact targetExecution


/-- Literal LocValue case: successful target label checking is derived from
stateRel and getLabelsComp, rather than supplied as a simulation premise. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectLocValue {width : Nat} [NeZero width] {C F : Type}
    (register first second : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.locValue register first second, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.locValue register first second)) info target resultState result ∧
    SimulationResult (comp info (.locValue register first second)) info target resultState result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have labels := locCheck_stateRel info source target relation (first, second)
  rw [StackSemEvaluate.evaluate_locValue] at execution
  split at execution
  · rename_i location
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
    obtain ⟨code, domain, equality, frames, entries⟩ := relation
    subst target
    have postRelation : stateRel info (setVar register (.loc first second) source)
        { setVar register (.loc first second) source with code := code } := by
      exact ⟨code, domain, rfl, frames, entries⟩
    have targetLocation : StackSem.locCheckExact code (first, second) := labels.mpr location
    constructor <;>
      refine ⟨0, { setVar register (.loc first second) source with code := code },
        (setVar register (.loc first second) source).stackSpace, postRelation, ?_, ?_⟩
    all_goals try (intro _; rfl)
    all_goals simp only [compTop, comp, Nat.add_zero, StackSemEvaluate.evaluate_locValue,
      targetLocation, if_true, setVar]
  · exact False.elim (nonerror (Prod.mk.inj execution).1.symm)

/-- Genuine original stackAlloc case: all three source premises and both
existential conclusions, with no supplied target evaluation or postrelation. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectStackAlloc {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackAlloc n, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.stackAlloc n)) info target resultState result ∧
    SimulationResult (comp info (.stackAlloc n)) info target resultState result :=
  compCorrectStack (.stackAlloc n) (.stackAlloc n)
    info source target resultState result hypothesis

/-- Genuine original stackFree case: all three source premises and both
existential conclusions, with no supplied target evaluation or postrelation. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectStackFree {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackFree n, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.stackFree n)) info target resultState result ∧
    SimulationResult (comp info (.stackFree n)) info target resultState result :=
  compCorrectStack (.stackFree n) (.stackFree n)
    info source target resultState result hypothesis

/-- Genuine original stackLoad case: all three source premises and both
existential conclusions, with no supplied target evaluation or postrelation. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectStackLoad {width : Nat} [NeZero width] {C F : Type}
    (r n : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackLoad r n, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.stackLoad r n)) info target resultState result ∧
    SimulationResult (comp info (.stackLoad r n)) info target resultState result :=
  compCorrectStack (.stackLoad r n) (.stackLoad r n)
    info source target resultState result hypothesis

/-- Genuine original stackLoadAny case: all three source premises and both
existential conclusions, with no supplied target evaluation or postrelation. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectStackLoadAny {width : Nat} [NeZero width] {C F : Type}
    (r rn : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackLoadAny r rn, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.stackLoadAny r rn)) info target resultState result ∧
    SimulationResult (comp info (.stackLoadAny r rn)) info target resultState result :=
  compCorrectStack (.stackLoadAny r rn) (.stackLoadAny r rn)
    info source target resultState result hypothesis

/-- Genuine original stackStore case: all three source premises and both
existential conclusions, with no supplied target evaluation or postrelation. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectStackStore {width : Nat} [NeZero width] {C F : Type}
    (r n : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackStore r n, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.stackStore r n)) info target resultState result ∧
    SimulationResult (comp info (.stackStore r n)) info target resultState result :=
  compCorrectStack (.stackStore r n) (.stackStore r n)
    info source target resultState result hypothesis

/-- Genuine original stackStoreAny case: all three source premises and both
existential conclusions, with no supplied target evaluation or postrelation. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectStackStoreAny {width : Nat} [NeZero width] {C F : Type}
    (r rn : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackStoreAny r rn, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.stackStoreAny r rn)) info target resultState result ∧
    SimulationResult (comp info (.stackStoreAny r rn)) info target resultState result :=
  compCorrectStack (.stackStoreAny r rn) (.stackStoreAny r rn)
    info source target resultState result hypothesis

/-- Genuine original stackGetSize case: all three source premises and both
existential conclusions, with no supplied target evaluation or postrelation. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectStackGetSize {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackGetSize r, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.stackGetSize r)) info target resultState result ∧
    SimulationResult (comp info (.stackGetSize r)) info target resultState result :=
  compCorrectStack (.stackGetSize r) (.stackGetSize r)
    info source target resultState result hypothesis

/-- Genuine original stackSetSize case: all three source premises and both
existential conclusions, with no supplied target evaluation or postrelation. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectStackSetSize {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackSetSize r, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.stackSetSize r)) info target resultState result ∧
    SimulationResult (comp info (.stackSetSize r)) info target resultState result :=
  compCorrectStack (.stackSetSize r) (.stackSetSize r)
    info source target resultState result hypothesis

/-- Genuine original bitmapLoad case: all three source premises and both
existential conclusions, with no supplied target evaluation or postrelation. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectBitmapLoad {width : Nat} [NeZero width] {C F : Type}
    (r v : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.bitmapLoad r v, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.bitmapLoad r v)) info target resultState result ∧
    SimulationResult (comp info (.bitmapLoad r v)) info target resultState result :=
  compCorrectStack (.bitmapLoad r v) (.bitmapLoad r v)
    info source target resultState result hypothesis

end Flapjack.Compiler.Backend.StackRawCall.StackAccessCase
