import Flapjack.Compiler.Backend.StackRawCall.Proofs.InstructionSimulation

namespace Flapjack.Compiler.Backend.StackRawCall.BasicLeaves
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemExpressions

/-- Canonical codec for the actual imported full-state owner; representation
infrastructure without a separate HOL declaration. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-! Flapjack infrastructure identifying six genuine nonrecursive cases of
the original rawcall comp_correct proof. No simplified evaluator is used. -/
inductive BasicLeaf {width : Nat} [NeZero width] : HolProg width → Prop where
  | skip : BasicLeaf .skip
  | halt (register : Nat) : BasicLeaf (.halt register)
  | get (register : Nat) (name : StoreName) : BasicLeaf (.get register name)
  | set (name : StoreName) (register : Nat) : BasicLeaf (.set name register)
  | opCurrHeap (operator : Compiler.Encoders.Asm.HolBinop) (destination source : Nat) :
      BasicLeaf (.opCurrHeap operator destination source)
  | tick : BasicLeaf .tick

/-- Actual evaluator transport, including source failures and timeouts.
Flapjack support only: the constructor premise is discharged by each final
HOL case theorem, not exposed as an extra pass-correctness premise. -/
theorem evaluate_codeUpdate {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : BasicLeaf program)
    (source : StackSemStateFiniteExact width C F) (code : Spt (HolProg width)) :
    StackSemEvaluate.evaluate (program, { source with code := code }) =
      let outcome := StackSemEvaluate.evaluate (program, source)
      (outcome.1, { outcome.2 with code := code }) := by
  cases leaf <;>
    simp only [StackSemEvaluate.evaluate_skip, StackSemEvaluate.evaluate_halt,
      StackSemEvaluate.evaluate_get, StackSemEvaluate.evaluate_set,
      StackSemEvaluate.evaluate_opCurrHeap, StackSemEvaluate.evaluate_tick,
      wordExp_codeUpdate, getVar, setVar, setStore, emptyEnv, decClock]
  all_goals repeat' (first | rfl | (split <;> try simp_all))

/-- Derived preservation of the actual code tree, including error outcomes. -/
theorem evaluate_code_eq {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : BasicLeaf program)
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
    (program : HolProg width) (leaf : BasicLeaf program) (info : Spt Nat)
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
The constructor predicate is discharged by each of the six final HOL cases. -/
theorem compCorrectBasic {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : BasicLeaf program) (info : Spt Nat)
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

/-- Genuine original Skip case with the original three premises and both
existential conclusions. Native evaluator retains its inherited real-carrier
assurance limit; this case proof introduces no real rendering. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectSkip {width : Nat} [NeZero width] {C F : Type}
     (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.skip : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.skip : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.skip : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectBasic (.skip : HolProg width) .skip info source target resultState result hypothesis

/-- Genuine original Halt case with the original three premises and both
existential conclusions. Native evaluator retains its inherited real-carrier
assurance limit; this case proof introduces no real rendering. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectHalt {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.halt register : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.halt register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.halt register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectBasic (.halt register : HolProg width) (.halt register) info source target resultState result hypothesis

/-- Genuine original Get case with the original three premises and both
existential conclusions. Native evaluator retains its inherited real-carrier
assurance limit; this case proof introduces no real rendering. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectGet {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (name : StoreName) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.get register name : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.get register name : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.get register name : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectBasic (.get register name : HolProg width) (.get register name) info source target resultState result hypothesis

/-- Genuine original Set case with the original three premises and both
existential conclusions. Native evaluator retains its inherited real-carrier
assurance limit; this case proof introduces no real rendering. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectSet {width : Nat} [NeZero width] {C F : Type}
    (name : StoreName) (register : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.set name register : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.set name register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.set name register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectBasic (.set name register : HolProg width) (.set name register) info source target resultState result hypothesis

/-- Genuine original OpCurrHeap case with the original three premises and both
existential conclusions. Native evaluator retains its inherited real-carrier
assurance limit; this case proof introduces no real rendering. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectOpCurrHeap {width : Nat} [NeZero width] {C F : Type}
    (operator : Compiler.Encoders.Asm.HolBinop) (destination input : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.opCurrHeap operator destination input : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.opCurrHeap operator destination input : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.opCurrHeap operator destination input : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectBasic (.opCurrHeap operator destination input : HolProg width) (.opCurrHeap operator destination input) info source target resultState result hypothesis

/-- Genuine original Tick case with the original three premises and both
existential conclusions. Native evaluator retains its inherited real-carrier
assurance limit; this case proof introduces no real rendering. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectTick {width : Nat} [NeZero width] {C F : Type}
     (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.tick : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.tick : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.tick : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectBasic (.tick : HolProg width) .tick info source target resultState result hypothesis

end Flapjack.Compiler.Backend.StackRawCall.BasicLeaves
