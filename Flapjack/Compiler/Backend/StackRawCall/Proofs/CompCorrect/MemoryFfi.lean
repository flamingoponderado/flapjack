import Mathlib.Tactic.SplitIfs
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.StackAccess

namespace Flapjack.Compiler.Backend.StackRawCall.MemoryFfiCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps
open IfCase

/-- Four source constructor cases; Flapjack classification infrastructure. -/
inductive MemoryLeaf {width : Nat} [NeZero width] : HolProg width → Prop where
  | shMemOp (op : Compiler.Encoders.Asm.HolMemop) (r a : Nat) (w : BitVec width) :
      MemoryLeaf (.shMemOp op r (.addr a w))
  | codeBufferWrite (r1 r2 : Nat) : MemoryLeaf (.codeBufferWrite r1 r2)
  | dataBufferWrite (r1 r2 : Nat) : MemoryLeaf (.dataBufferWrite r1 r2)
  | ffi (function : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat) :
      MemoryLeaf (.ffi function ptr len ptr2 len2 ret)

/-- Unconditional native code-update transport, including errors, timeout and
FFI final outcomes. Flapjack infrastructure, not an extra simulation premise. -/
theorem evaluate_codeUpdate {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : MemoryLeaf program)
    (source : StackSemStateFiniteExact width C F) (code : Spt (HolProg width)) :
    StackSemEvaluate.evaluate (program, { source with code := code }) =
      let outcome := StackSemEvaluate.evaluate (program, source)
      (outcome.1, { outcome.2 with code := code }) := by
  cases leaf
  case shMemOp op r a w =>
    cases op <;>
      simp [StackSemEvaluate.evaluate_shMemOp, StackSemExpressions.wordExp,
        StackSemShMem.shMemOp, StackSemShMem.shMemLoad, StackSemShMem.shMemStore,
        StackSemShMem.shMemLoadByte, StackSemShMem.shMemStoreByte,
        StackSemShMem.shMemLoad16, StackSemShMem.shMemStore16,
        StackSemShMem.shMemLoad32, StackSemShMem.shMemStore32,
        getVar, emptyEnv, decClock]
    all_goals split_ifs <;> try simp_all
    all_goals repeat' (first | rfl | (split <;> try simp_all))
    all_goals split_ifs <;> try simp_all
    all_goals repeat' (first | rfl | (split <;> try simp_all))
  all_goals
    simp only [StackSemEvaluate.evaluate_codeBufferWrite,
      StackSemEvaluate.evaluate_dataBufferWrite, StackSemEvaluate.evaluate_ffi, getVar]
  all_goals repeat' (first | rfl | (split <;> try simp_all))

/-- Derived preservation of the actual code tree, including error outcomes. -/
theorem evaluate_code_eq {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : MemoryLeaf program)
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
    (program : HolProg width) (leaf : MemoryLeaf program) (info : Spt Nat)
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
The constructor predicate is discharged by each of the four final HOL cases. -/
theorem compCorrectMemory {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : MemoryLeaf program) (info : Spt Nat)
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


/-- Canonical roundtrip of the actual imported evaluator state; representation
infrastructure, without a duplicate carrier or an assumed relation. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness


/-- Full original ShMemOp case, retaining the three source premises and both
existential simulation conclusions. The evaluator inherits the reviewed
reals_as_rational_cuts assurance limit in SOUNDNESS item 8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectShMemOp {width : Nat} [NeZero width] {C F : Type}
    (op : Compiler.Encoders.Asm.HolMemop) (r a : Nat) (w : BitVec width) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.shMemOp op r (.addr a w), source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.shMemOp op r (.addr a w))) info target resultState result ∧
    SimulationResult (comp info (.shMemOp op r (.addr a w))) info target resultState result :=
  compCorrectMemory (.shMemOp op r (.addr a w)) (.shMemOp op r a w)
    info source target resultState result hypothesis

/-- Full original CodeBufferWrite case, retaining the three source premises and both
existential simulation conclusions. The evaluator inherits the reviewed
reals_as_rational_cuts assurance limit in SOUNDNESS item 8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectCodeBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.codeBufferWrite r1 r2, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.codeBufferWrite r1 r2)) info target resultState result ∧
    SimulationResult (comp info (.codeBufferWrite r1 r2)) info target resultState result :=
  compCorrectMemory (.codeBufferWrite r1 r2) (.codeBufferWrite r1 r2)
    info source target resultState result hypothesis

/-- Full original DataBufferWrite case, retaining the three source premises and both
existential simulation conclusions. The evaluator inherits the reviewed
reals_as_rational_cuts assurance limit in SOUNDNESS item 8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectDataBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.dataBufferWrite r1 r2, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.dataBufferWrite r1 r2)) info target resultState result ∧
    SimulationResult (comp info (.dataBufferWrite r1 r2)) info target resultState result :=
  compCorrectMemory (.dataBufferWrite r1 r2) (.dataBufferWrite r1 r2)
    info source target resultState result hypothesis

/-- Full original Ffi case, retaining the three source premises and both
existential simulation conclusions. The evaluator inherits the reviewed
reals_as_rational_cuts assurance limit in SOUNDNESS item 8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectFfi {width : Nat} [NeZero width] {C F : Type}
    (function : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.ffi function ptr len ptr2 len2 ret, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.ffi function ptr len ptr2 len2 ret)) info target resultState result ∧
    SimulationResult (comp info (.ffi function ptr len ptr2 len2 ret)) info target resultState result :=
  compCorrectMemory (.ffi function ptr len ptr2 len2 ret) (.ffi function ptr len ptr2 len2 ret)
    info source target resultState result hypothesis
end Flapjack.Compiler.Backend.StackRawCall.MemoryFfiCase
