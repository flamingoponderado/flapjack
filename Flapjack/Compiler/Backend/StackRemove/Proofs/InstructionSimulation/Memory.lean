import Flapjack.Compiler.Backend.StackRemove.Proofs.MemoryStores
import Flapjack.Compiler.Backend.StackRemove.Proofs.MemoryLoads
import Flapjack.Compiler.Backend.StackRemove.Proofs.InstructionSimulation.Atoms

namespace Flapjack.Compiler.Backend.StackRemove.InstructionSimulation.Memory
open Flapjack Compiler.Encoders.Asm

/-- Canonical codec for the imported actual state, Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Complete genuine Mem case of the original instruction theorem, including
all eight opcodes and the native address carrier. Source failures are excluded
by its original success premise; successful target runs and full post-state
relations are derived from the original bounds and separated heap relation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRelInstMem {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer register : Nat)
    (operator : HolMemop) (address : HolAddr width)
    (source target postSource : StackSemStateFiniteExact width C F)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      StackProps.regBoundInst (.mem operator register address) pointer ∧
      StackSemInst.instHOL (.mem operator register address) source = some postSource) :
    ∃ postTarget, StackSemInst.instHOL (.mem operator register address) target = some postTarget ∧
      stateRelHOL jump bounds pointer postSource postTarget := by
  rcases hypothesis with ⟨relation, bound, run⟩
  cases address with
  | addr base offset =>
    simp only [StackProps.regBoundInst] at bound
    have addressBound : StackProps.regBoundExp
        (.op .add [.var base, .const offset]) pointer := by
      simp only [StackProps.regBoundExp, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, and_true]
      exact bound.2
    cases addressRun : StackSemExpressions.wordExp source (.op .add [.var base, .const offset]) with
    | none =>
      cases operator <;> simp [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
        addressRun] at run
    | some actualAddress =>
      have targetAddress := ExpressionSimulation.stateRelWordExp jump bounds pointer source target
        (.op .add [.var base, .const offset]) actualAddress ⟨relation, addressBound, addressRun⟩
      have registerEq := RelationLaws.stateRelGetVar jump bounds pointer register source target
        ⟨relation, bound.1⟩
      cases operator with
      | load16 => simp [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger] at run
      | store16 => simp [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger] at run
      | load =>
        simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
          Option.join_some, addressRun] at run
        cases read : StackSemStateOps.memLoad actualAddress source with
        | none => simp [read] at run
        | some value =>
          have targetRead := MemoryReads.stateRelMemLoadImp jump bounds pointer source target
            actualAddress value ⟨relation, read⟩
          simp only [read, Option.some.injEq] at run
          subst postSource
          refine ⟨StackSemStateOps.setVar register (value) target, ?_, ?_⟩
          · simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
              Option.join_some, targetAddress, targetRead]
          · exact StateUpdates.stateRelSetVar jump bounds pointer register (value) source target
              ⟨relation, bound.1⟩
      | load8 =>
        simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
          Option.join_some, addressRun] at run
        cases read : memLoadByteAuxExact source.memory source.mdomain source.be actualAddress with
        | none => simp [read] at run
        | some value =>
          have targetRead := MemoryLoads.memLoadByteAuxImp jump bounds pointer source target
            actualAddress value ⟨relation, read⟩
          simp only [read, Option.some.injEq] at run
          subst postSource
          refine ⟨StackSemStateOps.setVar register (.word (value.setWidth width)) target, ?_, ?_⟩
          · simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
              Option.join_some, targetAddress, targetRead]
          · exact StateUpdates.stateRelSetVar jump bounds pointer register (.word (value.setWidth width)) source target
              ⟨relation, bound.1⟩
      | load32 =>
        simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
          Option.join_some, addressRun] at run
        cases read : memLoad32Exact source.memory source.mdomain source.be actualAddress with
        | none => simp [read] at run
        | some value =>
          have targetRead := MemoryLoads.memLoad32Imp jump bounds pointer source target
            actualAddress value ⟨relation, read⟩
          simp only [read, Option.some.injEq] at run
          subst postSource
          refine ⟨StackSemStateOps.setVar register (.word (value.setWidth width)) target, ?_, ?_⟩
          · simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
              Option.join_some, targetAddress, targetRead]
          · exact StateUpdates.stateRelSetVar jump bounds pointer register (.word (value.setWidth width)) source target
              ⟨relation, bound.1⟩
      | store =>
        simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
          Option.join_some, addressRun] at run
        cases sourceValue : StackSemStateOps.getVar register source with
        | none => simp [sourceValue] at run
        | some value =>
          have targetValue : StackSemStateOps.getVar register target = some value :=
            registerEq.symm.trans sourceValue
          simp only [sourceValue] at run
          cases store : StackSemStateOps.memStore actualAddress value source with
          | none => simp [store] at run
          | some sourceResult =>
            simp only [store, Option.some.injEq] at run
            subst postSource
            cases inSource : source.mdomain actualAddress with
            | false => simp [StackSemStateOps.memStore, inSource] at store
            | true =>
              have targetDomain := (MemoryReads.stateRelRead jump bounds pointer source target
                actualAddress ⟨relation, inSource⟩).1
              have targetStore : StackSemStateOps.memStore actualAddress value target =
                  some {target with memory := fun key => if key = actualAddress then value else target.memory key} := by
                simp only [StackSemStateOps.memStore, targetDomain, ite_true]
              refine ⟨{target with memory := fun key => if key = actualAddress then value else target.memory key}, ?_, ?_⟩
              · simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
                  Option.join_some, targetAddress, targetValue, targetStore]
              · exact MemoryStores.stateRelMemStore jump bounds pointer source target sourceResult _
                  actualAddress value ⟨relation, store, targetStore⟩
      | store8 =>
        simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
          Option.join_some, addressRun] at run
        cases sourceValue : StackSemStateOps.getVar register source with
        | none => simp [sourceValue] at run
        | some value =>
          have targetValue : StackSemStateOps.getVar register target = some value :=
            registerEq.symm.trans sourceValue
          cases value with
          | loc block label => simp [sourceValue] at run
          | word word =>
            simp only [sourceValue] at run
            cases store : memStoreByteAuxExact source.memory source.mdomain source.be actualAddress (word.setWidth 8) with
            | none => simp [store] at run
            | some sourceMemory =>
              obtain ⟨targetMemory, targetStore, updatedRelation⟩ :=
                MemoryStores.stateRelMemStoreByteAux jump bounds pointer source target actualAddress
                  (word.setWidth 8) sourceMemory ⟨relation, store⟩
              simp only [store, Option.some.injEq] at run
              subst postSource
              refine ⟨{target with memory := targetMemory}, ?_, updatedRelation⟩
              simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
                Option.join_some, targetAddress, targetValue, targetStore]
      | store32 =>
        simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
          Option.join_some, addressRun] at run
        cases sourceValue : StackSemStateOps.getVar register source with
        | none => simp [sourceValue] at run
        | some value =>
          have targetValue : StackSemStateOps.getVar register target = some value :=
            registerEq.symm.trans sourceValue
          cases value with
          | loc block label => simp [sourceValue] at run
          | word word =>
            simp only [sourceValue] at run
            cases store : memStore32Exact source.memory source.mdomain source.be actualAddress (word.setWidth 32) with
            | none => simp [store] at run
            | some sourceMemory =>
              obtain ⟨targetMemory, targetStore, updatedRelation⟩ :=
                MemoryStores.stateRelMemStore32 jump bounds pointer source target actualAddress
                  (word.setWidth 32) sourceMemory ⟨relation, store⟩
              simp only [store, Option.some.injEq] at run
              subst postSource
              refine ⟨{target with memory := targetMemory}, ?_, updatedRelation⟩
              simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
                Option.join_some, targetAddress, targetValue, targetStore]

end Flapjack.Compiler.Backend.StackRemove.InstructionSimulation.Memory
