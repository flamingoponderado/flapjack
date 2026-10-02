import Flapjack.Compiler.Backend.StackRemove.Proofs.StoreHeapWrites
import Flapjack.Compiler.Backend.StackRemove.Proofs.StoreNames
import Flapjack.Compiler.Backend.StackRemove.Proofs.InstructionSimulation
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Atoms

namespace Flapjack.Compiler.Backend.StackRemove.CompCorrect.StoreTransfers
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

/-- Canonical imported-state codec witness, Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full genuine Get case: original non-error excludes absent source store
lookup, and the complete state relation derives reserved-register or full-heap
load execution before establishing the full post-state relation. The total
evaluator retains inherited reals_as_rational_cuts. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectGet {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (register : Nat) (name : StoreName)
    (hypothesis : StackSemEvaluate.evaluate (.get register name, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.get register name : HolProg width) pointer) :
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.get register name),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have useStore : source.useStore = true := relation.2.1
  rw [StackSemEvaluate.evaluate_get] at sourceRun
  simp only [useStore, not_true_eq_false, ite_false] at sourceRun
  cases lookup : source.store.lookup (StackSemRegisterTransfers.storeOfSyntax name) with
  | none =>
    rw [lookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some value =>
    rw [lookup] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨0, StackSemStateOps.setVar register value target, ?_, ?_⟩
    · by_cases current : name = .currHeap
      · subst name
        have heapLookup := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        simp only [StackSemRegisterTransfers.storeOfSyntax] at lookup
        rw [lookup] at heapLookup
        simp [comp, moveInst, moveHOL, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
          StackSemIntegerInstructions.instInteger, heapLookup]
      · have heaps := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        dsimp only at heaps
        cases baseLookup : target.regs.lookup (pointer + 1) with
        | none => simp only [baseLookup] at heaps; exact heaps.2.elim
        | some baseValue =>
          cases baseValue with
          | loc block offset => simp only [baseLookup] at heaps; exact heaps.2.elim
          | word base =>
            simp only [baseLookup] at heaps
            have load := StoreHeapReads.memLoadLemma name source target value base
              ⟨StoreNames.nameCases name current, lookup, by
                simpa only [List.length_append, Nat.add_comm] using heaps.2.2.2.2⟩
            have expression : StackSemExpressions.wordExp target
                (.op .add [.var (pointer + 1), .const (storeOffset name)]) =
                some (base + storeOffset name) := by
              simp [StackSemExpressions.wordExp, baseLookup, wordOpHOL, wordOp]
            simp [comp, current, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
              StackSemIntegerInstructions.instInteger, expression, load]
    · exact StateUpdates.stateRelSetVar jump bounds pointer register value source target
        ⟨relation, bound⟩

end Flapjack.Compiler.Backend.StackRemove.CompCorrect.StoreTransfers
