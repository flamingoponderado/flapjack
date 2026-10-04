import Flapjack.Compiler.Backend.StackRemove.Proofs.StoreHeapWrites
import Flapjack.Compiler.Backend.StackRemove.Proofs.WordStoreLaws
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

/-- Flapjack proof factoring of the original Set CurrHeap case. Its only
relation premise is the full original state relation, with no added bound,
frame, successful-evaluation or post-state relation assumption. -/
theorem stateRelSetCurrHeap {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (value : WordLocW width) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target) :
    stateRelHOL jump bounds pointer (StackSemStateOps.setStore .currHeap value source)
      (StackSemStateOps.setVar (pointer + 2) value target) := by
  simp only [stateRelHOL] at relation
  rcases relation with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩
  have lookupPreserved : ∀ query, query < pointer →
      (target.regs.updateEq (pointer + 2, value)).lookup query = source.regs.lookup query := by
    intro query below
    have different : query ≠ pointer + 2 := by omega
    simpa only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different, ite_false] using h18 query below
  have pointerNe : pointer ≠ pointer + 2 := by omega
  have baseNe : pointer + 1 ≠ pointer + 2 := by omega
  have bitmapNe : (WordStore.bitmapBase : WordStoreHOL) ≠ WordStore.currHeap := by
    intro equal
    cases equal
  simp only [stateRelHOL, StackSemStateOps.setStore, StackSemStateOps.setVar,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, pointerNe, baseNe, bitmapNe, ite_false,
    ite_true]
  refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    lookupPreserved, h19, h20, True.intro, h22, ?_, h24, ?_⟩
  · exact h23
  · simpa only [WordStoreLaws.wordStoreCurrHeap] using h25

/-- Flapjack proof factoring of the original non-CurrHeap Set branch.
The name exclusions and base lookup are discharged by the original bound and
full state relation in the genuine constructor theorem. -/
theorem stateRelSetStore {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (name : StoreName) (value : WordLocW width) (base : BitVec width)
    (source target : StackSemStateFiniteExact width C F)
    (notCurrHeap : name ≠ .currHeap) (notBitmapBase : name ≠ .bitmapBase)
    (baseLookup : target.regs.lookup (pointer + 1) = some (.word base))
    (relation : stateRelHOL jump bounds pointer source target) :
    stateRelHOL jump bounds pointer
      (StackSemStateOps.setStore (StackSemRegisterTransfers.storeOfSyntax name) value source)
      {target with memory := fun key => if key = base + storeOffset name then value else target.memory key} := by
  have currNe : WordStore.currHeap ≠ StackSemRegisterTransfers.storeOfSyntax name := by
    intro equal
    have names := congrArg StackSemRegisterTransfers.storeToSyntax equal
    simp only [StackSemRegisterTransfers.storeToSyntax_storeOfSyntax] at names
    exact notCurrHeap names.symm
  have bitmapNe : WordStore.bitmapBase ≠ StackSemRegisterTransfers.storeOfSyntax name := by
    intro equal
    have names := congrArg StackSemRegisterTransfers.storeToSyntax equal
    simp only [StackSemRegisterTransfers.storeToSyntax_storeOfSyntax] at names
    exact notBitmapBase names.symm
  simp only [stateRelHOL] at relation
  rcases relation with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩
  simp only [stateRelHOL, StackSemStateOps.setStore,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, currNe, bitmapNe, ite_false]
  refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, ?_⟩
  simp only [baseLookup] at h25 ⊢
  refine ⟨h25.1, h25.2.1, h25.2.2.1, h25.2.2.2.1, ?_⟩
  have written := StoreHeapWrites.storeWriteLemma name source target.memory
    (fun address => target.mdomain address = true) value base
    ⟨StoreNames.nameCases name notCurrHeap, by
      simpa only [List.length_append, Nat.add_comm] using h25.2.2.2.2⟩
  simpa only [List.length_append, Nat.add_comm] using written


/-- Full genuine Get case: original non-error excludes absent source store
lookup, and the complete state relation derives reserved-register or full-heap
load execution before establishing the full post-state relation. The total
evaluator retains inherited reals_as_rational_cuts. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
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

/-- Full genuine Set case: the original bound excludes BitmapBase. CurrHeap
updates the reserved target register; every other name uses the full native
store heap write law. Target execution and all post-state relation conjuncts
are derived. The total evaluator retains inherited reals_as_rational_cuts. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectSet {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (register : Nat) (name : StoreName)
    (hypothesis : StackSemEvaluate.evaluate (.set name register, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.set name register : HolProg width) pointer) :
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.set name register),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have useStore : source.useStore = true := relation.2.1
  rw [StackSemEvaluate.evaluate_set] at sourceRun
  simp only [useStore, not_true_eq_false, ite_false] at sourceRun
  cases lookup : StackSemStateOps.getVar register source with
  | none =>
    rw [lookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some value =>
    rw [lookup] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    have getVarEq := RelationLaws.stateRelGetVar jump bounds pointer register source target
      ⟨relation, bound.1⟩
    have targetLookup : target.regs.lookup register = some value := by
      simpa only [StackSemStateOps.getVar] using getVarEq.symm.trans lookup
    by_cases current : name = .currHeap
    · subst name
      refine ⟨0, StackSemStateOps.setVar (pointer + 2) value target, ?_, ?_⟩
      · simp [comp, moveInst, moveHOL, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
          StackSemIntegerInstructions.instInteger, targetLookup]
      · exact stateRelSetCurrHeap jump bounds pointer value source target relation
    · have heaps := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      dsimp only at heaps
      cases baseLookup : target.regs.lookup (pointer + 1) with
      | none => simp only [baseLookup] at heaps; exact heaps.2.elim
      | some baseValue =>
        cases baseValue with
        | loc block offset => simp only [baseLookup] at heaps; exact heaps.2.elim
        | word base =>
          simp only [baseLookup] at heaps
          have domain := StoreHeapReads.memLoadLemma2 name source target base
            ⟨StoreNames.nameCases name current, by
              simpa only [List.length_append, Nat.add_comm] using heaps.2.2.2.2⟩
          have expression : StackSemExpressions.wordExp target
              (.op .add [.var (pointer + 1), .const (storeOffset name)]) =
              some (base + storeOffset name) := by
            simp [StackSemExpressions.wordExp, baseLookup, wordOpHOL, wordOp]
          refine ⟨0, {target with memory := fun key =>
            if key = base + storeOffset name then value else target.memory key}, ?_, ?_⟩
          · simp [comp, current, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
              StackSemIntegerInstructions.instInteger, expression, StackSemStateOps.getVar,
              targetLookup, StackSemStateOps.memStore, domain]
          · exact stateRelSetStore jump bounds pointer name value base source target
              current bound.2 baseLookup relation

end Flapjack.Compiler.Backend.StackRemove.CompCorrect.StoreTransfers
