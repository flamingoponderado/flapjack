import Flapjack.Compiler.Backend.ClosConstant.Proofs.Build
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.FreshTargetRefs

/-! Correspondence of source and BVL constant-part builders. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.ClosConstant.Proofs
open Flapjack.Compiler.Backend.BackendCommon
open Flapjack.SemanticPrimitivesHOL

/-- Building one part preserves the state relation and the reference frame.
String parts allocate a fresh frozen byte array. -/
theorem constantPart_related {C F : Type} (part : ClosLang.ConstPart)
    (sourceMemory : Nat → ClosSem.Value) (targetMemory : Nat → BvlSem.Value)
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (states : stateRel f s t)
    (memoryRel : ∀ index, vRel s.maxApp f t.refs t.code (sourceMemory index) (targetMemory index)) :
    ∃ value refs,
      BvlSem.doPart targetMemory (updateTag part) t.refs = (value, refs) ∧
      vRel s.maxApp f refs t.code (buildPart sourceMemory part) value ∧
      stateRel f s { t with refs := refs } ∧ unmappedRefsSubmap t.refs refs f f := by
  have frame : unmappedRefsSubmap t.refs t.refs f f := by
    intro key value found fresh
    exact ⟨found, fresh⟩
  cases part with
  | int n => exact ⟨.number n, t.refs, rfl, .number n, by simpa using states, frame⟩
  | w64 w => exact ⟨.word64 w, t.refs, rfl, .word64 w, by simpa using states, frame⟩
  | con tag indices =>
    have fields : List.Forall₂ (vRel s.maxApp f t.refs t.code)
        (indices.map sourceMemory) (indices.map targetMemory) := by
      induction indices with
      | nil => exact .nil
      | cons index rest ih => exact .cons (memoryRel index) ih
    exact ⟨.block (closTagShift tag) (indices.map targetMemory), t.refs, rfl,
      .block fields, by simpa using states, frame⟩
  | str text =>
    let ptr := BvlSem.leastUnusedRef t.refs
    let refs := t.refs.updateEq (ptr, .byteArray true text.explode)
    have fresh := stateRel_targetRefs_allocate s t f (.byteArray true text.explode) states
    change stateRel f s { t with refs := refs } ∧ unmappedRefsSubmap t.refs refs f f ∧
      (¬ ∃ sourcePtr, f.lookup sourcePtr = some ptr) ∧
      refs.lookup ptr = some (.byteArray true text.explode) at fresh
    exact ⟨.refPtr true ptr, refs, rfl, .byteVector fresh.2.2.2 fresh.2.2.1, fresh.1, fresh.2.1⟩

/-- Building any part sequence preserves the source/target value and state
relations. The relocation map stays fixed; only fresh target references may
be added. This candidate is untagged pending HOL carrier review. -/
theorem constantBuild_related {C F : Type} (parts : List ClosLang.ConstPart)
    (sourceMemory : Nat → ClosSem.Value) (targetMemory : Nat → BvlSem.Value) (index : Nat)
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (states : stateRel f s t)
    (memoryRel : ∀ key, vRel s.maxApp f t.refs t.code (sourceMemory key) (targetMemory key)) :
    ∃ value refs,
      BvlSem.doBuild targetMemory index (parts.map updateTag) t.refs = (value, refs) ∧
      vRel s.maxApp f refs t.code (build sourceMemory index parts) value ∧
      stateRel f s { t with refs := refs } ∧ unmappedRefsSubmap t.refs refs f f := by
  induction parts generalizing sourceMemory targetMemory index t with
  | nil =>
    refine ⟨targetMemory (index - 1), t.refs, rfl, memoryRel _, ?_, ?_⟩
    · simpa using states
    · intro key value found fresh
      exact ⟨found, fresh⟩
  | cons part rest ih =>
    obtain ⟨value, refs, partRun, valueRel, nextStates, frame⟩ :=
      constantPart_related part sourceMemory targetMemory s t f states memoryRel
    have submap : relocationSubmap f f := by intro key val found; exact found
    let sourceNext := fun key => if key = index then buildPart sourceMemory part else sourceMemory key
    let targetNext := fun key => if key = index then value else targetMemory key
    have nextMemoryRel : ∀ key, vRel s.maxApp f refs t.code (sourceNext key) (targetNext key) := by
      intro key
      by_cases equal : key = index
      · simp [sourceNext, targetNext, equal, valueRel]
      · simp only [sourceNext, targetNext, if_neg equal]
        exact vRel_grow_refs (memoryRel key) submap frame
    obtain ⟨result, finalRefs, restRun, resultRel, finalStates, finalFrame⟩ :=
      ih sourceNext targetNext (index + 1) { t with refs := refs } nextStates nextMemoryRel
    refine ⟨result, finalRefs, ?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, BvlSem.doBuild, partRun]
      exact restRun
    · simpa [build, sourceNext] using resultRel
    · simpa using finalStates
    · exact unmappedRefsSubmap_trans frame finalFrame

/-- The initialized source and target constant builders return related
values and preserve the candidate state relation. -/
theorem constantBuildConst_related {C F : Type} (parts : List ClosLang.ConstPart)
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (states : stateRel f s t) :
    ∃ value refs,
      BvlSem.doBuildConst (parts.map updateTag) t.refs = (value, refs) ∧
      vRel s.maxApp f refs t.code (buildConst parts) value ∧
      stateRel f s { t with refs := refs } ∧ unmappedRefsSubmap t.refs refs f f := by
  have memoryRel : ∀ _ : Nat, vRel s.maxApp f t.refs t.code (.number 0) (.number 0) :=
    fun _ => .number 0
  exact constantBuild_related parts (fun _ => .number 0) (fun _ => .number 0) 0 s t f states memoryRel

end Flapjack.Compiler.Backend.ClosToBvl
