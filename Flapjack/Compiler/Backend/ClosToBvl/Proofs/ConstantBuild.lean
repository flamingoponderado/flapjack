module

public import Flapjack.FiniteMap.BroadCodec
public import Flapjack.Compiler.Backend.ClosConstant.Proofs.Reconstruct
public import Flapjack.Compiler.Backend.ClosConstant.Proofs.HashParts
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.FreshTargetRefs

@[expose] public section

/-! Correspondence of source and BVL constant-part builders. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.ClosConstant.Proofs
open Flapjack.Compiler.Backend.BackendCommon
open Flapjack.SemanticPrimitivesHOL

namespace ConstantBuildCarrier

/-- The closure state's finite maps have canonical finite support. -/
theorem holFmapAsFiniteSupportRelationWitness_ClosSem.State {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- The BVL state's reference map has canonical finite support. -/
theorem holFmapAsFiniteSupportRelationWitness_BvlSem.State {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness

/-- The existential relocation map roundtrips through the canonical codec. -/
theorem holFmapAsFiniteSupportExistentialWitness_doBuildConst_thm_f2out
    (f2out : HolFiniteMapExact Nat Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f2out)).lookup = f2out.lookup ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f2out)).finiteSupport = f2out.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f2out) = f2out := by
  cases f2out
  exact ⟨rfl, rfl, rfl⟩

end ConstantBuildCarrier

/-- Replacing a BVL state's reference map with itself leaves the state unchanged. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "refs_lemma"
  (fmap_as_finite_support_relation := [BvlSem.State.refs])]
theorem refs_lemma {C F : Type} (t : BvlSem.State C F) : { t with refs := t.refs } = t := by
  cases t
  rfl

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
  | int n => exact ⟨.number n, t.refs, rfl, .number n, (refs_lemma t).symm ▸ states, frame⟩
  | w64 w => exact ⟨.word64 w, t.refs, rfl, .word64 w, (refs_lemma t).symm ▸ states, frame⟩
  | con tag indices =>
    have fields : List.Forall₂ (vRel s.maxApp f t.refs t.code)
        (indices.map sourceMemory) (indices.map targetMemory) := by
      induction indices with
      | nil => exact .nil
      | cons index rest ih => exact .cons (memoryRel index) ih
    exact ⟨.block (closTagShift tag) (indices.map targetMemory), t.refs, rfl,
      .block fields, (refs_lemma t).symm ▸ states, frame⟩
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
    have submap : f.submap f := by intro key val found; exact found
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


/-- Building a constant preserves the earlier reference frame and relations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "do_build_const_thm"
  (fmap_as_finite_support_relation := [ClosSem.State.refs, ClosSem.State.code, BvlSem.State.refs, f1, f2, refs])
  (fmap_as_finite_support_existentials := [f2out])]
theorem doBuildConst_thm {C F D G : Type} (parts : List ClosLang.ConstPart)
    (t1 : BvlSem.State D G) (t2 : BvlSem.State C F) (s : ClosSem.State C F)
    (f1 : HolFiniteMapExact Nat Nat) (f2 : HolFiniteMapExact Nat Nat) (value : BvlSem.Value)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    (premises : BvlSem.doBuildConst (parts.map updateTag) t2.refs = (value, refs) ∧
      stateRel f2 s t2 ∧ f1.submap f2 ∧ unmappedRefsSubmap t1.refs t2.refs f1 f2) :
    ∃ (f2out : HolFiniteMapExact Nat Nat),
      vRel s.maxApp f2out refs t2.code (buildConst parts) value ∧
      stateRel f2out s { t2 with refs := refs } ∧ f1.submap f2out ∧
      unmappedRefsSubmap t1.refs refs f1 f2out := by
  obtain ⟨run, states, submap, previousFrame⟩ := premises
  obtain ⟨builtValue, builtRefs, builtRun, valueRel, finalStates, frame⟩ :=
    constantBuildConst_related parts s t2 f2 states
  have resultEq : (builtValue, builtRefs) = (value, refs) := builtRun.symm.trans run
  cases resultEq
  exact ⟨f2, valueRel, finalStates, submap, unmappedRefsSubmap_trans previousFrame frame⟩

/-- For constants emitted as a build operation, the executed part builder
produces a value related to the original constant. The state and value
relations are the current candidates pending HOL carrier review. -/
theorem compileConst_build_related {C F : Type} (constant : ClosLang.Const)
    (prereqs : (∀ n, constant ≠ .constInt n) ∧ (∀ tag, constant ≠ .constCons tag []))
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (states : stateRel f s t) :
    ∃ value refs,
      ClosToBvl.compileConst constant = .blockOp (.build ((toParts constant).map updateTag)) ∧
      BvlSem.doBuildConst ((toParts constant).map updateTag) t.refs = (value, refs) ∧
      vRel s.maxApp f refs t.code (ClosSem.makeConst constant) value ∧
      stateRel f s { t with refs := refs } ∧ unmappedRefsSubmap t.refs refs f f := by
  obtain ⟨value, refs, run, relation, finalStates, frame⟩ :=
    constantBuildConst_related (toParts constant) s t f states
  have sourceValue : buildConst (toParts constant) = ClosSem.makeConst constant := by
    rw [← makeConst_buildConstSyntax, buildConst_toParts]
  exact ⟨value, refs, compileConst_thm constant prereqs, run, sourceValue ▸ relation, finalStates, frame⟩

end Flapjack.Compiler.Backend.ClosToBvl
