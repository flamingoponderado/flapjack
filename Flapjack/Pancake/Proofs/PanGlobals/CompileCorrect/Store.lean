import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Base
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpCorrect
import Flapjack.Pancake.Proofs.PanGlobals.MemoryUpdate

/-! The Store case at pan_globalsProofScript.sml:692-714. The source proof
uses expression correctness and induction over the flattened value's memory
writes; no recursive program induction hypothesis is needed. -/
namespace Flapjack.PanGlobalsCompileCorrectStore
open Flapjack.Pancake.PanLang
open PanSemStateFiniteExact

/-- Canonical state roundtrips for the relation representation. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Canonical context roundtrip for the relation representation. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

/-- Local infrastructure for HOL's internal list induction in the Store proof.
No separate HOL declaration: each successful source-domain update supplies the
target update and preserves the original state relation. -/
private theorem memStoresSimulation {width : Nat} {σ : Type} [NeZero width]
    (context : PanGlobalsContextExact width) (words : List (HolWordLab width)) :
    ∀ (address : BitVec width) (source target : PanSemStateFiniteExact width σ)
      (memory : BitVec width → HolWordLab width),
      panGlobalsStateRelHOLExact true context source target →
      @panMemStoresHOL width _ address words source.memaddrs
        (fun a => Classical.propDecidable (source.memaddrs a)) source.memory = some memory →
      ∃ targetMemory,
        @panMemStoresHOL width _ address words target.memaddrs
          (fun a => Classical.propDecidable (target.memaddrs a)) target.memory = some targetMemory ∧
        panGlobalsStateRelHOLExact true context
          {source with memory := memory} {target with memory := targetMemory} := by
  classical
  induction words with
  | nil =>
      intro address source target memory hrel hm
      simp only [panMemStoresHOL, Option.some.injEq] at hm
      subst memory
      refine ⟨target.memory, rfl, ?_⟩
      simpa only using hrel
  | cons word words ih =>
      intro address source target memory hrel hm
      simp only [panMemStoresHOL, panMemStoreHOL] at hm
      by_cases hd : source.memaddrs address
      · simp only [if_pos hd] at hm
        have ht : target.memaddrs address := hrel.2.2.2.2.2.2.2.2.2.2.1 address hd
        have hu := PanGlobalsMemoryUpdate.stateRelMemoryUpdateHOL context source target
          address word ⟨hrel, hd⟩
        obtain ⟨targetMemory, htm, hrelm⟩ := ih (address + panBytesInWord width)
          {source with memory := fun x => if x = address then word else source.memory x}
          {target with memory := fun x => if x = address then word else target.memory x}
          memory hu hm
        refine ⟨targetMemory, ?_, ?_⟩
        · simpa only [panMemStoresHOL, panMemStoreHOL, if_pos ht] using htm
        · exact hrelm
      · simp [if_neg hd] at hm

/-- Genuine Store case of HOL compile_correct, with its original source
evaluation/nonerror premises and existential target run. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Store {width : Nat} {σ : Type} [NeZero width]
    (destination value : ExpHOL width) (s : PanSemStateFiniteExact width σ) :
    ∀ (res : Option (PanSemResultExact width)) (ctxt : PanGlobalsContextExact width)
      (t s' : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true ctxt s t ∧
        evaluateHOLFiniteState s (.store destination value) = (res, s') ∧
        res ≠ some .error →
      ∃ t', evaluateHOLFiniteState t (compileProgExactHOL ctxt (.store destination value)) =
          (res, t') ∧ panGlobalsStateRelHOLExact (goodResHOL res) ctxt s' t' := by
  classical
  intro res ctxt t s' ⟨hrel, hev, hne⟩
  rw [evaluateHOLFiniteState_store] at hev
  repeat' split at hev
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
  all_goals try exact False.elim (hne rfl)
  rename_i _ address hd _ storedValue hs _ memory hm
  have hdt := PanGlobalsCompileExpCorrect.compileExpCorrectHOL s destination
    (.val (.word address)) ctxt t ⟨hrel, hd⟩
  have hst := PanGlobalsCompileExpCorrect.compileExpCorrectHOL s value
    storedValue ctxt t ⟨hrel, hs⟩
  change evalHOLExact t.toExact (compileExpExactHOL ctxt destination) =
    some (.val (.word address)) at hdt
  change evalHOLExact t.toExact (compileExpExactHOL ctxt value) = some storedValue at hst
  obtain ⟨targetMemory, htm, hrelm⟩ := memStoresSimulation ctxt (flattenHOL storedValue)
    address s t memory hrel hm
  refine ⟨{t with memory := targetMemory}, ?_, hrelm⟩
  simp only [compileProgExactHOL, evaluateHOLFiniteState_store, hdt, hst, htm]

end Flapjack.PanGlobalsCompileCorrectStore
