import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Base
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpCorrect
import Flapjack.Pancake.Proofs.PanGlobals.MemoryUpdate
import Flapjack.Pancake.Semantics.PanSem.MemStore32Alt

/-! The Store32 case at pan_globalsProofScript.sml:714-724. The source proof
uses expression correctness and the successful aligned memory update; no recursive program induction hypothesis is needed. -/
namespace Flapjack.PanGlobalsCompileCorrectStore32
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

/-- Flapjack-only helper constructing the memory update inside HOL's Store32 case. -/
private theorem memStore32Simulation {width : Nat} {σ : Type} [NeZero width]
    (context : PanGlobalsContextExact width) (address : BitVec width) (value : BitVec 32)
    (source target : PanSemStateFiniteExact width σ)
    (memory : BitVec width → HolWordLab width)
    (hrel : panGlobalsStateRelHOLExact true context source target)
    (hstore : @panMemStore32HOL width _ source.memory source.memaddrs
      (fun a => Classical.propDecidable (source.memaddrs a)) source.be address value = some memory) :
    ∃ targetMemory,
      @panMemStore32HOL width _ target.memory target.memaddrs
        (fun a => Classical.propDecidable (target.memaddrs a)) target.be address value = some targetMemory ∧
      panGlobalsStateRelHOLExact true context
        {source with memory := memory} {target with memory := targetMemory} := by
  classical
  have hbe := hrel.2.2.2.1
  have hsub := hrel.2.2.2.2.2.2.2.2.2.2.1
  have hmem := hrel.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [panMemStore32HOL_eq_alt] at hstore
  by_cases ha : address.toNat % 4 = 0
  · cases hm : source.memory (panByteAlignHOL address) with
    | word cell =>
      by_cases hd : source.memaddrs (panByteAlignHOL address)
      · have htargetCell := hmem _ hd
        simp only [if_pos ha, hm, if_pos hd, Option.some.injEq] at hstore
        subst memory
        refine ⟨(fun a => if a = panByteAlignHOL address then
          .word (store32Alt address source.be value cell) else target.memory a), ?_, ?_⟩
        · rw [panMemStore32HOL_eq_alt]
          simp [ha, ← htargetCell, hm, hsub _ hd, ← hbe]
        · exact PanGlobalsMemoryUpdate.stateRelMemoryUpdateHOL context source target
            (panByteAlignHOL address) (.word (store32Alt address source.be value cell)) ⟨hrel, hd⟩
      · simp [ha, hd] at hstore
  · simp [ha] at hstore

/-- Genuine Store32 case of HOL compile_correct, with its original source
evaluation/nonerror premises and existential target run. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Store32 {width : Nat} {σ : Type} [NeZero width]
    (destination value : ExpHOL width) (s : PanSemStateFiniteExact width σ) :
    ∀ (res : Option (PanSemResultExact width)) (ctxt : PanGlobalsContextExact width)
      (t s' : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true ctxt s t ∧
        evaluateHOLFiniteState s (.store32 destination value) = (res, s') ∧
        res ≠ some .error →
      ∃ t', evaluateHOLFiniteState t (compileProgExactHOL ctxt (.store32 destination value)) =
          (res, t') ∧ panGlobalsStateRelHOLExact (goodResHOL res) ctxt s' t' := by
  classical
  intro res ctxt t s' ⟨hrel, hev, hne⟩
  rw [evaluateHOLFiniteState_store32] at hev
  repeat' split at hev
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
  all_goals try exact False.elim (hne rfl)
  rename_i _ address hd _ storedValue hs _ memory hm
  have hdt := PanGlobalsCompileExpCorrect.compileExpCorrectHOL s destination
    (.val (.word address)) ctxt t ⟨hrel, hd⟩
  have hst := PanGlobalsCompileExpCorrect.compileExpCorrectHOL s value
    (.val (.word storedValue)) ctxt t ⟨hrel, hs⟩
  change evalHOLExact t.toExact (compileExpExactHOL ctxt destination) =
    some (.val (.word address)) at hdt
  change evalHOLExact t.toExact (compileExpExactHOL ctxt value) = some (.val (.word storedValue)) at hst
  obtain ⟨targetMemory, htm, hrelm⟩ := memStore32Simulation ctxt address (BitVec.ofNat 32 storedValue.toNat)
    s t memory hrel hm
  refine ⟨{t with memory := targetMemory}, ?_, hrelm⟩
  simp only [compileProgExactHOL, evaluateHOLFiniteState_store32, hdt, hst, htm]

end Flapjack.PanGlobalsCompileCorrectStore32
