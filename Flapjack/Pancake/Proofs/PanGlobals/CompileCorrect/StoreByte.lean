import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Base
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpCorrect
import Flapjack.Pancake.Proofs.PanGlobals.MemoryUpdate
import Flapjack.Pancake.Proofs.PanGlobals.ByteStore

/-! The StoreByte case at pan_globalsProofScript.sml:726-736. The source proof
uses expression correctness and the successful aligned memory update; no recursive program induction hypothesis is needed. -/
namespace Flapjack.PanGlobalsCompileCorrectStoreByte
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

/-- Genuine StoreByte case of HOL compile_correct, with its original source
evaluation/nonerror premises and existential target run. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_StoreByte {width : Nat} {σ : Type} [NeZero width]
    (destination value : ExpHOL width) (s : PanSemStateFiniteExact width σ) :
    ∀ (res : Option (PanSemResultExact width)) (ctxt : PanGlobalsContextExact width)
      (t s' : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true ctxt s t ∧
        evaluateHOLFiniteState s (.storeByte destination value) = (res, s') ∧
        res ≠ some .error →
      ∃ t', evaluateHOLFiniteState t (compileProgExactHOL ctxt (.storeByte destination value)) =
          (res, t') ∧ panGlobalsStateRelHOLExact (goodResHOL res) ctxt s' t' := by
  classical
  intro res ctxt t s' ⟨hrel, hev, hne⟩
  rw [evaluateHOLFiniteState_storeByte] at hev
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
  obtain ⟨targetMemory, htm, hrelm⟩ := PanGlobalsByteStore.stateRelMemStoreByte true ctxt s t
    address (BitVec.ofNat 8 storedValue.toNat) memory ⟨hrel, hm⟩
  refine ⟨{t with memory := targetMemory}, ?_, hrelm⟩
  simp only [compileProgExactHOL, evaluateHOLFiniteState_storeByte, hdt, hst, htm]

end Flapjack.PanGlobalsCompileCorrectStoreByte
