import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact

namespace Flapjack.PanGlobalsCompileExpLeaves
open Flapjack
open Flapjack.Pancake.PanLang

/-- Canonical state roundtrips, re-exported for this relation theorem. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Canonical context roundtrip, re-exported for this relation theorem. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

/-- Residual Const constructor case of the original theorem, with no additional premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectConstHOL {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width) (constant : BitVec width) (value : ValueHOL width) :
    letI : DecidablePred source.memaddrs := fun a => Classical.propDecidable (source.memaddrs a)
    letI : DecidablePred target.memaddrs := fun a => Classical.propDecidable (target.memaddrs a)
    panGlobalsStateRelHOLExact true context source target ∧
      source.evalHOLFinite (.const constant) = some value →
    target.evalHOLFinite (compileExpExactHOL context (.const constant)) = some value := by
  classical
  intro ⟨hrel, heval⟩
  simpa [compileExpExactHOL, PanSemStateFiniteExact.evalHOLFinite, evalHOLExact] using heval

/-- Residual Local constructor case of the original theorem, with no additional premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectLocalHOL {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width) (name : MlS) (value : ValueHOL width) :
    letI : DecidablePred source.memaddrs := fun a => Classical.propDecidable (source.memaddrs a)
    letI : DecidablePred target.memaddrs := fun a => Classical.propDecidable (target.memaddrs a)
    panGlobalsStateRelHOLExact true context source target ∧
      source.evalHOLFinite (.var .local name) = some value →
    target.evalHOLFinite (compileExpExactHOL context (.var .local name)) = some value := by
  classical
  intro ⟨hrel, heval⟩
  have hl := hrel.2.1 rfl
  simpa [compileExpExactHOL, PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, hl] using heval

/-- Residual BaseAddr constructor case of the original theorem, with no additional premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectBaseAddrHOL {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width)  (value : ValueHOL width) :
    letI : DecidablePred source.memaddrs := fun a => Classical.propDecidable (source.memaddrs a)
    letI : DecidablePred target.memaddrs := fun a => Classical.propDecidable (target.memaddrs a)
    panGlobalsStateRelHOLExact true context source target ∧
      source.evalHOLFinite (.baseAddr) = some value →
    target.evalHOLFinite (compileExpExactHOL context (.baseAddr)) = some value := by
  classical
  intro ⟨hrel, heval⟩
  have hb := hrel.2.2.1
  simpa [compileExpExactHOL, PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, hb] using heval

/-- Residual TopAddr constructor case of the original theorem, with no additional premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectTopAddrHOL {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width)  (value : ValueHOL width) :
    letI : DecidablePred source.memaddrs := fun a => Classical.propDecidable (source.memaddrs a)
    letI : DecidablePred target.memaddrs := fun a => Classical.propDecidable (target.memaddrs a)
    panGlobalsStateRelHOLExact true context source target ∧
      source.evalHOLFinite (.topAddr) = some value →
    target.evalHOLFinite (compileExpExactHOL context (.topAddr)) = some value := by
  classical
  intro ⟨hrel, heval⟩
  have ht := hrel.1
  simpa [compileExpExactHOL, PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, evalListHOLExact, wordOpHOL, valueIsWord, valueWord, wordOp, ht] using heval

/-- Residual BytesInWord constructor case of the original theorem, with no additional premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectBytesInWordHOL {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width)  (value : ValueHOL width) :
    letI : DecidablePred source.memaddrs := fun a => Classical.propDecidable (source.memaddrs a)
    letI : DecidablePred target.memaddrs := fun a => Classical.propDecidable (target.memaddrs a)
    panGlobalsStateRelHOLExact true context source target ∧
      source.evalHOLFinite (.bytesInWord) = some value →
    target.evalHOLFinite (compileExpExactHOL context (.bytesInWord)) = some value := by
  classical
  intro ⟨hrel, heval⟩
  simpa [compileExpExactHOL, PanSemStateFiniteExact.evalHOLFinite, evalHOLExact] using heval

end Flapjack.PanGlobalsCompileExpLeaves
