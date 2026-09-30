import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Base
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpCorrect
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationLocals

namespace Flapjack.PanGlobalsCompileCorrectReturn
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

/-- Genuine Return case of compile_correct (source860-864).
Expression correctness supplies the target value; the original state relation
supplies equal empty struct contexts and the relation after clearing locals.
The target run and post-state are derived, with no additional hypothesis. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Return {width : Nat} {σ : Type} [NeZero width]
    (expression : ExpHOL width) (s : PanSemStateFiniteExact width σ) :
    ∀ (res : Option (PanSemResultExact width)) (ctxt : PanGlobalsContextExact width)
      (t s' : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true ctxt s t ∧
        evaluateHOLFiniteState s (.return expression) = (res, s') ∧ res ≠ some .error →
      ∃ t', evaluateHOLFiniteState t (compileProgExactHOL ctxt (.return expression)) =
          (res, t') ∧ panGlobalsStateRelHOLExact (goodResHOL res) ctxt s' t' := by
  classical
  intro res ctxt t s' ⟨hrel, hev, hne⟩
  rw [evaluateHOLFiniteState_return] at hev
  cases he : @evalHOLExact width σ _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) expression with
  | none =>
    simp only [he] at hev
    exact False.elim (hne (Prod.mk.inj hev).1.symm)
  | some value =>
    simp only [he] at hev
    by_cases hsize : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact value) ≤ 32
    · simp only [if_pos hsize] at hev
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
      have het := PanGlobalsCompileExpCorrect.compileExpCorrectHOL s expression value ctxt t ⟨hrel, he⟩
      change @evalHOLExact width σ _ t.toExact
        (fun a => Classical.propDecidable (t.memaddrs a)) (compileExpExactHOL ctxt expression) = some value at het
      obtain ⟨hss, hts⟩ := panGlobalsStateRelStructsHOLExact true ctxt s t hrel
      have hsizeT : sizeOfShapeWithContextHOL t.structs (shapeOfHOLExact value) ≤ 32 := by
        simpa only [hss, hts] using hsize
      refine ⟨t.emptyLocalsHOLFinite, ?_, ?_⟩
      · simp only [compileProgExactHOL, evaluateHOLFiniteState_return, het, if_pos hsizeT]
      · exact (PanGlobalsStateRelationLocals.stateRelEmptyLocalsHOL ctxt s t _).1 hrel
    · simp only [if_neg hsize] at hev
      exact False.elim (hne (Prod.mk.inj hev).1.symm)

end Flapjack.PanGlobalsCompileCorrectReturn
