import Flapjack.Pancake.Proofs.PanGlobals.CompileExpCorrect

namespace Flapjack.PanGlobalsOptMmapEvalCorrect
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

/-- Full HOL919-932 list theorem. The previously proved full expression
theorem supplies each element; list recursion proves the original successful
OPT_MMAP result with no pointwise IH or target-evaluation premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "OPT_MMAP_eval_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem optMmapEvalCorrectHOL {width : Nat} {σ : Type} [NeZero width]
    (context : PanGlobalsContextExact width) (source target : PanSemStateFiniteExact width σ)
    (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (h : panGlobalsStateRelHOLExact true context source target ∧
      PanSemStateFiniteExact.evalListHOLFinite source (h := fun a => Classical.propDecidable (source.memaddrs a)) arguments = some values) :
    PanSemStateFiniteExact.evalListHOLFinite target (h := fun a => Classical.propDecidable (target.memaddrs a))
      (arguments.map (compileExpExactHOL context)) = some values := by
  classical
  obtain ⟨hrel,heval⟩ := h
  change evalListHOLExact source.toExact arguments = some values at heval
  change evalListHOLExact target.toExact (arguments.map (compileExpExactHOL context)) = some values
  induction arguments generalizing values with
  | nil => simpa only [evalListHOLExact,List.map_nil] using heval
  | cons expression rest ih =>
    simp only [evalListHOLExact] at heval
    cases hh : evalHOLExact source.toExact expression with
    | none => simp [hh] at heval
    | some v =>
      cases ht : evalListHOLExact source.toExact rest with
      | none => simp [hh,ht] at heval
      | some vs =>
        have hv : v :: vs = values := by simpa [hh,ht] using heval
        subst values
        have hhead := PanGlobalsCompileExpCorrect.compileExpCorrectHOL source expression v context target ⟨hrel,hh⟩
        change evalHOLExact target.toExact (compileExpExactHOL context expression) = some v at hhead
        have htail := ih vs ht
        simp only [List.map_cons,evalListHOLExact,hhead,htail]

end Flapjack.PanGlobalsOptMmapEvalCorrect
