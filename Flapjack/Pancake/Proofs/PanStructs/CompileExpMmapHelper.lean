import Flapjack.Pancake.Proofs.PanStructs.CompileExpNStruct
namespace Flapjack.Pancake.Proofs.PanStructs.CompileExpMmapHelper
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.Proofs.PanStructs.ConvertState
open Flapjack.Pancake.Proofs.PanStructs.ShapeMap
open Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact

/-- Canonical imported state-carrier roundtrip for this representation qualifier.
Flapjack infrastructure, not an independent HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Full faithful original list-evaluation helper. Both original hypotheses
and the complete mapped converted-list conclusion are retained. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_exp_correct_mmap_helper"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectMmapHelper {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (context : ContextExact)
    (expressions : List (ExpHOL width)) (values : List (ValueHOL width))
    (h : @PanSemStateFiniteExact.evalListHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a)) expressions = some values ∧
      (∀ expression ∈ expressions, ∀ value : ValueHOL width,
        @PanSemStateFiniteExact.evalHOLFinite width σ _ source
          (fun a => Classical.propDecidable (source.memaddrs a)) expression = some value →
        @PanSemStateFiniteExact.evalHOLFinite width σ _ (convertStateExact context source)
          (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
          (compileExpExact context expression) = some (convertV value))) :
    @PanSemStateFiniteExact.evalListHOLFinite width σ _ (convertStateExact context source)
      (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
      (compileExpsExact context expressions) = some (values.map convertV) := by
  classical
  obtain ⟨heval, hpoint⟩ := h
  change evalListHOLExact source.toExact expressions = some values at heval
  change evalListHOLExact (convertStateExact context source).toExact
    (compileExpsExact context expressions) = some (values.map convertV)
  induction expressions generalizing values with
  | nil =>
    simp only [evalListHOLExact, Option.some.injEq] at heval
    subst values
    simp [compileExpsExact, evalListHOLExact]
  | cons expression rest ih =>
    simp only [evalListHOLExact] at heval
    cases hh : evalHOLExact source.toExact expression with
    | none => simp [hh] at heval
    | some value =>
      cases ht : evalListHOLExact source.toExact rest with
      | none => simp [hh, ht] at heval
      | some tail =>
        have hv : value :: tail = values := by simpa [hh, ht] using heval
        subst values
        have htarget := hpoint expression (by simp) value hh
        change evalHOLExact (convertStateExact context source).toExact
          (compileExpExact context expression) = some (convertV value) at htarget
        have htail := ih tail (fun e hm => hpoint e (by simp [hm])) ht
        simp only [compileExpsExact, evalListHOLExact, htarget, htail, List.map_cons]
end Flapjack.Pancake.Proofs.PanStructs.CompileExpMmapHelper
