import Flapjack.Pancake.Proofs.PanStructs.CompileExpLoad32
namespace Flapjack.Pancake.Proofs.PanStructs.CompileExpBytesInWord
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

/-- Genuine BytesInWord case retaining all seven original source hypotheses. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectBytesInWord {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (context : ContextExact)
    (value : ValueHOL width)
    (h : @PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a)) (.bytesInWord : ExpHOL width) = some value ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs) :
    oldExpShapeExact context (.bytesInWord : ExpHOL width) = shapeOfHOLExact value ∧
    valueFldsOkHOLExact source.structs value = true ∧
    @PanSemStateFiniteExact.evalHOLFinite width σ _ (convertStateExact context source)
      (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
      (compileExpExact context (.bytesInWord : ExpHOL width)) = some (convertV value) := by
  have hv : ValueHOL.val (.word (bytesInWordHOL width)) = value := by
    simpa only [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, Option.some.injEq] using h.1
  subst value
  refine ⟨?_, ?_, ?_⟩
  · simp [oldExpShapeExact, shapeOfHOLExact]
  · simp [valueFldsOkHOLExact]
  · simp [compileExpExact, PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, convertV]
end Flapjack.Pancake.Proofs.PanStructs.CompileExpBytesInWord
