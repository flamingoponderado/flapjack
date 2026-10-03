import Flapjack.Pancake.Proofs.PanStructs.ConvertState
import Flapjack.Pancake.Proofs.PanStructs.ShapeMap
import Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact
import Flapjack.Pancake.PanStructs.CompileExpExact
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant
namespace Flapjack.Pancake.Proofs.PanStructs.CompileExpAtomic
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.Proofs.PanStructs.ConvertState
open Flapjack.Pancake.Proofs.PanStructs.ShapeMap
open Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact

/-- Canonical owning-carrier roundtrip for the finite-map representation qualifier.
Flapjack infrastructure, not a distinct HOL source theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Genuine Const case of the full HOL expression theorem, retaining all
seven source hypotheses and deriving all three conclusions. No recursive IH is
needed for this constructor. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectConst {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (context : ContextExact)
    (constant : BitVec width) (value : ValueHOL width)
    (h : @PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a)) (.const constant) = some value ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs) :
    oldExpShapeExact context (.const constant) = shapeOfHOLExact value ∧
    valueFldsOkHOLExact source.structs value = true ∧
    @PanSemStateFiniteExact.evalHOLFinite width σ _ (convertStateExact context source)
      (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
      (compileExpExact context (.const constant)) = some (convertV value) := by
  have hv : value = .val (.word constant) := by
    simpa only [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, Option.some.injEq]
      using h.1.symm
  subst value
  refine ⟨?_, ?_, ?_⟩
  · simp [oldExpShapeExact, shapeOfHOLExact]
  · simp only [valueFldsOkHOLExact]
  · simp [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, compileExpExact,
      convertV, convertStateExact, PanSemStateFiniteExact.toExact]

/-- Genuine BaseAddr case of the full HOL expression theorem, retaining all
seven source hypotheses and deriving all three conclusions. No recursive IH is
needed for this constructor. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectBaseAddr {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (context : ContextExact)
    (value : ValueHOL width)
    (h : @PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a)) .baseAddr = some value ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs) :
    oldExpShapeExact context (.baseAddr : ExpHOL width) = shapeOfHOLExact value ∧
    valueFldsOkHOLExact source.structs value = true ∧
    @PanSemStateFiniteExact.evalHOLFinite width σ _ (convertStateExact context source)
      (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
      (compileExpExact context .baseAddr) = some (convertV value) := by
  have hv : value = .val (.word source.baseAddr) := by
    simpa only [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, Option.some.injEq]
      using h.1.symm
  subst value
  refine ⟨?_, ?_, ?_⟩
  · simp [oldExpShapeExact, shapeOfHOLExact]
  · simp only [valueFldsOkHOLExact]
  · simp [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, compileExpExact,
      convertV, convertStateExact, PanSemStateFiniteExact.toExact]

/-- Genuine TopAddr case of the full HOL expression theorem, retaining all
seven source hypotheses and deriving all three conclusions. No recursive IH is
needed for this constructor. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectTopAddr {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (context : ContextExact)
    (value : ValueHOL width)
    (h : @PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a)) .topAddr = some value ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs) :
    oldExpShapeExact context (.topAddr : ExpHOL width) = shapeOfHOLExact value ∧
    valueFldsOkHOLExact source.structs value = true ∧
    @PanSemStateFiniteExact.evalHOLFinite width σ _ (convertStateExact context source)
      (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
      (compileExpExact context .topAddr) = some (convertV value) := by
  have hv : value = .val (.word source.topAddr) := by
    simpa only [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, Option.some.injEq]
      using h.1.symm
  subst value
  refine ⟨?_, ?_, ?_⟩
  · simp [oldExpShapeExact, shapeOfHOLExact]
  · simp only [valueFldsOkHOLExact]
  · simp [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, compileExpExact,
      convertV, convertStateExact, PanSemStateFiniteExact.toExact]

end Flapjack.Pancake.Proofs.PanStructs.CompileExpAtomic
