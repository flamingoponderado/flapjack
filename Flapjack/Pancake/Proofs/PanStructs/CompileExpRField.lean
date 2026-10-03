import Flapjack.Pancake.Proofs.PanStructs.CompileExpVar
namespace Flapjack.Pancake.Proofs.PanStructs.CompileExpRField
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.Proofs.PanStructs.ConvertState
open Flapjack.Pancake.Proofs.PanStructs.ShapeMap
open Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact

/-- Flapjack list validity infrastructure: selecting an existing record field
preserves the source field-validity predicate. -/
theorem valuesFldsOk_getElem {width : Nat} [NeZero width]
    (context : StructContextExact) (values : List (ValueHOL width))
    (index : Nat) (value : ValueHOL width)
    (hvalid : valuesFldsOkHOLExact context values = true)
    (hindex : values[index]? = some value) :
    valueFldsOkHOLExact context value = true := by
  induction values generalizing index with
  | nil => simp at hindex
  | cons head tail ih =>
    have parts : valueFldsOkHOLExact context head = true ∧
        valuesFldsOkHOLExact context tail = true := by
      simpa only [valuesFldsOkHOLExact, Bool.and_eq_true] using hvalid
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hindex
      simpa only [hindex] using parts.1
    | succ index =>
      apply ih index parts.2
      simpa only [List.getElem?_cons_succ] using hindex
/-- Canonical imported state-carrier roundtrip for this representation qualifier.
Flapjack infrastructure, not an independent HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Genuine recursive RField case, with only the full original child induction hypothesis. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectRField {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (context : ContextExact)
    (index : Nat) (expression : ExpHOL width) (value : ValueHOL width)
    (ih : ∀ childValue : ValueHOL width,
      @PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a)) expression = some childValue ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs →
   oldExpShapeExact context expression = shapeOfHOLExact childValue ∧
    valueFldsOkHOLExact source.structs childValue = true ∧
    @PanSemStateFiniteExact.evalHOLFinite width σ _ (convertStateExact context source)
      (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
      (compileExpExact context expression) = some (convertV childValue))
    (h : @PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a)) (.rfield index expression : ExpHOL width) = some value ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs) :
    oldExpShapeExact context (.rfield index expression : ExpHOL width) = shapeOfHOLExact value ∧
    valueFldsOkHOLExact source.structs value = true ∧
    @PanSemStateFiniteExact.evalHOLFinite width σ _ (convertStateExact context source)
      (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
      (compileExpExact context (.rfield index expression : ExpHOL width)) = some (convertV value) := by
  rcases h with ⟨heval, hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩
  have hr := heval
  simp only [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact] at hr
  cases hchild : @PanSemStateFiniteExact.evalHOLFinite width σ _ source
      (fun a => Classical.propDecidable (source.memaddrs a)) expression with
  | none =>
    simp only [PanSemStateFiniteExact.evalHOLFinite] at hchild
    simp [hchild] at hr
  | some child =>
    cases child with
    | val word =>
      simp only [PanSemStateFiniteExact.evalHOLFinite] at hchild
      simp [hchild] at hr
    | nStruct name fields =>
      simp only [PanSemStateFiniteExact.evalHOLFinite] at hchild
      simp [hchild] at hr
    | rStruct values =>
      have hindex : values[index]? = some value := by
        simp only [PanSemStateFiniteExact.evalHOLFinite] at hchild
        simpa only [hchild] using hr
      obtain ⟨hshape, hvalid, htarget⟩ := ih (.rStruct values)
        ⟨hchild, hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩
      refine ⟨?_, ?_, ?_⟩
      · simp only [oldExpShapeExact, hshape, shapeOfHOLExact]
        simp [List.getElem?_map, hindex]
      · apply valuesFldsOk_getElem source.structs values index value
        · simpa only [valueFldsOkHOLExact] using hvalid
        · exact hindex
      · simp only [compileExpExact, PanSemStateFiniteExact.evalHOLFinite,
          evalHOLExact] at htarget ⊢
        rw [htarget]
        simp [convertV, List.getElem?_map, hindex]
end Flapjack.Pancake.Proofs.PanStructs.CompileExpRField
