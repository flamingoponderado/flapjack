import Flapjack.Pancake.Proofs.PanStructs.CompileExpMmapHelper
namespace Flapjack.Pancake.Proofs.PanStructs.CompileExpOperators
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.Proofs.PanStructs.ConvertState
open Flapjack.Pancake.Proofs.PanStructs.ShapeMap
open Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact

/-- Flapjack argument infrastructure: the actual source operator word guard
implies conversion leaves the complete argument list unchanged. -/
theorem convert_word_arguments {width : Nat} [NeZero width]
    (values : List (ValueHOL width)) (h : values.all valueIsWord = true) :
    values.map convertV = values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases value with
    | val word => simp [convertV, ih h.2]
    | rStruct fields => simp [valueIsWord] at h
    | nStruct name fields => simp [valueIsWord] at h
/-- Canonical imported state-carrier roundtrip for this representation qualifier.
Flapjack infrastructure, not an independent HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Genuine Op case retaining all original hypotheses and member-expression IHs. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectOp {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (context : ContextExact)
    (operator : BinOp) (expressions : List (ExpHOL width)) (value : ValueHOL width)
    (ih : ∀ expression ∈ expressions, ∀ childValue : ValueHOL width,
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
        (fun a => Classical.propDecidable (source.memaddrs a)) (.op operator expressions : ExpHOL width) = some value ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs) :
    oldExpShapeExact context (.op operator expressions : ExpHOL width) = shapeOfHOLExact value ∧
    valueFldsOkHOLExact source.structs value = true ∧
    @PanSemStateFiniteExact.evalHOLFinite width σ _ (convertStateExact context source)
      (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
      (compileExpExact context (.op operator expressions : ExpHOL width)) = some (convertV value) := by
  classical
  rcases h with ⟨heval, hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩
  have hr := heval
  simp only [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact] at hr
  cases he : evalListHOLExact source.toExact expressions with
  | none => simp [he] at hr
  | some values =>
    by_cases hw : values.all valueIsWord = true
    · cases hop : wordOpHOL operator (values.map valueWord) with
      | none => simp [he, hw, hop] at hr
      | some word =>
        have hv : ValueHOL.val (.word word) = value := by simpa [he, hw, hop] using hr
        subst value
        have ht := CompileExpMmapHelper.compileExpCorrectMmapHelper source context expressions values
          ⟨he, fun expression hm v hev =>
            (ih expression hm v ⟨hev, hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩).2.2⟩
        change evalListHOLExact (convertStateExact context source).toExact
          (compileExpsExact context expressions) = some (values.map convertV) at ht
        rw [convert_word_arguments values hw] at ht
        refine ⟨?_, ?_, ?_⟩
        · simp [oldExpShapeExact, shapeOfHOLExact]
        · simp [valueFldsOkHOLExact]
        · simp only [compileExpExact, PanSemStateFiniteExact.evalHOLFinite, evalHOLExact]
          rw [ht]
          simp [hw, hop, convertV]
    · simp [he, hw] at hr
/-- Genuine Panop case retaining all original hypotheses and member-expression IHs. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectPanop {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (context : ContextExact)
    (operator : PanOp) (expressions : List (ExpHOL width)) (value : ValueHOL width)
    (ih : ∀ expression ∈ expressions, ∀ childValue : ValueHOL width,
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
        (fun a => Classical.propDecidable (source.memaddrs a)) (.panop operator expressions : ExpHOL width) = some value ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs) :
    oldExpShapeExact context (.panop operator expressions : ExpHOL width) = shapeOfHOLExact value ∧
    valueFldsOkHOLExact source.structs value = true ∧
    @PanSemStateFiniteExact.evalHOLFinite width σ _ (convertStateExact context source)
      (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
      (compileExpExact context (.panop operator expressions : ExpHOL width)) = some (convertV value) := by
  classical
  rcases h with ⟨heval, hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩
  have hr := heval
  simp only [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact] at hr
  cases he : evalListHOLExact source.toExact expressions with
  | none => simp [he] at hr
  | some values =>
    by_cases hw : values.all valueIsWord = true
    · cases hop : panOpHOL operator (values.map valueWord) with
      | none => simp [he, hw, hop] at hr
      | some word =>
        have hv : ValueHOL.val (.word word) = value := by simpa [he, hw, hop] using hr
        subst value
        have ht := CompileExpMmapHelper.compileExpCorrectMmapHelper source context expressions values
          ⟨he, fun expression hm v hev =>
            (ih expression hm v ⟨hev, hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩).2.2⟩
        change evalListHOLExact (convertStateExact context source).toExact
          (compileExpsExact context expressions) = some (values.map convertV) at ht
        rw [convert_word_arguments values hw] at ht
        refine ⟨?_, ?_, ?_⟩
        · simp [oldExpShapeExact, shapeOfHOLExact]
        · simp [valueFldsOkHOLExact]
        · simp only [compileExpExact, PanSemStateFiniteExact.evalHOLFinite, evalHOLExact]
          rw [ht]
          simp [hw, hop, convertV]
    · simp [he, hw] at hr
end Flapjack.Pancake.Proofs.PanStructs.CompileExpOperators
