import Flapjack.Pancake.Proofs.PanStructs.CompileExpRField
namespace Flapjack.Pancake.Proofs.PanStructs.CompileExpRStruct
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.Proofs.PanStructs.ConvertState
open Flapjack.Pancake.Proofs.PanStructs.ShapeMap
open Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact

/-- Flapjack exact evaluator infrastructure: successful record-field list
execution preserves list length, without a pre-imposed resource or bound condition. -/
theorem evalList_length {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (expressions : List (ExpHOL width))
    (values : List (ValueHOL width))
    (heval : @PanSemStateFiniteExact.evalListHOLFinite width σ _ source
      (fun a => Classical.propDecidable (source.memaddrs a)) expressions = some values) :
    values.length = expressions.length := by
  classical
  change evalListHOLExact source.toExact expressions = some values at heval
  induction expressions generalizing values with
  | nil =>
    simp only [evalListHOLExact, Option.some.injEq] at heval
    simp [← heval]
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
        simp only [List.length_cons, ih tail ht]
/-- Canonical imported state-carrier roundtrip for this representation qualifier.
Flapjack infrastructure, not an independent HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Genuine RStruct constructor case with only the original member-expression induction hypotheses. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectRStruct {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (context : ContextExact)
    (expressions : List (ExpHOL width)) (value : ValueHOL width)
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
        (fun a => Classical.propDecidable (source.memaddrs a)) (.rstruct expressions : ExpHOL width) = some value ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs) :
    oldExpShapeExact context (.rstruct expressions : ExpHOL width) = shapeOfHOLExact value ∧
    valueFldsOkHOLExact source.structs value = true ∧
    @PanSemStateFiniteExact.evalHOLFinite width σ _ (convertStateExact context source)
      (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
      (compileExpExact context (.rstruct expressions : ExpHOL width)) = some (convertV value) := by
  classical
  rcases h with ⟨heval, hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩
  have list_result : ∀ (es : List (ExpHOL width)) (vs : List (ValueHOL width)),
      (∀ e ∈ es, e ∈ expressions) →
      evalListHOLExact source.toExact es = some vs →
      oldExpShapesExact context es = vs.map shapeOfHOLExact ∧
      valuesFldsOkHOLExact source.structs vs = true ∧
      evalListHOLExact (convertStateExact context source).toExact
        (compileExpsExact context es) = some (vs.map convertV) := by
    intro es
    induction es with
    | nil =>
      intro vs hmem he
      simp only [evalListHOLExact, Option.some.injEq] at he
      subst vs
      simp [oldExpShapesExact, valuesFldsOkHOLExact, compileExpsExact, evalListHOLExact]
    | cons e es inductionHyp =>
      intro vs hmem he
      simp only [evalListHOLExact] at he
      cases hh : evalHOLExact source.toExact e with
      | none => simp [hh] at he
      | some v =>
        cases ht : evalListHOLExact source.toExact es with
        | none => simp [hh, ht] at he
        | some tail =>
          have hv : v :: tail = vs := by simpa [hh, ht] using he
          subst vs
          obtain ⟨hshape, hvalid, htarget⟩ := ih e (hmem e (by simp)) v
            ⟨hh, hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩
          obtain ⟨htshape, htvalid, httarget⟩ := inductionHyp tail
            (fun x hx => hmem x (by simp [hx])) ht
          change evalHOLExact (convertStateExact context source).toExact
            (compileExpExact context e) = some (convertV v) at htarget
          refine ⟨?_, ?_, ?_⟩
          · simp [oldExpShapesExact, hshape, htshape]
          · simp [valuesFldsOkHOLExact, hvalid, htvalid]
          · simp only [compileExpsExact, evalListHOLExact, htarget, httarget, List.map_cons]
  have hr := heval
  simp only [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact] at hr
  cases he : evalListHOLExact source.toExact expressions with
  | none => simp [he] at hr
  | some values =>
    have hv : ValueHOL.rStruct values = value := by simpa [he] using hr
    subst value
    obtain ⟨hs, hv, ht⟩ := list_result expressions values (fun _ hx => hx) he
    refine ⟨?_, ?_, ?_⟩
    · simp [oldExpShapeExact, shapeOfHOLExact, hs]
    · simpa only [valueFldsOkHOLExact] using hv
    · simp only [compileExpExact, PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, ht]
      simp [convertV]
end Flapjack.Pancake.Proofs.PanStructs.CompileExpRStruct
