import Flapjack.Pancake.Proofs.PanStructs.FieldsInOrderReorderNoop
namespace Flapjack.Pancake.Proofs.PanStructs.CompileExpNStruct
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.Proofs.PanStructs.ConvertState
open Flapjack.Pancake.Proofs.PanStructs.ShapeMap
open Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact

/-- Flapjack exact list-evaluator infrastructure: successful named-field
execution retains the complete name list and order, including duplicates. -/
theorem evalFields_names {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ)
    (fields : List (MlS × ExpHOL width)) (values : List (MlS × ValueHOL width))
    (h : @evalListFieldsHOLExact width σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) fields = some values) :
    values.map Prod.fst = fields.map Prod.fst := by
  classical
  induction fields generalizing values with
  | nil =>
    simp only [evalListFieldsHOLExact, Option.some.injEq] at h
    simp [← h]
  | cons entry rest ih =>
    obtain ⟨name, expression⟩ := entry
    simp only [evalListFieldsHOLExact] at h
    cases hh : evalHOLExact source.toExact expression with
    | none => simp [hh] at h
    | some value =>
      cases ht : evalListFieldsHOLExact source.toExact rest with
      | none => simp [hh, ht] at h
      | some tail =>
        have hv : (name, value) :: tail = values := by simpa [hh, ht] using h
        subst values
        simp only [List.map_cons, ih tail ht]
/-- Flapjack shape-check infrastructure: equal lengths make the original
zip/all shape comparison imply the entire list equality. Length is derived
from source field names and successful field evaluation in the constructor. -/
theorem shapes_zip_eq (left right : List ShapeHOL)
    (hlen : left.length = right.length)
    (h : (left.zip right).all (fun pair => shapeEqHOL pair.1 pair.2) = true) :
    left = right := by
  induction left generalizing right with
  | nil =>
    have hr : right = [] := List.length_eq_zero_iff.mp hlen.symm
    exact hr.symm
  | cons head tail ih =>
    cases right with
    | nil => simp at hlen
    | cons other rest =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
      have heq := (shapeEqHOL_eq_true head other).mp h.1
      subst other
      exact congrArg (List.cons head) (ih rest hlen h.2)
/-- Flapjack list induction used by the genuine NStruct case. Per-field
facts are supplied by its original conditional child induction hypotheses. -/
theorem evalFields_converted {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (context : ContextExact)
    (fields : List (MlS × ExpHOL width)) (values : List (MlS × ValueHOL width))
    (heval : @evalListFieldsHOLExact width σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) fields = some values)
    (hchildren : ∀ entry ∈ fields, ∀ value : ValueHOL width,
      @evalHOLExact width σ _ source.toExact
        (fun a => Classical.propDecidable (source.memaddrs a)) entry.2 = some value →
      valueFldsOkHOLExact source.structs value = true ∧
      @evalHOLExact width σ _ (convertStateExact context source).toExact
        (fun a => Classical.propDecidable ((convertStateExact context source).toExact.memaddrs a))
        (compileExpExact context entry.2) = some (convertV value)) :
    fieldsFldsOkHOLExact source.structs values = true ∧
    @evalListHOLExact width σ _ (convertStateExact context source).toExact
      (fun a => Classical.propDecidable ((convertStateExact context source).toExact.memaddrs a))
      (fields.map (fun entry => compileExpExact context entry.2)) =
      some (values.map (fun entry => convertV entry.2)) := by
  classical
  induction fields generalizing values with
  | nil =>
    simp only [evalListFieldsHOLExact, Option.some.injEq] at heval
    subst values
    simp [fieldsFldsOkHOLExact, evalListHOLExact]
  | cons entry rest ih =>
    obtain ⟨name, expression⟩ := entry
    simp only [evalListFieldsHOLExact] at heval
    cases hh : evalHOLExact source.toExact expression with
    | none => simp [hh] at heval
    | some value =>
      cases ht : evalListFieldsHOLExact source.toExact rest with
      | none => simp [hh, ht] at heval
      | some tail =>
        have hv : (name, value) :: tail = values := by simpa [hh, ht] using heval
        subst values
        obtain ⟨hvalid, htarget⟩ := hchildren (name, expression) (by simp) value hh
        obtain ⟨htvalid, httarget⟩ := ih tail ht
          (fun entry hm => hchildren entry (by simp [hm]))
        refine ⟨?_, ?_⟩
        · simp [fieldsFldsOkHOLExact, hvalid, htvalid]
        · simp only [List.map_cons, evalListHOLExact]
          rw [htarget, httarget]
/-- Canonical imported state-carrier roundtrip for this representation qualifier.
Flapjack infrastructure, not an independent HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Genuine NStruct case; conditional child IH retains the original lookup and name-order guards. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectNStruct {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (context : ContextExact)
    (name : MlS) (fields : List (MlS × ExpHOL width)) (value : ValueHOL width)
    (ih : ∀ info : StructInfoHOLExact,
      structContextLookupHOL name source.structs = some info →
      info.fields.map Prod.fst = fields.map Prod.fst →
      ∀ expression ∈ fields.map Prod.snd, ∀ childValue : ValueHOL width,
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
        (fun a => Classical.propDecidable (source.memaddrs a)) (.nstruct name fields : ExpHOL width) = some value ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs) :
    oldExpShapeExact context (.nstruct name fields : ExpHOL width) = shapeOfHOLExact value ∧
    valueFldsOkHOLExact source.structs value = true ∧
    @PanSemStateFiniteExact.evalHOLFinite width σ _ (convertStateExact context source)
      (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
      (compileExpExact context (.nstruct name fields : ExpHOL width)) = some (convertV value) := by
  classical
  rcases h with ⟨heval, hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩
  have hr := heval
  simp only [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact,
    PanSemStateFiniteExact.toExact] at hr
  cases hi : structContextLookupHOL name source.structs with
  | none => simp [hi] at hr
  | some info =>
    by_cases hn : info.fields.map Prod.fst = fields.map Prod.fst
    · cases he : evalListFieldsHOLExact source.toExact fields with
      | none => simp [hi, hn, he] at hr
      | some values =>
        by_cases hs : ((info.fields.map Prod.snd).zip
            (values.map (fun entry => shapeOfHOLExact entry.2))).all
              (fun pair => shapeEqHOL pair.1 pair.2) = true
        · have hv : ValueHOL.nStruct name values = value := by
            simpa [hi, hn, he, hs, PanSemStateFiniteExact.toExact] using hr
          subst value
          have hvnames := evalFields_names source fields values he
          have hlen : (info.fields.map Prod.snd).length =
              (values.map (fun entry => shapeOfHOLExact entry.2)).length := by
            simpa only [List.length_map] using congrArg List.length (hn.trans hvnames.symm)
          have hshapes := shapes_zip_eq _ _ hlen hs
          obtain ⟨hvalid, htarget⟩ := evalFields_converted source context fields values he
            (fun entry hm v hev => by
              have hmem : entry.2 ∈ fields.map Prod.snd := List.mem_map.mpr ⟨entry, hm, rfl⟩
              obtain ⟨_, hv, ht⟩ := ih info hi hn entry.2 hmem v
                ⟨hev, hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩
              exact ⟨hv, ht⟩)
          have hcontext : context.structs.findSome?
              (fun entry => if entry.1 = name then some entry.2 else none) = some info.fields := by
            rw [hstructs]
            exact CompileExpNField.structFields_lookup source.structs name info hi
          have hcompiled : compileExpExact context (.nstruct name fields : ExpHOL width) =
              .rstruct (fields.map (fun entry => compileExpExact context entry.2)) := by
            simp only [compileExpExact, hcontext]
            congr 1
            exact FieldsInOrderReorderNoop.fieldsInOrderReorderNoopExact context fields info.fields
              hn (structInfosOkHOLExact_lookup_fields_nodup name source.structs info hi hinfo)
          refine ⟨?_, ?_, ?_⟩
          · simp [oldExpShapeExact, shapeOfHOLExact]
          · simp [valueFldsOkHOLExact, hvalid, hi, hvnames, ← hn,
              shapeEqListHOL_eq_true, hshapes]
          · simp only [hcompiled, PanSemStateFiniteExact.evalHOLFinite, evalHOLExact]
            rw [htarget]
            simp [convertV]
        · simp [hi, hn, he, hs] at hr
    · simp [hi, hn] at hr
end Flapjack.Pancake.Proofs.PanStructs.CompileExpNStruct
