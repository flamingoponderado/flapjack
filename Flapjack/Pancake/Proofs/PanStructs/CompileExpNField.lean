import Flapjack.Pancake.Proofs.PanStructs.CompileExpRStruct
namespace Flapjack.Pancake.Proofs.PanStructs.CompileExpNField
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.Proofs.PanStructs.ConvertState
open Flapjack.Pancake.Proofs.PanStructs.ShapeMap
open Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact

/-- Flapjack exact named-field infrastructure. Source field-list validity
and a successful actual first-match lookup imply result validity. -/
theorem fieldsFldsOk_lookup {width : Nat} [NeZero width]
    (context : StructContextExact) (fields : List (MlS × ValueHOL width))
    (name : MlS) (value : ValueHOL width)
    (hvalid : fieldsFldsOkHOLExact context fields = true)
    (hlookup : lookupFieldHOL name fields = some value) :
    valueFldsOkHOLExact context value = true := by
  induction fields with
  | nil => simp [lookupFieldHOL] at hlookup
  | cons entry fields ih =>
    obtain ⟨candidate, head⟩ := entry
    have parts : valueFldsOkHOLExact context head = true ∧
        fieldsFldsOkHOLExact context fields = true := by
      simpa only [fieldsFldsOkHOLExact, Bool.and_eq_true] using hvalid
    by_cases heq : candidate = name
    · simp only [lookupFieldHOL, heq, ↓reduceIte, Option.some.injEq] at hlookup
      simpa only [hlookup] using parts.1
    · apply ih parts.2
      simpa only [lookupFieldHOL, heq, ↓reduceIte] using hlookup
/-- Flapjack first-match codec infrastructure: successful named-field lookup
produces its actual index and payload. No distinctness or bound premise. -/
theorem lookupField_index {width : Nat} [NeZero width]
    (name : MlS) (fields : List (MlS × ValueHOL width)) (value : ValueHOL width)
    (h : lookupFieldHOL name fields = some value) :
    ∃ index, afindi name fields = some index ∧
      (fields.map Prod.snd)[index]? = some value := by
  induction fields with
  | nil => simp [lookupFieldHOL] at h
  | cons entry fields ih =>
    obtain ⟨candidate, head⟩ := entry
    by_cases heq : candidate = name
    · simp only [lookupFieldHOL, heq, ↓reduceIte, Option.some.injEq] at h
      subst candidate
      subst head
      exact ⟨0, by simp [afindi_cons], by simp⟩
    · have htail : lookupFieldHOL name fields = some value := by
        simpa only [lookupFieldHOL, heq, ↓reduceIte] using h
      obtain ⟨index, hi, hv⟩ := ih htail
      refine ⟨index + 1, ?_, ?_⟩
      · simp [afindi_cons, Ne.symm heq, hi]
      · simpa only [List.map_cons, List.getElem?_cons_succ] using hv
/-- Flapjack payload codec infrastructure: the index supplied by successful
source lookup selects the converted payload in the actual converted record. -/
theorem lookupField_converted_index {width : Nat} [NeZero width]
    (name : MlS) (fields : List (MlS × ValueHOL width)) (value : ValueHOL width)
    (h : lookupFieldHOL name fields = some value) :
    ∃ index, afindi name fields = some index ∧
      (fields.map (fun entry => convertV entry.2))[index]? = some (convertV value) := by
  obtain ⟨index, hi, hv⟩ := lookupField_index name fields value h
  refine ⟨index, hi, ?_⟩
  have hmap := congrArg (Option.map convertV) hv
  simpa only [List.getElem?_map, List.map_map, Function.comp_def, Option.map_some, Option.map_map] using hmap
/-- Flapjack factoring of actual named-value validity. The source Boolean
predicate itself supplies the structure lookup, key order and shape equality. -/
theorem namedValidity_fields {width : Nat} [NeZero width]
    (context : StructContextExact) (name : MlS)
    (fields : List (MlS × ValueHOL width))
    (h : valueFldsOkHOLExact context (.nStruct name fields) = true) :
    ∃ info, structContextLookupHOL name context = some info ∧
      fieldsFldsOkHOLExact context fields = true ∧
      fields.map Prod.fst = info.fields.map Prod.fst ∧
      fields.map (fun entry => shapeOfHOLExact entry.2) = info.fields.map Prod.snd := by
  simp only [valueFldsOkHOLExact, Bool.and_eq_true] at h
  cases hi : structContextLookupHOL name context with
  | none => simp [hi] at h
  | some info =>
    simp only [hi, Bool.and_eq_true] at h
    exact ⟨info, rfl, h.1, by simpa using h.2.1,
      (shapeEqListHOL_eq_true _ _).mp h.2.2⟩

/-- Flapjack struct-context codec infrastructure. Mapping source infos to fields
preserves the actual first binding, even with duplicate structure names. -/
theorem structFields_lookup (context : StructContextExact) (name : MlS)
    (info : StructInfoHOLExact) (h : structContextLookupHOL name context = some info) :
    (context.map (fun entry => (entry.1, entry.2.fields))).findSome?
      (fun entry => if entry.1 = name then some entry.2 else none) = some info.fields := by
  induction context with
  | nil => simp [structContextLookupHOL] at h
  | cons entry rest ih =>
    obtain ⟨candidate, head⟩ := entry
    by_cases heq : name = candidate
    · simp only [structContextLookupHOL, heq, ↓reduceIte, Option.some.injEq] at h
      subst head
      simp [heq]
    · have ht : structContextLookupHOL name rest = some info := by
        simpa only [structContextLookupHOL, heq, ↓reduceIte] using h
      simpa [Ne.symm heq] using ih ht
/-- Flapjack generic first-match/index codec equality. -/
theorem findSome_afindi {α β : Type} [DecidableEq α]
    (name : α) (entries : List (α × β)) :
    entries.findSome? (fun entry => if entry.1 = name then some entry.2 else none) =
      (afindi name entries).bind (fun index => (entries.map Prod.snd)[index]?) := by
  induction entries with
  | nil => simp [afindi]
  | cons entry rest ih =>
    obtain ⟨candidate, value⟩ := entry
    by_cases heq : name = candidate
    · simp [afindi_cons, heq]
    · simp only [afindi_cons, heq, ↓reduceIte, List.map_cons]
      simp only [List.findSome?_cons, Ne.symm heq, ↓reduceIte]
      rw [ih]
      cases afindi name rest with
      | none => rfl
      | some index => simp
/-- Canonical imported state-carrier roundtrip for this representation qualifier.
Flapjack infrastructure, not an independent HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Genuine NField case with only the original full child induction hypothesis. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectNField {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (context : ContextExact)
    (field : MlS) (expression : ExpHOL width) (value : ValueHOL width)
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
        (fun a => Classical.propDecidable (source.memaddrs a)) (.nfield field expression : ExpHOL width) = some value ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs) :
    oldExpShapeExact context (.nfield field expression : ExpHOL width) = shapeOfHOLExact value ∧
    valueFldsOkHOLExact source.structs value = true ∧
    @PanSemStateFiniteExact.evalHOLFinite width σ _ (convertStateExact context source)
      (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
      (compileExpExact context (.nfield field expression : ExpHOL width)) = some (convertV value) := by
  classical
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
    | rStruct values =>
      simp only [PanSemStateFiniteExact.evalHOLFinite] at hchild
      simp [hchild] at hr
    | nStruct name fields =>
      obtain ⟨hcshape, hcvalid, htarget⟩ := ih (.nStruct name fields)
        ⟨hchild, hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩
      obtain ⟨info, hi, hfields, hnames, hshapes⟩ := namedValidity_fields
        source.structs name fields hcvalid
      have hl : lookupFieldHOL field fields = some value := by
        simp only [PanSemStateFiniteExact.evalHOLFinite] at hchild
        simpa only [hchild, PanSemStateFiniteExact.toExact, hi, Option.isSome_some,
          ↓reduceIte] using hr
      obtain ⟨index, hindex, hvalue⟩ := lookupField_index field fields value hl
      have hinfoIndex : afindi field info.fields = some index := by
        rw [← afindi_eq_of_map_fst_eq field fields info.fields hnames]
        exact hindex
      have hcontext : context.structs.findSome?
          (fun entry => if entry.1 = name then some entry.2 else none) = some info.fields := by
        rw [hstructs]
        exact structFields_lookup source.structs name info hi
      have hshapeIndex : (info.fields.map Prod.snd)[index]? = some (shapeOfHOLExact value) := by
        rw [← hshapes]
        have hm := congrArg (Option.map shapeOfHOLExact) hvalue
        simpa only [List.getElem?_map, Option.map_map, Function.comp_def,
          Option.map_some] using hm
      refine ⟨?_, fieldsFldsOk_lookup source.structs fields field value hfields hl, ?_⟩
      · simp only [oldExpShapeExact, hcshape, shapeOfHOLExact, hcontext]
        rw [findSome_afindi, hinfoIndex]
        simpa only [Option.bind_some, Option.getD_some] using
          congrArg (fun result : Option ShapeHOL => result.getD .one) hshapeIndex
      · have ht := htarget
        change evalHOLExact (convertStateExact context source).toExact
          (compileExpExact context expression) = some (convertV (.nStruct name fields)) at ht
        simp only [compileExpExact, hcshape, shapeOfHOLExact, hcontext, hinfoIndex,
          Option.getD_some, PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, ht, convertV]
        have hm := congrArg (Option.map convertV) hvalue
        simpa only [List.getElem?_map, Option.map_map, Function.comp_def,
          Option.map_some] using hm
end Flapjack.Pancake.Proofs.PanStructs.CompileExpNField
