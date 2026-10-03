import Flapjack.Pancake.Proofs.PanStructs.FlattenConversion
import Flapjack.Pancake.Proofs.PanStructs.CompileExpCorrectExact
import Flapjack.Pancake.Proofs.PanStructs.ValueShapeConversion
import Flapjack.Pancake.PanStructs.CompileProgExact
namespace Flapjack.Pancake.Proofs.PanStructs.LookupCodeFields
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.Proofs.PanStructs.ConvertState
open Flapjack.Pancake.Proofs.PanStructs.ShapeMap
open Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact

/-- Canonical imported state-carrier roundtrip for this representation qualifier.
Flapjack infrastructure, not an independent HOL declaration. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness


/-- Flapjack list-evaluation proof plumbing, no independent HOL declaration. -/
private theorem evalListEvery {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (expressions : List (ExpHOL width))
    (values : List (ValueHOL width)) (P : ValueHOL width → Prop)
    (heval : @evalListHOLExact width σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) expressions = some values)
    (hpoint : ∀ expression ∈ expressions, ∀ value,
      @evalHOLExact width σ _ source.toExact
        (fun a => Classical.propDecidable (source.memaddrs a)) expression = some value → P value) :
    ∀ value ∈ values, P value := by
  classical
  induction expressions generalizing values with
  | nil =>
    simp only [evalListHOLExact,Option.some.injEq] at heval
    subst values
    simp
  | cons expression rest ih =>
    simp only [evalListHOLExact] at heval
    cases hh : evalHOLExact source.toExact expression with
    | none => simp [hh] at heval
    | some value =>
      cases ht : evalListHOLExact source.toExact rest with
      | none => simp [hh,ht] at heval
      | some tail =>
        have hv : value :: tail = values := by simpa [hh,ht] using heval
        subst values
        have hhead := hpoint expression (by simp) value hh
        have htail := ih tail ht (fun e hm => hpoint e (by simp [hm]))
        intro v hm
        rcases List.mem_cons.mp hm with heq | hmem
        · subst v
          exact hhead
        · exact htail v hmem

/-- Flapjack proof plumbing for the source parameter/argument shape guard. -/
private theorem parameterShapes {width : Nat} [NeZero width]
    (parameters : List (MlS × ShapeHOL)) (arguments : List (ValueHOL width))
    (hlen : parameters.length = arguments.length)
    (hguard : (parameters.zip arguments).all
      (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)) = true) :
    parameters = (parameters.map Prod.fst).zip (arguments.map shapeOfHOLExact) := by
  induction parameters generalizing arguments with
  | nil =>
    cases arguments with
    | nil => rfl
    | cons value rest => simp at hlen
  | cons parameter parameters ih =>
    cases arguments with
    | nil => simp at hlen
    | cons value values =>
      have htlen := Nat.succ.inj hlen
      simp only [List.zip_cons_cons,List.all_cons,Bool.and_eq_true] at hguard
      have hs := (shapeEqHOL_eq_true _ _).mp hguard.1
      rw [List.map_cons,List.map_cons,List.zip_cons_cons,← ih values htlen hguard.2]
      exact congrArg (fun head => head :: parameters) (Prod.ext rfl hs)

/-- Full original lookup_code_flds_ok, retaining ten source hypotheses and
all five conclusions, including existential callee context and actual lookup. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "lookup_code_flds_ok"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, calleeLocals])
  (words_as_type_indexed_bitvec)]
theorem lookupCodeFields {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (context : ContextExact)
    (expressions : List (ExpHOL width)) (arguments : List (ValueHOL width))
    (function : MlS) (body : ProgHOL width)
    (calleeLocals : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
    (h : @PanSemStateFiniteExact.evalListHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a)) expressions = some arguments ∧
      PanSemStateFiniteExact.lookupCodeCanonicalHOL source.code function arguments =
        some (body,calleeLocals,returnShape) ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      context.structs = source.structs.map (fun entry => (entry.1,entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs) :
    @PanSemStateFiniteExact.evalListHOLFinite width σ _ (convertStateExact context source)
      (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
      (compileExpsExact context expressions) = some (arguments.map convertV) ∧
    (∀ value ∈ arguments, valueFldsOkHOLExact source.structs value = true) ∧
    (∃ parameters : List (MlS × ShapeHOL),
      PanSemStateFiniteExact.lookupCodeCanonicalHOL (convertStateExact context source).code
        function (arguments.map convertV) =
        some (compileProgExact {context with locals := parameters} body,
          calleeLocals.map2 (fun entry => convertV entry.2),
          compileShapeExact context.structs returnShape) ∧
      shapeMap parameters = calleeLocals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) calleeLocals ∧
    feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) calleeLocals := by
  classical
  rcases h with ⟨heval,hlookup,hlocals,hglobals,hstructs,hlocal,hglobal,hwlocal,hwglobal,hinfo⟩
  have htarget := CompileExpMmapHelper.compileExpCorrectMmapHelper source context expressions arguments
    ⟨heval,fun expression _ value hv =>
      (CompileExpCorrectExact.compileExpCorrectExact source context expression value
        ⟨hv,hlocals,hglobals,hstructs,hlocal,hglobal,hinfo⟩).2.2⟩
  have hproperties : ∀ value ∈ arguments,
      valueFldsOkHOLExact source.structs value = true ∧
      isWfShapeValueHOLExact source.structs value = true := by
    apply evalListEvery source expressions arguments
      (fun value => valueFldsOkHOLExact source.structs value = true ∧
        isWfShapeValueHOLExact source.structs value = true) heval
    intro expression _ value hv
    exact ⟨(CompileExpCorrectExact.compileExpCorrectExact source context expression value
        ⟨hv,hlocals,hglobals,hstructs,hlocal,hglobal,hinfo⟩).2.1,
      @evalHOLExact_isWfShapeValueHOLExact width σ _ source.toExact
        (fun a => Classical.propDecidable (source.memaddrs a)) hwlocal hwglobal expression value hv⟩
  have hraw := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    source.code.lookup function arguments body calleeLocals returnShape hlookup
  have hentry : ∃ parameters sourceBody sourceReturn,
      source.code.lookup function = some (parameters,sourceBody,sourceReturn) ∧
      (parameters.map Prod.fst).Nodup ∧ parameters.length = arguments.length ∧
      ((parameters.zip arguments).all
        (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    unfold lookupCodeHOLExact at hraw
    cases hc : source.code.lookup function with
    | none => simp [hc] at hraw
    | some entry =>
      rcases entry with ⟨parameters,sourceBody,sourceReturn⟩
      rw [hc] at hraw
      dsimp only at hraw
      split at hraw
      next hgood => exact ⟨parameters,sourceBody,sourceReturn,rfl,hgood⟩
      next => simp at hraw
  rcases hentry with ⟨parameters,sourceBody,sourceReturn,hcode,hgood⟩
  simp only [lookupCodeHOLExact,hcode,if_pos hgood,Option.some.injEq,Prod.mk.injEq] at hraw
  have hcallee : FUPDATE_LIST FEMPTY ((parameters.map Prod.fst).zip arguments) = calleeLocals.lookup := by
    have hx := hraw.2.1
    change FUPDATE_LIST_HOL FEMPTY ((parameters.map Prod.fst).zip arguments) = calleeLocals.lookup at hx
    simpa only [FUPDATE_LIST_HOL_eq_FUPDATE_LIST] using hx
  have hcalleeEvery : ∀ key value, calleeLocals.lookup key = some value →
      valueFldsOkHOLExact source.structs value = true ∧ isWfShapeValueHOLExact source.structs value = true := by
    intro key value hv
    rw [← hcallee] at hv
    rcases flookupFupdateList_mem_or_base FEMPTY ((parameters.map Prod.fst).zip arguments) key value hv with he | hb
    · rcases he with ⟨entry,hm,_,hvalue⟩
      have hmem := (List.of_mem_zip hm).2
      rw [hvalue] at hmem
      exact hproperties value hmem
    · simp [FLOOKUP,FEMPTY] at hb
  refine ⟨htarget,fun value hm => (hproperties value hm).1,?_,?_,?_⟩
  · have hparameters := parameterShapes parameters arguments hgood.2.1 hgood.2.2
    have hparameterMap : shapeMap parameters = calleeLocals.map2 (fun entry => shapeOfHOLExact entry.2) := by
      apply HolFiniteMapExact.ext
      funext key
      rw [shapeMap_lookup,HolFiniteMapExact.lookup_map2]
      change alistToFmap parameters key = (calleeLocals.lookup key).map shapeOfHOLExact
      rw [← hcallee,HolFiniteMapExact.map_updateList_eq]
      simp only [FEMPTY,Option.map_none]
      have hzip : ((parameters.map Prod.fst).zip arguments).map
          (fun entry => (entry.1,shapeOfHOLExact entry.2)) = parameters := by
        have he := hparameters.symm
        rw [List.zip_map_right] at he
        have hfun : Prod.map id (@shapeOfHOLExact width _) =
            (fun entry : MlS × ValueHOL width => (entry.1,shapeOfHOLExact entry.2)) := by
          funext entry
          cases entry
          rfl
        rw [hfun] at he
        exact he
      rw [hzip]
      have hfold := fmEmptyZipAlist (parameters.map Prod.fst) (arguments.map shapeOfHOLExact)
        (by simp only [List.length_map]; exact hgood.2.1) hgood.1
      rw [← hparameters] at hfold
      exact (congrFun hfold key).symm
    refine ⟨parameters,?_,hparameterMap⟩
    let compiledParameters := parameters.map
      (fun parameter => (parameter.1,compileShapeExact context.structs parameter.2))
    have hcompiledKeys : compiledParameters.map Prod.fst = parameters.map Prod.fst := by
      simp only [compiledParameters,List.map_map]
      rfl
    have hcompiledGuard : (compiledParameters.zip (arguments.map convertV)).all
        (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)) = true := by
      apply List.all_eq_true.mpr
      intro pair hm
      simp only [compiledParameters,List.zip_map] at hm
      rcases List.mem_map.mp hm with ⟨original,hmemOriginal,hpair⟩
      subst pair
      have hs := (shapeEqHOL_eq_true _ _).mp (List.all_eq_true.mp hgood.2.2 original hmemOriginal)
      have hv := hproperties original.2 (List.of_mem_zip hmemOriginal).2
      have hshape := ValueShapeConversion.shapeOfConvertVRev source.structs original.2
        ⟨hv.1,hv.2,hinfo⟩
      apply (shapeEqHOL_eq_true _ _).mpr
      dsimp only [Prod.map]
      rw [hshape,← hstructs,hs]
    have htargetCode : (convertStateExact context source).code.lookup function =
        some (compiledParameters,compileProgExact {context with locals := parameters} sourceBody,
          compileShapeExact context.structs sourceReturn) := by
      simp only [convertStateExact,convertCodeExact,HolFiniteMapExact.lookup_map2,hcode,Option.map_some]
      rfl
    have htargetGood : (compiledParameters.map Prod.fst).Nodup ∧
        compiledParameters.length = (arguments.map convertV).length ∧
        (compiledParameters.zip (arguments.map convertV)).all
          (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)) = true :=
      ⟨by rw [hcompiledKeys]; exact hgood.1,
        by simpa only [compiledParameters,List.length_map] using hgood.2.1,
        hcompiledGuard⟩
    have hfold : FUPDATE_LIST_HOL FEMPTY
        ((compiledParameters.map Prod.fst).zip (arguments.map convertV)) =
        (fun key => (calleeLocals.lookup key).map convertV) := by
      rw [FUPDATE_LIST_HOL_eq_FUPDATE_LIST,hcompiledKeys]
      funext key
      rw [← hcallee,HolFiniteMapExact.map_updateList_eq]
      simp only [FEMPTY,Option.map_none]
      have hzip : (parameters.map Prod.fst).zip (arguments.map convertV) =
          ((parameters.map Prod.fst).zip arguments).map
            (fun entry => (entry.1,convertV entry.2)) := by
        rw [List.zip_map_right]
        congr 1
      rw [hzip]
      rfl
    have htargetRaw : lookupCodeHOLExact (convertStateExact context source).code.lookup
        function (arguments.map convertV) =
        some (compileProgExact {context with locals := parameters} body,
          (fun key => (calleeLocals.lookup key).map convertV),
          compileShapeExact context.structs returnShape) := by
      rw [lookupCodeHOLExact,htargetCode]
      dsimp only
      rw [if_pos htargetGood]
      change some (compileProgExact {context with locals := parameters} sourceBody,
        FUPDATE_LIST_HOL FEMPTY ((compiledParameters.map Prod.fst).zip (arguments.map convertV)),
        compileShapeExact context.structs sourceReturn) = _
      rw [hfold,hraw.1,hraw.2.2]
    have hproject := PanSemStateFiniteExact.holFmapAsFiniteSupportHeterogeneousFunctionWitness_lookupCodeCanonicalHOL
      (convertStateExact context source).code function (arguments.map convertV)
    rw [htargetRaw] at hproject
    cases htargetLookup : PanSemStateFiniteExact.lookupCodeCanonicalHOL
        (convertStateExact context source).code function (arguments.map convertV) with
    | none => simp [htargetLookup] at hproject
    | some output =>
      rcases output with ⟨targetBody,targetLocals,targetReturn⟩
      simp only [htargetLookup,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hproject
      apply congrArg some
      apply Prod.ext hproject.1
      apply Prod.ext
      · apply HolFiniteMapExact.ext
        exact hproject.2.1
      · exact hproject.2.2
  · intro key value hv
    exact (hcalleeEvery key value hv).1
  · intro key value hv
    exact (hcalleeEvery key value hv).2
end Flapjack.Pancake.Proofs.PanStructs.LookupCodeFields
