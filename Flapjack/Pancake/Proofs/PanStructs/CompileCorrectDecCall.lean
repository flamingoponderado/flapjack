import Flapjack.Pancake.Proofs.PanStructs.MapRestoration
import Flapjack.Pancake.Semantics.PanProps.EvaluateResultInvariant
import Flapjack.Pancake.Proofs.PanStructs.EvaluateStructsCodeInvariant
import Flapjack.Pancake.Proofs.PanStructs.LookupCodeFields
import Flapjack.Pancake.Proofs.PanStructs.ConvertCodeLocals
import Flapjack.Pancake.Proofs.PanStructs.FlattenConversion
import Flapjack.Pancake.Proofs.PanStructs.CompileExpCorrectExact
import Flapjack.Pancake.Proofs.PanStructs.ValueShapeConversion
import Flapjack.Pancake.PanStructs.CompileProgExact
namespace Flapjack.Pancake.Proofs.PanStructs.CompileCorrectDecCall
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


/-- Lookup extensionality for proof plumbing; no independent HOL original. -/
private theorem mapExt {α β : Type} (a b : HolFiniteMapExact α β)
    (h : ∀ k, a.lookup k = b.lookup k) : a = b := by
  cases a with | mk al af =>
    cases b with | mk bl bf =>
      have he : al = bl := funext h
      subst bl
      rfl

/-- Map/update commutation for proof plumbing; no independent HOL original. -/
private theorem mapUpdate {α β γ : Type} [BEq α] [LawfulBEq α]
    (fm : HolFiniteMapExact α β) (f : α × β → γ) (k : α) (v : β) :
    (fm.update (k,v)).map2 f = (fm.map2 f).update (k,f (k,v)) := by
  apply mapExt
  intro key
  simp only [HolFiniteMapExact.lookup_map2, HolFiniteMapExact.lookup_update, FUPDATE]
  by_cases hk : k == key
  · have he := beq_iff_eq.mp hk
    subst key
    simp
  · simp [hk]

/-- Updated-map validity for proof plumbing; no independent HOL original. -/
private theorem everyUpdate {α β : Type} [BEq α] [LawfulBEq α]
    (fm : HolFiniteMapExact α β) (P : α × β → Bool) (k : α) (v : β)
    (h : feveryHOL P fm) (hv : P (k,v) = true) : feveryHOL P (fm.update (k,v)) := by
  intro key value he
  simp only [HolFiniteMapExact.lookup_update, FUPDATE] at he
  split at he
  next hk =>
    have heq := beq_iff_eq.mp hk
    subst key
    cases he
    exact hv
  next => exact h key value he


/-- Local context bindings are overwritten by every code entry's own params.
Flapjack proof plumbing; no independent HOL declaration. -/
private theorem convertStateLocalContext {width : Nat} {σ : Type} [NeZero width]
    (context : ContextExact) (locals : List (MlS × ShapeHOL))
    (state : PanSemStateFiniteExact width σ) :
    convertStateExact {context with locals := locals} state = convertStateExact context state := by
  rfl

/-- Equality decisions for the same key proposition are unique. Flapjack proof
plumbing; no extra comparison assumption and no independent HOL declaration. -/
private theorem resVarCanonical {α β : Type} (d : DecidableEq α)
    (fm : HolFiniteMapExact α β) (entry : α × Option β) :
    @HolFiniteMapExact.resVarEq α β d fm entry =
    @HolFiniteMapExact.resVarEq α β (Classical.typeDecidableEq α) fm entry := by
  have h : d = Classical.typeDecidableEq α := Subsingleton.elim _ _
  subst d
  rfl


/-- Full original program-correctness predicate used solely to spell the
two genuine guarded IHs; no extra predicate is supplied by the caller. -/
def DecCallProperty {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (program : ProgHOL width) : Prop :=
  ∀ (post : PanSemStateFiniteExact width σ) (context : ContextExact)
    (res : Option (PanSemResultExact width)),
    ( PanSemStateFiniteExact.evaluateHOLFiniteState source program = (res, post) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      res ≠ some .error) →
    PanSemStateFiniteExact.evaluateHOLFiniteState (convertStateExact context source)
      (compileProgExact context program) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true)

/-- Full original DecCall case: all ten premises/seven conclusions and exactly
its two original source-guarded recursive IHs. Full lookup correctness derives
actual compiled arguments/code and callee validity. The body IH plus source
invariants establishes continuation fields/WF/maps and return-shape guards.
Clock-zero timeout and all non-return outcomes use the faithful evaluator;
return installs the declared binding, runs the genuine continuation IH and
restores the old binding, including absent and shadowed names. No target run,
lookup, shape agreement, oracle or post-map premise is added. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectDecCall {width : Nat} {σ : Type} [NeZero width]
    (source post : PanSemStateFiniteExact width σ) (context : ContextExact)
    (name : MlS) (declaredShape : ShapeHOL) (function : MlS)
    (expressions : List (ExpHOL width)) (continuation : ProgHOL width)
    (res : Option (PanSemResultExact width))
    (ihContinuation : (∀ (args : List (ValueHOL width))
        (v2 : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (prog : ProgHOL width) (v7 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (return_sh : ShapeHOL)
        (eval_prog : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
        (v : Option (PanSemResultExact width)) (st : PanSemStateFiniteExact width σ)
        (v3 : PanSemResultExact width) (retv : ValueHOL width),
      source.evalListHOLFinite
          (h := fun address => Classical.propDecidable (source.memaddrs address))
          expressions = some args ∧
        PanSemStateFiniteExact.lookupCodeHOLFinite source.code.lookup function args = some v2 ∧
        v2 = (prog, v7) ∧ v7 = (newlocals, return_sh) ∧ source.clock ≠ 0 ∧
        eval_prog = PanSemStateFiniteExact.evaluateHOLFiniteState
          { source.decClockHOLFinite with locals := newlocals } prog ∧
        eval_prog = (v, st) ∧ v = some v3 ∧ v3 = .returned retv ∧
        shapeOfHOLExact retv = declaredShape ∧ shapeOfHOLExact retv = return_sh →
      DecCallProperty (PanSemStateFiniteExact.setVarHOLFinite name retv { st with locals := source.locals }) continuation))
    (ihBody : (∀ (args : List (ValueHOL width))
        (v2 : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (prog : ProgHOL width) (v7 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (return_sh : ShapeHOL),
      source.evalListHOLFinite
          (h := fun address => Classical.propDecidable (source.memaddrs address))
          expressions = some args ∧
        PanSemStateFiniteExact.lookupCodeHOLFinite source.code.lookup function args = some v2 ∧
        v2 = (prog, v7) ∧ v7 = (newlocals, return_sh) ∧ source.clock ≠ 0 →
      DecCallProperty { source.decClockHOLFinite with locals := newlocals } prog))
    (h : PanSemStateFiniteExact.evaluateHOLFiniteState source (.decCall name declaredShape function expressions continuation : ProgHOL width) = (res, post) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      res ≠ some .error) :
    PanSemStateFiniteExact.evaluateHOLFiniteState (convertStateExact context source)
      (compileProgExact context (.decCall name declaredShape function expressions continuation : ProgHOL width)) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true) := by
  classical
  rcases h with ⟨heval,hstructs,hlocal,hglobal,hwlocal,hwglobal,hinfo,hlocals,hglobals,herror⟩
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_decCall_fixClockRewrite] at heval
  cases ha : @PanSemStateFiniteExact.evalListHOLFinite width σ _ source
      (fun a => Classical.propDecidable (source.memaddrs a)) expressions with
  | none =>
    simp only [ha,Prod.mk.injEq] at heval
    exact False.elim (herror heval.1.symm)
  | some arguments =>
    rw [ha] at heval
    dsimp only at heval
    cases hl : PanSemStateFiniteExact.lookupCodeHOLFinite source.code.lookup function arguments with
    | none =>
      simp only [hl,Prod.mk.injEq] at heval
      exact False.elim (herror heval.1.symm)
    | some output =>
      rw [hl] at heval
      rcases output with ⟨body,callee,returnShape⟩
      dsimp only at heval
      have hlookup := LookupCodeFields.lookupCodeFields source context expressions arguments function body callee returnShape
        ⟨ha,hl,hlocals,hglobals,hstructs,hlocal,hglobal,hwlocal,hwglobal,hinfo⟩
      rcases hlookup.2.2.1 with ⟨parameters,htlookup,hparams⟩
      change PanSemStateFiniteExact.lookupCodeHOLFinite (convertStateExact context source).code.lookup
        function (arguments.map convertV) = some
          (compileProgExact {context with locals := parameters} body,
            callee.map2 (fun entry => convertV entry.2),compileShapeExact context.structs returnShape) at htlookup
      by_cases hc : source.clock = 0
      · rw [if_pos hc] at heval
        rcases Prod.mk.inj heval with ⟨hr,hp⟩
        subst res
        subst post
        refine ⟨?_,?_,hglobal,hglobals,?_,?_,?_⟩
        · rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_decCall_fixClockRewrite]
          rw [hlookup.1]
          dsimp only
          rw [htlookup]
          dsimp only
          have htclock : (convertStateExact context source).clock = 0 := hc
          rw [if_pos htclock]
          rfl
        · simp [PanSemStateFiniteExact.emptyLocalsHOLFinite,feveryHOL]
        · simp [isContResHOL]
        · simp [resVsHOL]
        · simp [resVsHOL]
      · rw [if_neg hc] at heval
        let entry := PanSemStateFiniteExact.callEntryStateHOLFinite source callee
        cases hb : PanSemStateFiniteExact.evaluateHOLFiniteState entry body with
        | mk bodyRes middle =>
          rw [hb] at heval
          dsimp only at heval
          have hbodyNoError : bodyRes ≠ some .error := by
            intro he
            rw [he] at heval
            dsimp only at heval
            exact herror (Prod.mk.inj heval).1.symm
          have hbodyIH := ihBody arguments (body,callee,returnShape) body (callee,returnShape)
            callee returnShape ⟨ha,hl,rfl,rfl,hc⟩
          have hbody := hbodyIH middle {context with locals := parameters} bodyRes
            ⟨hb,hstructs,hlookup.2.2.2.1,hglobal,hlookup.2.2.2.2,hwglobal,hinfo,hparams,hglobals,hbodyNoError⟩
          have hpres := EvaluateStructsCodeInvariant.evaluateStructsCodeInv body entry middle bodyRes hb
          have hstruct : middle.structs = source.structs := hpres.1
          have hentryConv : convertStateExact {context with locals := parameters} entry =
              PanSemStateFiniteExact.callEntryStateHOLFinite (convertStateExact context source)
                (callee.map2 (fun entry => convertV entry.2)) := by
            rfl
          have hmiddleConv : convertStateExact {context with locals := parameters} middle =
              convertStateExact context middle := by rfl
          have hbodyRun : PanSemStateFiniteExact.evaluateHOLFiniteState
              (PanSemStateFiniteExact.callEntryStateHOLFinite (convertStateExact context source)
                (callee.map2 (fun entry => convertV entry.2)))
              (compileProgExact {context with locals := parameters} body) =
              (convertResHOL bodyRes,convertStateExact context middle) := by
            have he : PanSemStateFiniteExact.evaluateHOLFiniteState
                (convertStateExact {context with locals := parameters} entry)
                (compileProgExact {context with locals := parameters} body) =
                (convertResHOL bodyRes,convertStateExact {context with locals := parameters} middle) := hbody.1
            rw [hentryConv,hmiddleConv] at he
            exact he
          cases bodyRes with
          | none =>
            exact False.elim (herror (Prod.mk.inj heval).1.symm)
          | some result =>
            cases result with
            | error => exact False.elim (hbodyNoError rfl)
            | «break» => exact False.elim (herror (Prod.mk.inj heval).1.symm)
            | «continue» => exact False.elim (herror (Prod.mk.inj heval).1.symm)
            | returned value =>
              dsimp only at heval
              split at heval
              next hguard =>
                have hshapes : shapeEqHOL (shapeOfHOLExact value) declaredShape = true ∧
                    shapeEqHOL (shapeOfHOLExact value) returnShape = true := by
                  simpa only [Bool.and_eq_true] using hguard
                have hsdecl := (shapeEqHOL_eq_true _ _).mp hshapes.1
                have hsreturn := (shapeEqHOL_eq_true _ _).mp hshapes.2
                let contState := PanSemStateFiniteExact.setVarHOLFinite name value {middle with locals := source.locals}
                let upd : ContextExact := {context with locals := (name,declaredShape)::context.locals}
                have hvalueFields := hbody.2.2.2.2.2.1 value (by simp [resVsHOL])
                have hvalueWf := hbody.2.2.2.2.2.2 value (by simp [resVsHOL])
                have hprops : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
                    (PanPropsEvalStateFiniteExact.ofPanSemFinite entry) body =
                    (some (.returned value),PanPropsEvalStateFiniteExact.ofPanSemFinite middle) := by
                  simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using
                    congrArg (fun pair => (pair.1,PanPropsEvalStateFiniteExact.ofPanSemFinite pair.2)) hb
                have hwf := evaluateIsWfShapeInvariantFiniteExact body
                  (PanPropsEvalStateFiniteExact.ofPanSemFinite entry) (some (.returned value))
                  (PanPropsEvalStateFiniteExact.ofPanSemFinite middle) hprops hlookup.2.2.2.2 hwglobal
                have hfields : feveryHOL (fun entry => valueFldsOkHOLExact contState.structs entry.2) contState.locals := by
                  change feveryHOL (fun entry => valueFldsOkHOLExact middle.structs entry.2)
                    (source.locals.update (name,value))
                  apply everyUpdate
                  · simpa only [hstruct] using hlocal
                  · exact hvalueFields
                have hlocalWf : feveryHOL (fun entry => isWfShapeValueHOLExact contState.structs entry.2) contState.locals := by
                  change feveryHOL (fun entry => isWfShapeValueHOLExact middle.structs entry.2)
                    (source.locals.update (name,value))
                  apply everyUpdate
                  · simpa only [hstruct] using hwlocal
                  · exact hvalueWf
                have hmaps : shapeMap upd.locals = contState.locals.map2 (fun entry => shapeOfHOLExact entry.2) := by
                  change (shapeMap context.locals).update (name,declaredShape) =
                    (source.locals.update (name,value)).map2 (fun entry => shapeOfHOLExact entry.2)
                  rw [mapUpdate,hlocals,hsdecl]
                have hcontIH := ihContinuation arguments (body,callee,returnShape) body (callee,returnShape)
                  callee returnShape (some (.returned value),middle) (some (.returned value)) middle
                  (.returned value) value ⟨ha,hl,rfl,rfl,hc,hb.symm,rfl,rfl,rfl,hsdecl,hsreturn⟩
                cases hcontEval : PanSemStateFiniteExact.evaluateHOLFiniteState contState continuation with
                | mk contRes last =>
                  rw [hcontEval] at heval
                  dsimp only at heval
                  have hcontNoError : contRes ≠ some .error := by
                    intro he
                    rw [he] at heval
                    exact herror (Prod.mk.inj heval).1.symm
                  have hcont := hcontIH last upd contRes
                    ⟨hcontEval,by
                        change context.structs = middle.structs.map (fun entry => (entry.1,entry.2.fields))
                        rw [hstruct]
                        exact hstructs,
                      hfields,hbody.2.2.1,
                      hlocalWf,hwf.2.1,by
                        change structInfosOkHOLExact middle.structs
                        rw [hstruct]
                        exact hinfo,
                      hmaps,hbody.2.2.2.1,hcontNoError⟩
                  have hcontPres := EvaluateStructsCodeInvariant.evaluateStructsCodeInv
                    continuation contState last contRes hcontEval
                  have hlastStruct : last.structs = source.structs := hcontPres.1.trans hstruct
                  rcases Prod.mk.inj heval with ⟨hr,hp⟩
                  subst res
                  subst post
                  have hvalueSourceFields : valueFldsOkHOLExact source.structs value = true := by
                    simpa only [hstruct] using hvalueFields
                  have hvalueSourceWf : isWfShapeValueHOLExact source.structs value = true := by
                    simpa only [hstruct] using hvalueWf
                  have hconverted := ValueShapeConversion.shapeOfConvertVRev source.structs value
                    ⟨hvalueSourceFields,hvalueSourceWf,hinfo⟩
                  refine ⟨?_,?_,hcont.2.2.1,hcont.2.2.2.1,?_,hcont.2.2.2.2.2.1,hcont.2.2.2.2.2.2⟩
                  · rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_decCall_fixClockRewrite]
                    rw [hlookup.1]
                    dsimp only
                    rw [htlookup]
                    dsimp only
                    have htclock : (convertStateExact context source).clock ≠ 0 := hc
                    rw [if_neg htclock,hbodyRun]
                    simp only [convertResHOL]
                    have htd : shapeEqHOL (shapeOfHOLExact (convertV value))
                        (compileShapeExact context.structs declaredShape) = true := by
                      apply (shapeEqHOL_eq_true _ _).mpr
                      rw [hconverted,← hstructs,hsdecl]
                    have htr : shapeEqHOL (shapeOfHOLExact (convertV value))
                        (compileShapeExact context.structs returnShape) = true := by
                      apply (shapeEqHOL_eq_true _ _).mpr
                      rw [hconverted,← hstructs,hsreturn]
                    rw [htd,htr]
                    simp only [Bool.true_and,ite_true]
                    have hstate : PanSemStateFiniteExact.setVarHOLFinite name (convertV value)
                        {convertStateExact context middle with locals := (convertStateExact context source).locals} =
                        convertStateExact upd contState := by
                      rw [show upd = {context with locals := (name,declaredShape)::context.locals} from rfl,
                        convertStateLocalContext]
                      simp only [contState,PanSemStateFiniteExact.setVarHOLFinite,convertStateExact]
                      congr 1
                      exact (mapUpdate source.locals (fun entry => convertV entry.2) name value).symm
                    have hrun : PanSemStateFiniteExact.evaluateHOLFiniteState
                        (convertStateExact upd contState)
                        (compileProgExact {context with locals := (name,declaredShape)::context.locals} continuation) =
                        (convertResHOL contRes,convertStateExact upd last) := hcont.1
                    rw [hstate,hrun]
                    dsimp only
                    simp only [show upd = {context with locals := (name,declaredShape)::context.locals} from rfl,
                      convertStateExact,HolFiniteMapExact.lookup_map2,resVarCanonical]
                    congr 1
                    congr 1
                    exact (MapRestoration.resVarFmapMap2Rev last.locals
                      (fun entry => convertV entry.2) name (source.locals.lookup name)).symm
                  · dsimp only
                    simp only [resVarCanonical]
                    apply (MapRestoration.feveryResVar last.locals
                      (fun entry => valueFldsOkHOLExact last.structs entry.2) name
                      (source.locals.lookup name)).mpr
                    constructor
                    · intro key val he
                      rw [MapRestoration.restrictExceptLookup] at he
                      by_cases hk : key=name
                      · simp [hk] at he
                      · apply hcont.2.1 key val
                        simpa [hk] using he
                    · intro val he
                      simpa only [hlastStruct] using hlocal name val he
                  · intro hc
                    have hcontmap := hcont.2.2.2.2.1 hc
                    dsimp only
                    simp only [resVarCanonical]
                    rw [MapRestoration.resVarFmapMap2Rev]
                    apply mapExt
                    intro key
                    by_cases hk : key=name
                    · subst key
                      simp only [HolFiniteMapExact.resVarEq]
                      cases ho : source.locals.lookup name with
                      | none =>
                        simp only [Option.map_none, HolFiniteMapExact.eraseEq, FDOMSUB_HOL, ite_true]
                        simpa only [HolFiniteMapExact.lookup_map2, ho, Option.map_none] using
                          congrArg (fun m => m.lookup name) hlocals
                      | some old =>
                        simp only [Option.map_some, HolFiniteMapExact.updateEq, FUPDATE_HOL, ite_true]
                        simpa only [HolFiniteMapExact.lookup_map2, ho, Option.map_some] using
                          congrArg (fun m => m.lookup name) hlocals
                    · have hright :
                          (@HolFiniteMapExact.resVarEq MlS ShapeHOL (Classical.typeDecidableEq MlS)
                            (last.locals.map2 (fun entry => shapeOfHOLExact entry.2))
                            (name,(source.locals.lookup name).map (fun y => shapeOfHOLExact y))).lookup key =
                          (last.locals.map2 (fun entry => shapeOfHOLExact entry.2)).lookup key := by
                        cases source.locals.lookup name <;>
                          simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.eraseEq,
                            HolFiniteMapExact.updateEq, FDOMSUB_HOL, FUPDATE_HOL, hk]
                      rw [hright, ← hcontmap]
                      simp only [upd, shapeMap, List.foldr_cons, HolFiniteMapExact.lookup_update, FUPDATE]
                      have hne : ¬(name == key) := by
                        intro he
                        exact hk (beq_iff_eq.mp he).symm
                      simp [hne]
              next => exact False.elim (herror (Prod.mk.inj heval).1.symm)
            | timeOut =>
              rcases Prod.mk.inj heval with ⟨hr,hp⟩
              subst res
              subst post
              refine ⟨?_,?_,hbody.2.2.1,hbody.2.2.2.1,?_,?_,?_⟩
              · rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_decCall_fixClockRewrite]
                rw [hlookup.1]
                dsimp only
                rw [htlookup]
                dsimp only
                have htclock : (convertStateExact context source).clock ≠ 0 := hc
                rw [if_neg htclock,hbodyRun]
                rfl
              · simp [PanSemStateFiniteExact.emptyLocalsHOLFinite,feveryHOL]
              · simp [isContResHOL]
              · simp [resVsHOL]
              · simp [resVsHOL]
            | exception eid value =>
              rcases Prod.mk.inj heval with ⟨hr,hp⟩
              subst res
              subst post
              refine ⟨?_,?_,hbody.2.2.1,hbody.2.2.2.1,?_,?_,?_⟩
              · rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_decCall_fixClockRewrite]
                rw [hlookup.1]
                dsimp only
                rw [htlookup]
                dsimp only
                have htclock : (convertStateExact context source).clock ≠ 0 := hc
                rw [if_neg htclock,hbodyRun]
                rfl
              · simp [PanSemStateFiniteExact.emptyLocalsHOLFinite,feveryHOL]
              · simp [isContResHOL]
              · exact hbody.2.2.2.2.2.1
              · exact hbody.2.2.2.2.2.2
            | finalFfi event =>
              rcases Prod.mk.inj heval with ⟨hr,hp⟩
              subst res
              subst post
              refine ⟨?_,?_,hbody.2.2.1,hbody.2.2.2.1,?_,?_,?_⟩
              · rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_decCall_fixClockRewrite]
                rw [hlookup.1]
                dsimp only
                rw [htlookup]
                dsimp only
                have htclock : (convertStateExact context source).clock ≠ 0 := hc
                rw [if_neg htclock,hbodyRun]
                rfl
              · simp [PanSemStateFiniteExact.emptyLocalsHOLFinite,feveryHOL]
              · simp [isContResHOL]
              · simp [resVsHOL]
              · simp [resVsHOL]

end Flapjack.Pancake.Proofs.PanStructs.CompileCorrectDecCall
