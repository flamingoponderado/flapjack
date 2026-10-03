import Flapjack.Pancake.Proofs.PanStructs.FupdateElim2
import Flapjack.Pancake.Semantics.PanProps.EvaluateResultInvariant
import Flapjack.Pancake.Proofs.PanStructs.EvaluateStructsCodeInvariant
import Flapjack.Pancake.Proofs.PanStructs.LookupCodeFields
import Flapjack.Pancake.Proofs.PanStructs.ConvertCodeLocals
import Flapjack.Pancake.Proofs.PanStructs.FlattenConversion
import Flapjack.Pancake.Proofs.PanStructs.CompileExpCorrectExact
import Flapjack.Pancake.Proofs.PanStructs.ValueShapeConversion
import Flapjack.Pancake.PanStructs.CompileProgExact
namespace Flapjack.Pancake.Proofs.PanStructs.CompileCorrectCall
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

/-- Existing-binding neutrality for the executed update; no independent HOL original. -/
private theorem updateNeutral {α β : Type} [BEq α] [LawfulBEq α]
    (fm : HolFiniteMapExact α β) (k : α) (v : β) (h : fm.lookup k = some v) :
    fm.update (k,v) = fm := by
  classical
  have he : fm.update (k,v) = fm.updateEq (k,v) := by
    apply mapExt
    intro key
    simp only [HolFiniteMapExact.lookup_update, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_HOL_eq_FUPDATE]
  rw [he]
  exact FupdateElim2.fupdateElim2 fm k v h

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


/-- Full original program-correctness predicate used solely to spell the
two genuine guarded IHs; no extra predicate is supplied by the caller. -/
def CallProperty {width : Nat} {σ : Type} [NeZero width]
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

/-- Full original Call case: ten premises/seven conclusions and exactly the
original body and exception-handler guarded IHs. Full lookup correctness gives
actual compiled arguments/code and callee validity; body correctness and source
invariants derive return/handler fields, WF, maps and comparisons. Tail return,
discarded return, local/global binding, exception propagation, handler execution,
clock-zero timeout and other terminal outcomes use the faithful evaluator.
No target lookup/run, oracle, shape-agreement or post-map premise is added. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectCall {width : Nat} {σ : Type} [NeZero width]
    (source post : PanSemStateFiniteExact width σ) (context : ContextExact)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (expressions : List (ExpHOL width))
    (res : Option (PanSemResultExact width))
    (ihHandler : (∀ (args : List (ValueHOL width))
        (v7 : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (prog : ProgHOL width) (v12 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (return_sh : ShapeHOL)
        (eval_prog : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
        (v4 : Option (PanSemResultExact width)) (st : PanSemStateFiniteExact width σ)
        (v8 : PanSemResultExact width) (eid : MlS) (exn : ValueHOL width)
        (v : Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width))
        (v1 : Option (VarKind × MlS)) (v2 : Option (MlS × MlS × ProgHOL width))
        (v3 : MlS × MlS × ProgHOL width) (eid' : MlS) (v5 : MlS × ProgHOL width)
        (evar : MlS) (p : ProgHOL width) (sh : ShapeHOL),
      source.evalListHOLFinite
          (h := fun address => Classical.propDecidable (source.memaddrs address))
          expressions = some args ∧
        PanSemStateFiniteExact.lookupCodeHOLFinite source.code.lookup function args = some v7 ∧
        v7 = (prog, v12) ∧ v12 = (newlocals, return_sh) ∧ source.clock ≠ 0 ∧
        eval_prog = PanSemStateFiniteExact.evaluateHOLFiniteState
          { source.decClockHOLFinite with locals := newlocals } prog ∧
        eval_prog = (v4, st) ∧ v4 = some v8 ∧ v8 = .exception eid exn ∧
        info = some v ∧ v = (v1, v2) ∧ v2 = some v3 ∧ v3 = (eid', v5) ∧
        v5 = (evar, p) ∧ eid = eid' ∧ source.eshapes.lookup eid = some sh ∧
        shapeOfHOLExact exn = sh ∧ isValidValueHOLExact source.toExact .local evar exn = true →
      CallProperty (PanSemStateFiniteExact.setVarHOLFinite evar exn { st with locals := source.locals }) p))
    (ihBody : (∀ (args : List (ValueHOL width))
        (v7 : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (prog : ProgHOL width) (v12 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
        (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (return_sh : ShapeHOL),
      source.evalListHOLFinite
          (h := fun address => Classical.propDecidable (source.memaddrs address))
          expressions = some args ∧
        PanSemStateFiniteExact.lookupCodeHOLFinite source.code.lookup function args = some v7 ∧
        v7 = (prog, v12) ∧ v12 = (newlocals, return_sh) ∧ source.clock ≠ 0 →
      CallProperty { source.decClockHOLFinite with locals := newlocals } prog))
    (h : PanSemStateFiniteExact.evaluateHOLFiniteState source (.call info function expressions : ProgHOL width) = (res, post) ∧
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
      (compileProgExact context (.call info function expressions : ProgHOL width)) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true) := by
  classical
  rcases h with ⟨heval,hstructs,hlocal,hglobal,hwlocal,hwglobal,hinfo,hlocals,hglobals,herror⟩
  rw [Flapjack.evaluateHOLFiniteState_call] at heval
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
      have hcompile : compileProgExact context (.call info function expressions) =
            .call (info.map (fun pair => (pair.1,pair.2.map (fun handler =>
              (handler.1,handler.2.1,compileProgExact context handler.2.2))))) function
              (compileExpsExact context expressions) := by
          cases info with
          | none => simp only [compileProgExact,Option.map_none]
          | some callInfo =>
            rcases callInfo with ⟨target,handler⟩
            cases handler with
            | none => simp only [compileProgExact,Option.map_none,Option.map_some]
            | some handler =>
              rcases handler with ⟨hid,hvar,hprogram⟩
              simp only [compileProgExact,Option.map_some]
      by_cases hc : source.clock = 0
      · rw [if_pos hc] at heval
        rcases Prod.mk.inj heval with ⟨hr,hp⟩
        subst res
        subst post
        refine ⟨?_,?_,hglobal,hglobals,?_,?_,?_⟩
        · rw [hcompile,Flapjack.evaluateHOLFiniteState_call]
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
                have hsreturn := (shapeEqHOL_eq_true _ _).mp hguard
                have hvalueFields := hbody.2.2.2.2.2.1 value (by simp [resVsHOL])
                have hvalueWf := hbody.2.2.2.2.2.2 value (by simp [resVsHOL])
                have hconverted := ValueShapeConversion.shapeOfConvertVRev source.structs value
                  ⟨by simpa only [hstruct] using hvalueFields,
                    by simpa only [hstruct] using hvalueWf,hinfo⟩
                have htr : shapeEqHOL (shapeOfHOLExact (convertV value))
                    (compileShapeExact context.structs returnShape) = true := by
                  apply (shapeEqHOL_eq_true _ _).mpr
                  rw [hconverted,← hstructs,hsreturn]
                cases info with
                | none =>
                  rcases Prod.mk.inj heval with ⟨hr,hp⟩
                  subst res
                  subst post
                  refine ⟨?_,?_,hbody.2.2.1,hbody.2.2.2.1,?_,hbody.2.2.2.2.2.1,hbody.2.2.2.2.2.2⟩
                  · rw [hcompile,Flapjack.evaluateHOLFiniteState_call]
                    rw [hlookup.1]
                    dsimp only
                    rw [htlookup]
                    dsimp only
                    have htclock : (convertStateExact context source).clock ≠ 0 := hc
                    rw [if_neg htclock,hbodyRun]
                    simp only [convertResHOL]
                    rw [htr]
                    rfl
                  · simp [PanSemStateFiniteExact.emptyLocalsHOLFinite,feveryHOL]
                  · simp [isContResHOL]
                | some callInfo =>
                  rcases callInfo with ⟨target,handler⟩
                  cases target with
                  | none =>
                    rcases Prod.mk.inj heval with ⟨hr,hp⟩
                    subst res
                    subst post
                    refine ⟨?_,?_,hbody.2.2.1,hbody.2.2.2.1,?_,?_,?_⟩
                    · rw [hcompile,Flapjack.evaluateHOLFiniteState_call]
                      rw [hlookup.1]
                      dsimp only
                      rw [htlookup]
                      dsimp only
                      have htclock : (convertStateExact context source).clock ≠ 0 := hc
                      rw [if_neg htclock,hbodyRun]
                      simp only [convertResHOL]
                      rw [htr]
                      rfl
                    · simpa only [hstruct] using hlocal
                    · intro _
                      exact hlocals
                    · simp [resVsHOL]
                    · simp [resVsHOL]
                  | some target =>
                    rcases target with ⟨kind,name⟩
                    dsimp only at heval
                    split at heval
                    next hvalid =>
                      change PanSemStateFiniteExact.isValidValueHOLFinite source kind name value = true at hvalid
                      cases kind with
                      | «local» =>
                        simp only [PanSemStateFiniteExact.isValidValueHOLFinite,
                          PanSemStateFiniteExact.lookupKvarHOLFinite] at hvalid
                        cases ho : source.locals.lookup name with
                        | none => simp [ho] at hvalid
                        | some old =>
                          simp only [ho] at hvalid
                          have hs := (shapeEqHOL_eq_true _ _).mp hvalid
                          have holdshape := ValueShapeConversion.shapeOfConvertVRev source.structs old
                            ⟨hlocal name old ho,hwlocal name old ho,hinfo⟩
                          have htvalid : isValidValueHOLExact (convertStateExact context source).toExact
                              .«local» name (convertV value) = true := by
                            change PanSemStateFiniteExact.isValidValueHOLFinite (convertStateExact context source)
                              .«local» name (convertV value) = true
                            simp only [PanSemStateFiniteExact.isValidValueHOLFinite,
                              PanSemStateFiniteExact.lookupKvarHOLFinite,convertStateExact,
                              HolFiniteMapExact.lookup_map2,ho,Option.map_some]
                            apply (shapeEqHOL_eq_true _ _).mpr
                            rw [hconverted,holdshape,hs]
                          have hmaps : (source.locals.update (name,value)).map2 (fun entry => shapeOfHOLExact entry.2) =
                              source.locals.map2 (fun entry => shapeOfHOLExact entry.2) := by
                            rw [mapUpdate]
                            apply updateNeutral
                            simp only [HolFiniteMapExact.lookup_map2,ho,Option.map_some]
                            exact congrArg some hs.symm
                          rcases Prod.mk.inj heval with ⟨hr,hp⟩
                          subst res
                          subst post
                          refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
                          · rw [hcompile,Flapjack.evaluateHOLFiniteState_call]
                            rw [hlookup.1]
                            dsimp only
                            rw [htlookup]
                            dsimp only
                            have htclock : (convertStateExact context source).clock ≠ 0 := hc
                            rw [if_neg htclock,hbodyRun]
                            simp only [convertResHOL]
                            rw [htr]
                            simp only [ite_true,Option.map_some]
                            rw [htvalid]
                            simp only [ite_true,PanSemStateFiniteExact.setKvarHOLFinite,
                              PanSemStateFiniteExact.setVarHOLFinite,convertStateExact]
                            congr 1
                            congr 1
                            exact (mapUpdate source.locals (fun entry => convertV entry.2) name value).symm
                          · change feveryHOL (fun entry => valueFldsOkHOLExact middle.structs entry.2) (source.locals.update (name,value))
                            apply everyUpdate
                            · simpa only [hstruct] using hlocal
                            · exact hvalueFields
                          · exact hbody.2.2.1
                          · exact hbody.2.2.2.1
                          · intro _
                            change shapeMap context.locals = (source.locals.update (name,value)).map2 (fun entry => shapeOfHOLExact entry.2)
                            rw [hmaps]
                            exact hlocals
                          · simp [resVsHOL]
                          · simp [resVsHOL]
                      | global =>
                        simp only [PanSemStateFiniteExact.isValidValueHOLFinite,
                          PanSemStateFiniteExact.lookupKvarHOLFinite] at hvalid
                        cases ho : source.globals.lookup name with
                        | none => simp [ho] at hvalid
                        | some old =>
                          simp only [ho] at hvalid
                          have hs := (shapeEqHOL_eq_true _ _).mp hvalid
                          have holdshape := ValueShapeConversion.shapeOfConvertVRev source.structs old
                            ⟨hglobal name old ho,hwglobal name old ho,hinfo⟩
                          have htvalid : isValidValueHOLExact (convertStateExact context source).toExact
                              .global name (convertV value) = true := by
                            change PanSemStateFiniteExact.isValidValueHOLFinite (convertStateExact context source)
                              .global name (convertV value) = true
                            simp only [PanSemStateFiniteExact.isValidValueHOLFinite,
                              PanSemStateFiniteExact.lookupKvarHOLFinite,convertStateExact,
                              HolFiniteMapExact.lookup_map2,ho,Option.map_some]
                            apply (shapeEqHOL_eq_true _ _).mpr
                            rw [hconverted,holdshape,hs]
                          have hmaps : (middle.globals.update (name,value)).map2 (fun entry => shapeOfHOLExact entry.2) =
                              middle.globals.map2 (fun entry => shapeOfHOLExact entry.2) := by
                            rw [mapUpdate]
                            apply updateNeutral
                            rw [← hbody.2.2.2.1,hglobals]
                            simp only [HolFiniteMapExact.lookup_map2,ho,Option.map_some]
                            exact congrArg some hs.symm
                          rcases Prod.mk.inj heval with ⟨hr,hp⟩
                          subst res
                          subst post
                          refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
                          · rw [hcompile,Flapjack.evaluateHOLFiniteState_call]
                            rw [hlookup.1]
                            dsimp only
                            rw [htlookup]
                            dsimp only
                            have htclock : (convertStateExact context source).clock ≠ 0 := hc
                            rw [if_neg htclock,hbodyRun]
                            simp only [convertResHOL]
                            rw [htr]
                            simp only [ite_true,Option.map_some]
                            rw [htvalid]
                            simp only [ite_true,PanSemStateFiniteExact.setKvarHOLFinite,
                              PanSemStateFiniteExact.setGlobalHOLFinite,convertStateExact]
                            congr 1
                            congr 1
                            exact (mapUpdate middle.globals (fun entry => convertV entry.2) name value).symm
                          · change feveryHOL (fun entry => valueFldsOkHOLExact middle.structs entry.2) source.locals
                            rw [hstruct]
                            exact hlocal
                          · change feveryHOL (fun entry => valueFldsOkHOLExact middle.structs entry.2) (middle.globals.update (name,value))
                            exact everyUpdate middle.globals (fun entry => valueFldsOkHOLExact middle.structs entry.2) name value hbody.2.2.1 hvalueFields
                          · change shapeMap context.globals = (middle.globals.update (name,value)).map2 (fun entry => shapeOfHOLExact entry.2)
                            rw [hmaps]
                            exact hbody.2.2.2.1
                          · intro _
                            exact hlocals
                          · simp [resVsHOL]
                          · simp [resVsHOL]
                    next => exact False.elim (herror (Prod.mk.inj heval).1.symm)
              next => exact False.elim (herror (Prod.mk.inj heval).1.symm)
            | timeOut =>
              rcases Prod.mk.inj heval with ⟨hr,hp⟩
              subst res
              subst post
              refine ⟨?_,?_,hbody.2.2.1,hbody.2.2.2.1,?_,?_,?_⟩
              · rw [hcompile,Flapjack.evaluateHOLFiniteState_call]
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
              dsimp only at heval
              cases info with
              | none =>
                rcases Prod.mk.inj heval with ⟨hr,hp⟩
                subst res
                subst post
                refine ⟨?_,?_,hbody.2.2.1,hbody.2.2.2.1,?_,hbody.2.2.2.2.2.1,hbody.2.2.2.2.2.2⟩
                · rw [hcompile,Flapjack.evaluateHOLFiniteState_call]
                  rw [hlookup.1]
                  dsimp only
                  rw [htlookup]
                  dsimp only
                  have htclock : (convertStateExact context source).clock ≠ 0 := hc
                  rw [if_neg htclock,hbodyRun]
                  simp only [convertResHOL,Option.map_none]
                  rfl
                · simp [PanSemStateFiniteExact.emptyLocalsHOLFinite,feveryHOL]
                · simp [isContResHOL]
              | some callInfo =>
                rcases callInfo with ⟨target,handler⟩
                cases handler with
                | none =>
                  rcases Prod.mk.inj heval with ⟨hr,hp⟩
                  subst res
                  subst post
                  refine ⟨?_,?_,hbody.2.2.1,hbody.2.2.2.1,?_,hbody.2.2.2.2.2.1,hbody.2.2.2.2.2.2⟩
                  · rw [hcompile,Flapjack.evaluateHOLFiniteState_call]
                    rw [hlookup.1]
                    dsimp only
                    rw [htlookup]
                    dsimp only
                    have htclock : (convertStateExact context source).clock ≠ 0 := hc
                    rw [if_neg htclock,hbodyRun]
                    simp only [convertResHOL,Option.map_none,Option.map_some]
                    rfl
                  · simp [PanSemStateFiniteExact.emptyLocalsHOLFinite,feveryHOL]
                  · simp [isContResHOL]
                | some handler =>
                  rcases handler with ⟨handlerId,handlerVar,handlerProgram⟩
                  dsimp only at heval
                  by_cases hid : eid = handlerId
                  · rw [if_pos hid] at heval
                    cases hesh : source.eshapes.lookup eid with
                    | none =>
                      simp only [hesh,Prod.mk.injEq] at heval
                      exact False.elim (herror heval.1.symm)
                    | some shape =>
                      rw [hesh] at heval
                      dsimp only at heval
                      split at heval
                      next hguard =>
                        have hparts : shapeEqHOL (shapeOfHOLExact value) shape = true ∧
                            isValidValueHOLExact source.toExact .local handlerVar value = true := by
                          simpa only [Bool.and_eq_true] using hguard
                        have hshape := (shapeEqHOL_eq_true _ _).mp hparts.1
                        have hvalid := hparts.2
                        change PanSemStateFiniteExact.isValidValueHOLFinite source .local handlerVar value = true at hvalid
                        simp only [PanSemStateFiniteExact.isValidValueHOLFinite,
                          PanSemStateFiniteExact.lookupKvarHOLFinite] at hvalid
                        cases ho : source.locals.lookup handlerVar with
                        | none => simp [ho] at hvalid
                        | some old =>
                          simp only [ho] at hvalid
                          have hs := (shapeEqHOL_eq_true _ _).mp hvalid
                          have hvalueFields := hbody.2.2.2.2.2.1 value (by simp [resVsHOL])
                          have hvalueWf := hbody.2.2.2.2.2.2 value (by simp [resVsHOL])
                          let handlerState := PanSemStateFiniteExact.setVarHOLFinite handlerVar value
                            {middle with locals := source.locals}
                          have hprops : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
                              (PanPropsEvalStateFiniteExact.ofPanSemFinite entry) body =
                              (some (.exception eid value),PanPropsEvalStateFiniteExact.ofPanSemFinite middle) := by
                            simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using
                              congrArg (fun pair => (pair.1,PanPropsEvalStateFiniteExact.ofPanSemFinite pair.2)) hb
                          have hwf := evaluateIsWfShapeInvariantFiniteExact body
                            (PanPropsEvalStateFiniteExact.ofPanSemFinite entry) (some (.exception eid value))
                            (PanPropsEvalStateFiniteExact.ofPanSemFinite middle) hprops hlookup.2.2.2.2 hwglobal
                          have hfields : feveryHOL (fun entry => valueFldsOkHOLExact handlerState.structs entry.2) handlerState.locals := by
                            change feveryHOL (fun entry => valueFldsOkHOLExact middle.structs entry.2)
                              (source.locals.update (handlerVar,value))
                            apply everyUpdate
                            · simpa only [hstruct] using hlocal
                            · exact hvalueFields
                          have hlocalWf : feveryHOL (fun entry => isWfShapeValueHOLExact handlerState.structs entry.2) handlerState.locals := by
                            change feveryHOL (fun entry => isWfShapeValueHOLExact middle.structs entry.2)
                              (source.locals.update (handlerVar,value))
                            apply everyUpdate
                            · simpa only [hstruct] using hwlocal
                            · exact hvalueWf
                          have hmaps : (source.locals.update (handlerVar,value)).map2 (fun entry => shapeOfHOLExact entry.2) =
                              source.locals.map2 (fun entry => shapeOfHOLExact entry.2) := by
                            rw [mapUpdate]
                            apply updateNeutral
                            simp only [HolFiniteMapExact.lookup_map2,ho,Option.map_some]
                            exact congrArg some hs.symm
                          have hhandlerIH := ihHandler arguments (body,callee,returnShape) body (callee,returnShape)
                            callee returnShape (some (.exception eid value),middle) (some (.exception eid value)) middle
                            (.exception eid value) eid value (target,some (handlerId,handlerVar,handlerProgram)) target
                            (some (handlerId,handlerVar,handlerProgram)) (handlerId,handlerVar,handlerProgram)
                            handlerId (handlerVar,handlerProgram) handlerVar handlerProgram shape
                            ⟨ha,hl,rfl,rfl,hc,hb.symm,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hid,hesh,hshape,hparts.2⟩
                          have hhandler := hhandlerIH post context res
                            ⟨heval,by
                                change context.structs = middle.structs.map (fun entry => (entry.1,entry.2.fields))
                                rw [hstruct]
                                exact hstructs,
                              hfields,hbody.2.2.1,hlocalWf,hwf.2.1,by
                                change structInfosOkHOLExact middle.structs
                                rw [hstruct]
                                exact hinfo,
                              by
                                change shapeMap context.locals = (source.locals.update (handlerVar,value)).map2 (fun entry => shapeOfHOLExact entry.2)
                                rw [hmaps]
                                exact hlocals,
                              hbody.2.2.2.1,herror⟩
                          refine ⟨?_,hhandler.2⟩
                          have hconverted := ValueShapeConversion.shapeOfConvertVRev source.structs value
                            ⟨by simpa only [hstruct] using hvalueFields,
                              by simpa only [hstruct] using hvalueWf,hinfo⟩
                          have holdshape := ValueShapeConversion.shapeOfConvertVRev source.structs old
                            ⟨hlocal handlerVar old ho,hwlocal handlerVar old ho,hinfo⟩
                          have htvalid : isValidValueHOLExact (convertStateExact context source).toExact
                              .local handlerVar (convertV value) = true := by
                            change PanSemStateFiniteExact.isValidValueHOLFinite (convertStateExact context source)
                              .local handlerVar (convertV value) = true
                            simp only [PanSemStateFiniteExact.isValidValueHOLFinite,
                              PanSemStateFiniteExact.lookupKvarHOLFinite,convertStateExact,
                              HolFiniteMapExact.lookup_map2,ho,Option.map_some]
                            apply (shapeEqHOL_eq_true _ _).mpr
                            rw [hconverted,holdshape,hs]
                          have htshape : shapeEqHOL (shapeOfHOLExact (convertV value))
                              (compileShapeExact context.structs shape) = true := by
                            apply (shapeEqHOL_eq_true _ _).mpr
                            rw [hconverted,← hstructs,hshape]
                          have htesh : (convertStateExact context source).eshapes.lookup eid =
                              some (compileShapeExact context.structs shape) := by
                            simp only [convertStateExact,convertEshapesExact,HolFiniteMapExact.lookup_map2,
                              hesh,Option.map_some]
                          rw [hcompile,Flapjack.evaluateHOLFiniteState_call]
                          rw [hlookup.1]
                          dsimp only
                          rw [htlookup]
                          dsimp only
                          have htclock : (convertStateExact context source).clock ≠ 0 := hc
                          rw [if_neg htclock,hbodyRun]
                          simp only [convertResHOL,Option.map_some]
                          rw [if_pos hid,htesh]
                          dsimp only
                          rw [htshape,htvalid]
                          simp only [Bool.true_and,ite_true]
                          have hstate : PanSemStateFiniteExact.setVarHOLFinite handlerVar (convertV value)
                              {convertStateExact context middle with locals := (convertStateExact context source).locals} =
                              convertStateExact context handlerState := by
                            simp only [handlerState,PanSemStateFiniteExact.setVarHOLFinite,convertStateExact]
                            congr 1
                            exact (mapUpdate source.locals (fun entry => convertV entry.2) handlerVar value).symm
                          rw [hstate]
                          exact hhandler.1
                      next => exact False.elim (herror (Prod.mk.inj heval).1.symm)
                  · rw [if_neg hid] at heval
                    rcases Prod.mk.inj heval with ⟨hr,hp⟩
                    subst res
                    subst post
                    refine ⟨?_,?_,hbody.2.2.1,hbody.2.2.2.1,?_,hbody.2.2.2.2.2.1,hbody.2.2.2.2.2.2⟩
                    · rw [hcompile,Flapjack.evaluateHOLFiniteState_call]
                      rw [hlookup.1]
                      dsimp only
                      rw [htlookup]
                      dsimp only
                      have htclock : (convertStateExact context source).clock ≠ 0 := hc
                      rw [if_neg htclock,hbodyRun]
                      simp only [convertResHOL,Option.map_some]
                      rw [if_neg hid]
                      rfl
                    · simp [PanSemStateFiniteExact.emptyLocalsHOLFinite,feveryHOL]
                    · simp [isContResHOL]

            | finalFfi event =>
              rcases Prod.mk.inj heval with ⟨hr,hp⟩
              subst res
              subst post
              refine ⟨?_,?_,hbody.2.2.1,hbody.2.2.2.1,?_,?_,?_⟩
              · rw [hcompile,Flapjack.evaluateHOLFiniteState_call]
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

end Flapjack.Pancake.Proofs.PanStructs.CompileCorrectCall
