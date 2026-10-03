import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
import Flapjack.Pancake.Semantics.PanProps.EvaluateResultInvariant
import Flapjack.Pancake.Proofs.PanStructs.EvaluateStructsCodeInvariant
import Flapjack.Pancake.Proofs.PanStructs.CompileExpCorrectExact
import Flapjack.Pancake.Proofs.PanStructs.ValueShapeConversion
import Flapjack.Pancake.PanStructs.CompileProgExact
namespace Flapjack.Pancake.Proofs.PanStructs.CompileCorrectWhile
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


/-- Full original program-correctness predicate used solely to spell the
three genuine guarded IHs; no extra predicate is supplied by the caller. -/
def WhileProperty {width : Nat} {σ : Type} [NeZero width]
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

/-- Full original While case with ten premises/seven conclusions and precisely
its three guarded recursive IHs. The body IH retains source eval/Val/Word,
nonzero-word and nonzero-clock guards; recursive-loop IHs additionally retain
the actual body evaluation and original Continue/NONE outcome guards. All next
state fields/WF/maps come from the body theorem and original evaluation invariants.
Zero-word termination, clock-zero empty-locals timeout, Break-to-NONE, recursive
Continue/NONE and propagated terminal values use the faithful total evaluators.
No target evaluation, next-state compatibility or extra clock premise is added. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectWhile {width : Nat} {σ : Type} [NeZero width]
    (source post : PanSemStateFiniteExact width σ) (context : ContextExact)
    (condition : ExpHOL width) (body : ProgHOL width)
    (res : Option (PanSemResultExact width))
    (ihContinue : ∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width)
        (bodyRes : Option (PanSemResultExact width)) (middle : PanSemStateFiniteExact width σ)
        (v1 : PanSemResultExact width),
      @evalHOLExact width σ _ source.toExact
        (fun a => Classical.propDecidable (source.memaddrs a)) condition = some v2 ∧
        v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ source.clock ≠ 0 ∧
        (bodyRes,middle) = PanSemStateFiniteExact.evaluateHOLFiniteState source.decClockHOLFinite body ∧
        bodyRes = some v1 ∧ v1 = .continue →
      WhileProperty middle (.while condition body))
    (ihNone : ∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width)
        (bodyRes : Option (PanSemResultExact width)) (middle : PanSemStateFiniteExact width σ),
      @evalHOLExact width σ _ source.toExact
        (fun a => Classical.propDecidable (source.memaddrs a)) condition = some v2 ∧
        v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ source.clock ≠ 0 ∧
        (bodyRes,middle) = PanSemStateFiniteExact.evaluateHOLFiniteState source.decClockHOLFinite body ∧
        bodyRes = none →
      WhileProperty middle (.while condition body))
    (ihBody : ∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width),
      @evalHOLExact width σ _ source.toExact
        (fun a => Classical.propDecidable (source.memaddrs a)) condition = some v2 ∧
        v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ source.clock ≠ 0 →
      WhileProperty source.decClockHOLFinite body)
    (h : PanSemStateFiniteExact.evaluateHOLFiniteState source (.while condition body : ProgHOL width) = (res, post) ∧
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
      (compileProgExact context (.while condition body : ProgHOL width)) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true) := by
  classical
  rcases h with ⟨heval,hstructs,hlocal,hglobal,hwlocal,hwglobal,hinfo,hlocals,hglobals,herror⟩
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_while_fixClockRewrite] at heval
  cases hv : @evalHOLExact width σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) condition with
  | none =>
    simp only [PanSemStateFiniteExact.evalHOLFinite, hv, Prod.mk.injEq] at heval
    exact False.elim (herror heval.1.symm)
  | some value =>
    simp only [PanSemStateFiniteExact.evalHOLFinite, hv] at heval
    cases value with
    | rStruct fields =>
      simp only [Prod.mk.injEq] at heval
      exact False.elim (herror heval.1.symm)
    | nStruct name fields =>
      simp only [Prod.mk.injEq] at heval
      exact False.elim (herror heval.1.symm)
    | val payload =>
      cases payload with
      | word word =>
        have hexp := CompileExpCorrectExact.compileExpCorrectExact source context condition (.val (.word word))
          ⟨hv,hlocals,hglobals,hstructs,hlocal,hglobal,hinfo⟩
        have ht := hexp.2.2
        simp only [PanSemStateFiniteExact.evalHOLFinite, convertV] at ht
        dsimp only at heval
        by_cases hz : word = 0
        · simp only [hz, ne_eq, not_true_eq_false, if_false, Prod.mk.injEq] at heval
          rcases heval with ⟨hr,hp⟩
          subst res
          subst post
          refine ⟨?_,hlocal,hglobal,hglobals,?_,?_,?_⟩
          · rw [compileProgExact, PanSemStateFiniteExact.evaluateHOLFiniteState_while_fixClockRewrite]
            simp only [PanSemStateFiniteExact.evalHOLFinite]
            rw [ht]
            simp [hz,convertResHOL]
          · intro _
            exact hlocals
          · simp [resVsHOL]
          · simp [resVsHOL]
        · rw [if_pos hz] at heval
          by_cases hc : source.clock = 0
          · simp only [hc, ite_true, Prod.mk.injEq] at heval
            rcases heval with ⟨hr,hp⟩
            subst res
            subst post
            refine ⟨?_,?_,hglobal,hglobals,?_,?_,?_⟩
            · rw [compileProgExact, PanSemStateFiniteExact.evaluateHOLFiniteState_while_fixClockRewrite]
              simp only [PanSemStateFiniteExact.evalHOLFinite]
              rw [ht]
              dsimp only
              have htargetClock : (convertStateExact context source).clock = 0 := hc
              rw [if_pos hz, if_pos htargetClock]
              rfl
            · simp [PanSemStateFiniteExact.emptyLocalsHOLFinite, feveryHOL]
            · simp [isContResHOL]
            · simp [resVsHOL]
            · simp [resVsHOL]
          · rw [if_neg hc] at heval
            cases hb : PanSemStateFiniteExact.evaluateHOLFiniteState source.decClockHOLFinite body with
            | mk bodyRes middle =>
              rw [hb] at heval
              cases bodyRes with
              | none =>
                dsimp only at heval
                have hbody := ihBody (.val (.word word)) (.word word) word
                  ⟨hv,rfl,rfl,hz,hc⟩ middle context none
                  ⟨hb,hstructs,hlocal,hglobal,hwlocal,hwglobal,hinfo,hlocals,hglobals,by simp⟩
                have hpres := EvaluateStructsCodeInvariant.evaluateStructsCodeInv body
                  source.decClockHOLFinite middle none hb
                have hstruct : middle.structs = source.structs := hpres.1
                have hprops : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
                    (PanPropsEvalStateFiniteExact.ofPanSemFinite source.decClockHOLFinite) body =
                    (none,PanPropsEvalStateFiniteExact.ofPanSemFinite middle) := by
                  simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using
                    congrArg (fun pair => (pair.1,PanPropsEvalStateFiniteExact.ofPanSemFinite pair.2)) hb
                have hwf := evaluateIsWfShapeInvariantFiniteExact body
                  (PanPropsEvalStateFiniteExact.ofPanSemFinite source.decClockHOLFinite) none
                  (PanPropsEvalStateFiniteExact.ofPanSemFinite middle) hprops hwlocal hwglobal
                have hloop := ihNone (.val (.word word)) (.word word) word none middle
                  ⟨hv,rfl,rfl,hz,hc,hb.symm,rfl⟩ post context res
                  ⟨heval,by simpa only [hstruct] using hstructs,hbody.2.1,hbody.2.2.1,
                    hwf.1,hwf.2.1,by simpa only [hstruct] using hinfo,
                    hbody.2.2.2.2.1 (by simp [isContResHOL]),hbody.2.2.2.1,herror⟩
                refine ⟨?_,hloop.2⟩
                rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_while_fixClockRewrite]
                simp only [PanSemStateFiniteExact.evalHOLFinite]
                rw [ht]
                dsimp only
                have htargetClock : (convertStateExact context source).clock ≠ 0 := hc
                rw [if_pos hz,if_neg htargetClock]
                have htargetBody : PanSemStateFiniteExact.evaluateHOLFiniteState
                    (convertStateExact context source).decClockHOLFinite (compileProgExact context body) =
                    (convertResHOL none,convertStateExact context middle) := hbody.1
                rw [htargetBody]
                simpa only [convertResHOL,compileProgExact] using hloop.1
              | some result =>
                cases result with
                | «continue» =>
                  dsimp only at heval
                  have hbody := ihBody (.val (.word word)) (.word word) word
                    ⟨hv,rfl,rfl,hz,hc⟩ middle context (some .continue)
                    ⟨hb,hstructs,hlocal,hglobal,hwlocal,hwglobal,hinfo,hlocals,hglobals,by simp⟩
                  have hpres := EvaluateStructsCodeInvariant.evaluateStructsCodeInv body
                    source.decClockHOLFinite middle (some .continue) hb
                  have hstruct : middle.structs = source.structs := hpres.1
                  have hprops : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
                      (PanPropsEvalStateFiniteExact.ofPanSemFinite source.decClockHOLFinite) body =
                      (some .continue,PanPropsEvalStateFiniteExact.ofPanSemFinite middle) := by
                    simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using
                      congrArg (fun pair => (pair.1,PanPropsEvalStateFiniteExact.ofPanSemFinite pair.2)) hb
                  have hwf := evaluateIsWfShapeInvariantFiniteExact body
                    (PanPropsEvalStateFiniteExact.ofPanSemFinite source.decClockHOLFinite) (some .continue)
                    (PanPropsEvalStateFiniteExact.ofPanSemFinite middle) hprops hwlocal hwglobal
                  have hloop := ihContinue (.val (.word word)) (.word word) word (some .continue) middle .continue
                    ⟨hv,rfl,rfl,hz,hc,hb.symm,rfl,rfl⟩ post context res
                    ⟨heval,by simpa only [hstruct] using hstructs,hbody.2.1,hbody.2.2.1,
                      hwf.1,hwf.2.1,by simpa only [hstruct] using hinfo,
                      hbody.2.2.2.2.1 (by simp [isContResHOL]),hbody.2.2.2.1,herror⟩
                  refine ⟨?_,hloop.2⟩
                  rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_while_fixClockRewrite]
                  simp only [PanSemStateFiniteExact.evalHOLFinite]
                  rw [ht]
                  dsimp only
                  have htargetClock : (convertStateExact context source).clock ≠ 0 := hc
                  rw [if_pos hz,if_neg htargetClock]
                  have htargetBody : PanSemStateFiniteExact.evaluateHOLFiniteState
                      (convertStateExact context source).decClockHOLFinite (compileProgExact context body) =
                      (convertResHOL (some .continue),convertStateExact context middle) := hbody.1
                  rw [htargetBody]
                  simpa only [convertResHOL,compileProgExact] using hloop.1
                | «break» =>
                  dsimp only at heval
                  rcases Prod.mk.inj heval with ⟨hr,hp⟩
                  subst res
                  subst post
                  have hbody := ihBody (.val (.word word)) (.word word) word
                    ⟨hv,rfl,rfl,hz,hc⟩ middle context (some .break)
                    ⟨hb,hstructs,hlocal,hglobal,hwlocal,hwglobal,hinfo,hlocals,hglobals,by simp⟩
                  refine ⟨?_,hbody.2.1,hbody.2.2.1,hbody.2.2.2.1,?_,?_,?_⟩
                  · rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_while_fixClockRewrite]
                    simp only [PanSemStateFiniteExact.evalHOLFinite]
                    rw [ht]
                    dsimp only
                    have htargetClock : (convertStateExact context source).clock ≠ 0 := hc
                    rw [if_pos hz,if_neg htargetClock]
                    have htargetBody : PanSemStateFiniteExact.evaluateHOLFiniteState
                        (convertStateExact context source).decClockHOLFinite (compileProgExact context body) =
                        (convertResHOL (some .break),convertStateExact context middle) := hbody.1
                    rw [htargetBody]
                    rfl
                  · intro _
                    exact hbody.2.2.2.2.1 (by simp [isContResHOL])
                  · simp [resVsHOL]
                  · simp [resVsHOL]
                | error =>
                  dsimp only at heval
                  exact False.elim (herror (Prod.mk.inj heval).1.symm)
                | timeOut =>
                  dsimp only at heval
                  rcases Prod.mk.inj heval with ⟨hr,hp⟩
                  subst res
                  subst post
                  have hbody := ihBody (.val (.word word)) (.word word) word
                    ⟨hv,rfl,rfl,hz,hc⟩ middle context (some .timeOut)
                    ⟨hb,hstructs,hlocal,hglobal,hwlocal,hwglobal,hinfo,hlocals,hglobals,herror⟩
                  refine ⟨?_,hbody.2⟩
                  rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_while_fixClockRewrite]
                  simp only [PanSemStateFiniteExact.evalHOLFinite]
                  rw [ht]
                  dsimp only
                  have htargetClock : (convertStateExact context source).clock ≠ 0 := hc
                  rw [if_pos hz,if_neg htargetClock]
                  have htargetBody : PanSemStateFiniteExact.evaluateHOLFiniteState
                      (convertStateExact context source).decClockHOLFinite (compileProgExact context body) =
                      (convertResHOL (some .timeOut),convertStateExact context middle) := hbody.1
                  rw [htargetBody]
                  rfl
                | returned value =>
                  dsimp only at heval
                  rcases Prod.mk.inj heval with ⟨hr,hp⟩
                  subst res
                  subst post
                  have hbody := ihBody (.val (.word word)) (.word word) word
                    ⟨hv,rfl,rfl,hz,hc⟩ middle context (some (.returned value))
                    ⟨hb,hstructs,hlocal,hglobal,hwlocal,hwglobal,hinfo,hlocals,hglobals,herror⟩
                  refine ⟨?_,hbody.2⟩
                  rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_while_fixClockRewrite]
                  simp only [PanSemStateFiniteExact.evalHOLFinite]
                  rw [ht]
                  dsimp only
                  have htargetClock : (convertStateExact context source).clock ≠ 0 := hc
                  rw [if_pos hz,if_neg htargetClock]
                  have htargetBody : PanSemStateFiniteExact.evaluateHOLFiniteState
                      (convertStateExact context source).decClockHOLFinite (compileProgExact context body) =
                      (convertResHOL (some (.returned value)),convertStateExact context middle) := hbody.1
                  rw [htargetBody]
                  rfl
                | finalFfi outcome =>
                  dsimp only at heval
                  rcases Prod.mk.inj heval with ⟨hr,hp⟩
                  subst res
                  subst post
                  have hbody := ihBody (.val (.word word)) (.word word) word
                    ⟨hv,rfl,rfl,hz,hc⟩ middle context (some (.finalFfi outcome))
                    ⟨hb,hstructs,hlocal,hglobal,hwlocal,hwglobal,hinfo,hlocals,hglobals,herror⟩
                  refine ⟨?_,hbody.2⟩
                  rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_while_fixClockRewrite]
                  simp only [PanSemStateFiniteExact.evalHOLFinite]
                  rw [ht]
                  dsimp only
                  have htargetClock : (convertStateExact context source).clock ≠ 0 := hc
                  rw [if_pos hz,if_neg htargetClock]
                  have htargetBody : PanSemStateFiniteExact.evaluateHOLFiniteState
                      (convertStateExact context source).decClockHOLFinite (compileProgExact context body) =
                      (convertResHOL (some (.finalFfi outcome)),convertStateExact context middle) := hbody.1
                  rw [htargetBody]
                  rfl
                | exception eid value =>
                  dsimp only at heval
                  rcases Prod.mk.inj heval with ⟨hr,hp⟩
                  subst res
                  subst post
                  have hbody := ihBody (.val (.word word)) (.word word) word
                    ⟨hv,rfl,rfl,hz,hc⟩ middle context (some (.exception eid value))
                    ⟨hb,hstructs,hlocal,hglobal,hwlocal,hwglobal,hinfo,hlocals,hglobals,herror⟩
                  refine ⟨?_,hbody.2⟩
                  rw [compileProgExact,PanSemStateFiniteExact.evaluateHOLFiniteState_while_fixClockRewrite]
                  simp only [PanSemStateFiniteExact.evalHOLFinite]
                  rw [ht]
                  dsimp only
                  have htargetClock : (convertStateExact context source).clock ≠ 0 := hc
                  rw [if_pos hz,if_neg htargetClock]
                  have htargetBody : PanSemStateFiniteExact.evaluateHOLFiniteState
                      (convertStateExact context source).decClockHOLFinite (compileProgExact context body) =
                      (convertResHOL (some (.exception eid value)),convertStateExact context middle) := hbody.1
                  rw [htargetBody]
                  rfl
end Flapjack.Pancake.Proofs.PanStructs.CompileCorrectWhile
