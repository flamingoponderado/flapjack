import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
import Flapjack.Pancake.Proofs.PanStructs.CompileExpCorrectExact
import Flapjack.Pancake.Proofs.PanStructs.EvaluateStructsCodeInvariant
import Flapjack.Pancake.PanStructs.CompileProgExact
import Flapjack.Pancake.Semantics.PanProps.EvaluateResultInvariant
namespace Flapjack.Pancake.Proofs.PanStructs.CompileCorrectSeqIf
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


/-- Genuine If case: original ten premises/seven conclusions and precisely
its source-word-guarded selected-branch induction hypothesis. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectIf {width : Nat} {σ : Type} [NeZero width]
    (source post : PanSemStateFiniteExact width σ) (context : ContextExact)
    (condition : ExpHOL width) (thenBranch elseBranch : ProgHOL width)
    (res : Option (PanSemResultExact width))
    (ih : ∀ (value : ValueHOL width) (payload : HolWordLab width) (word : BitVec width),
      @evalHOLExact width σ _ source.toExact
          (fun a => Classical.propDecidable (source.memaddrs a)) condition = some value ∧
        value = .val payload ∧ payload = .word word →
      ∀ (post : PanSemStateFiniteExact width σ) (context : ContextExact)
        (res : Option (PanSemResultExact width)),
      (PanSemStateFiniteExact.evaluateHOLFiniteState source (if word ≠ 0 then thenBranch else elseBranch : ProgHOL width) = (res, post) ∧
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
      (compileProgExact context (if word ≠ 0 then thenBranch else elseBranch : ProgHOL width)) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true))
    (h : PanSemStateFiniteExact.evaluateHOLFiniteState source (.ite condition thenBranch elseBranch : ProgHOL width) = (res, post) ∧
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
      (compileProgExact context (.ite condition thenBranch elseBranch : ProgHOL width)) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true) := by
  classical
  rcases h with ⟨heval, hstructs, hlocal, hglobal, hwlocal, hwglobal, hinfo, hlocals, hglobals, herror⟩
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_ite] at heval
  cases hv : @evalHOLExact width σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) condition with
  | none =>
    simp only [hv, Prod.mk.injEq] at heval
    exact False.elim (herror heval.1.symm)
  | some value =>
    rw [hv] at heval
    cases value with
    | rStruct values =>
      simp only [Prod.mk.injEq] at heval
      exact False.elim (herror heval.1.symm)
    | nStruct name fields =>
      simp only [Prod.mk.injEq] at heval
      exact False.elim (herror heval.1.symm)
    | val payload =>
      cases payload with
      | word word =>
        have hbranch : PanSemStateFiniteExact.evaluateHOLFiniteState source
            (if word ≠ 0 then thenBranch else elseBranch) = (res, post) := by
          by_cases hz : word = 0
          · simpa only [if_pos hz, if_neg (not_not_intro hz)] using heval
          · simpa only [if_neg hz, if_pos hz] using heval
        have hb := ih (.val (.word word)) (.word word) word ⟨hv, rfl, rfl⟩ post context res
          ⟨hbranch, hstructs, hlocal, hglobal, hwlocal, hwglobal, hinfo, hlocals, hglobals, herror⟩
        have hexp := CompileExpCorrectExact.compileExpCorrectExact source context condition (.val (.word word))
          ⟨by simpa [PanSemStateFiniteExact.evalHOLFinite] using hv,
            hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩
        refine ⟨?_, hb.2⟩
        have htarget := hexp.2.2
        simp only [PanSemStateFiniteExact.evalHOLFinite] at htarget
        simp only [compileProgExact, PanSemStateFiniteExact.evaluateHOLFiniteState_ite, htarget, convertV]
        by_cases hz : word = 0
        · simpa only [if_pos hz, if_neg (not_not_intro hz)] using hb.1
        · simpa only [if_neg hz, if_pos hz] using hb.1
/-- Genuine Seq case with the first-program IH and the source-NONE-guarded
second-program IH at the actual intermediate state. All original premises and
conclusions are retained. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectSeq {width : Nat} {σ : Type} [NeZero width]
    (source post : PanSemStateFiniteExact width σ) (context : ContextExact)
    (first second : ProgHOL width) (res : Option (PanSemResultExact width))
    (ihFirst : ∀ (post : PanSemStateFiniteExact width σ) (context : ContextExact)
      (res : Option (PanSemResultExact width)),
      (PanSemStateFiniteExact.evaluateHOLFiniteState source first = (res, post) ∧
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
      (compileProgExact context first) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true))
    (ihSecond : ∀ (firstRes : Option (PanSemResultExact width))
      (middle : PanSemStateFiniteExact width σ),
      (firstRes, middle) = PanSemStateFiniteExact.evaluateHOLFiniteState source first ∧
        firstRes = none →
      ∀ (post : PanSemStateFiniteExact width σ) (context : ContextExact)
        (res : Option (PanSemResultExact width)),
      (PanSemStateFiniteExact.evaluateHOLFiniteState middle second = (res, post) ∧
      context.structs = middle.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact middle.structs entry.2) middle.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact middle.structs entry.2) middle.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact middle.structs entry.2) middle.locals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact middle.structs entry.2) middle.globals ∧
      structInfosOkHOLExact middle.structs ∧
      shapeMap context.locals = middle.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = middle.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      res ≠ some .error) →
    PanSemStateFiniteExact.evaluateHOLFiniteState (convertStateExact context middle)
      (compileProgExact context second) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true))
    (h : PanSemStateFiniteExact.evaluateHOLFiniteState source (.seq first second : ProgHOL width) = (res, post) ∧
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
      (compileProgExact context (.seq first second : ProgHOL width)) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true) := by
  classical
  rcases h with ⟨heval, hstructs, hlocal, hglobal, hwlocal, hwglobal, hinfo, hlocals, hglobals, herror⟩
  rw [evaluateHOLFiniteState_seq_line780] at heval
  cases hfirst : PanSemStateFiniteExact.evaluateHOLFiniteState source first with
  | mk firstRes middle =>
    rw [hfirst] at heval
    cases firstRes with
    | none =>
      dsimp only at heval
      have hf := ihFirst middle context none
        ⟨hfirst, hstructs, hlocal, hglobal, hwlocal, hwglobal, hinfo, hlocals, hglobals, by simp⟩
      have hpres := EvaluateStructsCodeInvariant.evaluateStructsCodeInv first source middle none hfirst
      have hprops : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
          (PanPropsEvalStateFiniteExact.ofPanSemFinite source) first =
          (none, PanPropsEvalStateFiniteExact.ofPanSemFinite middle) := by
        simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using
          congrArg (fun pair => (pair.1, PanPropsEvalStateFiniteExact.ofPanSemFinite pair.2)) hfirst
      have hwf := evaluateIsWfShapeInvariantFiniteExact first
        (PanPropsEvalStateFiniteExact.ofPanSemFinite source) none
        (PanPropsEvalStateFiniteExact.ofPanSemFinite middle) hprops hwlocal hwglobal
      have hs := ihSecond none middle ⟨hfirst.symm, rfl⟩ post context res
        ⟨heval, by simpa only [hpres.1] using hstructs,
          hf.2.1, hf.2.2.1, hwf.1, hwf.2.1,
          by simpa only [hpres.1] using hinfo,
          hf.2.2.2.2.1 (by simp [isContResHOL]), hf.2.2.2.1, herror⟩
      refine ⟨?_, hs.2⟩
      simp only [compileProgExact, evaluateHOLFiniteState_seq_line780,
        hf.1, convertResHOL]
      exact hs.1
    | some result =>
      dsimp only at heval
      rcases Prod.mk.inj heval with ⟨hr, hp⟩
      subst res
      subst post
      have hf := ihFirst middle context (some result)
        ⟨hfirst, hstructs, hlocal, hglobal, hwlocal, hwglobal, hinfo, hlocals, hglobals, herror⟩
      refine ⟨?_, hf.2⟩
      simp only [compileProgExact, evaluateHOLFiniteState_seq_line780, hf.1]
      cases result <;> rfl

end Flapjack.Pancake.Proofs.PanStructs.CompileCorrectSeqIf
