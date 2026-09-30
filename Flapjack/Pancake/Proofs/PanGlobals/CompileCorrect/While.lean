import Flapjack.Pancake.Proofs.PanGlobals.CompileExpCorrect
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Base
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationLocals
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationClock
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack.PanGlobalsCompileCorrectWhile
open Flapjack.Pancake.PanLang

/-- Canonical state roundtrips, re-exported for this relation theorem. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Canonical context roundtrip, re-exported for this relation theorem. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

open Flapjack.PanSemStateFiniteExact

open Flapjack.PanGlobalsCompileCorrect

/-- While case of HOL compile_correct (902-916). The three IHs are precisely
    the body and NONE/Continue tail guards of the original evaluate_ind;
    constructor-equality aliases are collapsed, with every semantic guard retained. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_While {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (condition : ExpHOL width) (body : ProgHOL width)
    (ihContinue : ∀ (word : BitVec width) (s1 : PanSemStateFiniteExact width σ),
      @evalHOLFinite width σ _ source (fun a => Classical.propDecidable (source.memaddrs a)) condition = some (.val (.word word)) ∧ word ≠ 0 ∧ source.clock ≠ 0 ∧
        (some .continue,s1) = evaluateHOLFiniteState (decClockHOLFinite source) body →
      compileCorrectGoal (.while condition body) s1)
    (ihNone : ∀ (word : BitVec width) (s1 : PanSemStateFiniteExact width σ),
      @evalHOLFinite width σ _ source (fun a => Classical.propDecidable (source.memaddrs a)) condition = some (.val (.word word)) ∧ word ≠ 0 ∧ source.clock ≠ 0 ∧
        (none,s1) = evaluateHOLFiniteState (decClockHOLFinite source) body →
      compileCorrectGoal (.while condition body) s1)
    (ihBody : ∀ (word : BitVec width),
      @evalHOLFinite width σ _ source (fun a => Classical.propDecidable (source.memaddrs a)) condition = some (.val (.word word)) ∧ word ≠ 0 ∧ source.clock ≠ 0 →
      compileCorrectGoal body (decClockHOLFinite source)) :
    ∀ (res : Option (PanSemResultExact width)) (context : PanGlobalsContextExact width)
      (target post : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true context source target ∧
        evaluateHOLFiniteState source (.while condition body) = (res,post) ∧ res ≠ some .error →
      ∃ targetPost,
        evaluateHOLFiniteState target (compileProgExactHOL context (.while condition body)) = (res,targetPost) ∧
        panGlobalsStateRelHOLExact (goodResHOL res) context post targetPost := by
  classical
  intro res context target post ⟨hrel,hev,hne⟩
  have hcompile : compileProgExactHOL context (.while condition body : ProgHOL width) =
      .while (compileExpExactHOL context condition) (compileProgExactHOL context body) := by
    simp [compileProgExactHOL]
  rw [evaluateHOLFiniteState_while_fixClockRewrite] at hev
  rw [hcompile,evaluateHOLFiniteState_while_fixClockRewrite]
  cases he : @evalHOLFinite width σ _ source (fun a => Classical.propDecidable (source.memaddrs a)) condition with
  | none => simp only [he] at hev; obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev; exact False.elim (hne rfl)
  | some value =>
    cases value with
    | rStruct fields => simp only [he] at hev; obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev; exact False.elim (hne rfl)
    | nStruct name fields => simp only [he] at hev; obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev; exact False.elim (hne rfl)
    | val scalar =>
      cases scalar with
      | word word =>
        have ht := PanGlobalsCompileExpCorrect.compileExpCorrectHOL source condition (.val (.word word)) context target ⟨hrel,he⟩
        change @evalHOLFinite width σ _ target (fun a => Classical.propDecidable (target.memaddrs a)) (compileExpExactHOL context condition) = some (.val (.word word)) at ht
        simp only [he] at hev
        simp only [ht]
        by_cases hw : word = 0
        · simp only [hw,ne_eq,not_true_eq_false,↓reduceIte] at hev ⊢
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
          exact ⟨target,rfl,hrel⟩
        · simp only [if_pos hw] at hev ⊢
          have hc := hrel.2.2.2.2.2.1
          by_cases hz : source.clock = 0
          · have htz : target.clock = 0 := hc ▸ hz
            simp only [if_pos hz] at hev
            obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
            exact ⟨emptyLocalsHOLFinite target,by simp only [if_pos htz],
              (PanGlobalsStateRelationLocals.stateRelEmptyLocalsHOL context source target false).1 hrel⟩
          · have htz : target.clock ≠ 0 := hc ▸ hz
            simp only [if_neg hz] at hev
            simp only [if_neg htz]
            rcases hb : evaluateHOLFiniteState (decClockHOLFinite source) body with ⟨br,bs⟩
            simp only [hb] at hev
            have hbody := ihBody word ⟨he,hw,hz⟩
            have hd := PanGlobalsStateRelationClock.stateRelDecClockHOL context source target true hrel
            cases br with
            | none =>
              obtain ⟨bt,hbt,hr⟩ := hbody none context (decClockHOLFinite target) bs ⟨hd,hb,by simp⟩
              obtain ⟨out,hout,hrout⟩ := ihNone word bs ⟨he,hw,hz,hb.symm⟩ res context bt post ⟨hr,hev,hne⟩
              exact ⟨out,by simp only [hbt]; exact hcompile ▸ hout,hrout⟩
            | some result =>
              cases result with
              | «continue» =>
                obtain ⟨bt,hbt,hr⟩ := hbody (some .continue) context (decClockHOLFinite target) bs ⟨hd,hb,by simp⟩
                obtain ⟨out,hout,hrout⟩ := ihContinue word bs ⟨he,hw,hz,hb.symm⟩ res context bt post ⟨hr,hev,hne⟩
                exact ⟨out,by simp only [hbt]; exact hcompile ▸ hout,hrout⟩
              | error =>
                obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
                exact False.elim (hne rfl)
              | «break» =>
                obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
                obtain ⟨bt,hbt,hr⟩ := hbody (some .break) context (decClockHOLFinite target) bs ⟨hd,hb,by simp⟩
                exact ⟨bt,by simp only [hbt],hr⟩
              | timeOut | returned value | exception eid value | finalFfi outcome =>
                obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
                obtain ⟨bt,hbt,hr⟩ := hbody _ context (decClockHOLFinite target) bs ⟨hd,hb,by simp⟩
                exact ⟨bt,by simp only [hbt],hr⟩

end Flapjack.PanGlobalsCompileCorrectWhile
