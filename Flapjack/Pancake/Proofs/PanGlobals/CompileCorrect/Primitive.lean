import Flapjack.Pancake.Proofs.PanGlobals.OptMmapEvalCorrect
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Base

namespace Flapjack.PanGlobalsCompileCorrectPrimitive
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

/-- Flapjack-only paired local update algebra; all non-local relation
conjuncts are unchanged and equality of locals follows from the original relation.
No separate HOL declaration is claimed for this proof support. -/
private theorem stateRelLocalSetVar {width : Nat} {σ : Type} [NeZero width]
    (context : PanGlobalsContextExact width) (source target : PanSemStateFiniteExact width σ)
    (name : MlS) (value : ValueHOL width)
    (h : panGlobalsStateRelHOLExact true context source target) :
    panGlobalsStateRelHOLExact true context
      (setVarHOLFinite name value source)
      (setVarHOLFinite name value target) := by
  have hl := h.2.1 rfl
  exact ⟨h.1, fun _ => congrArg (fun locals => locals.update (name,value)) hl, h.2.2⟩

/-- Flapjack-only equation connecting the mutually recursive compiler list
worker with literal HOL MAP; not a separate HOL declaration. -/
private theorem compileList_eq_map {width : Nat} [NeZero width]
    (context : PanGlobalsContextExact width) (arguments : List (ExpHOL width)) :
    compileExpExactHOLList context arguments = arguments.map (compileExpExactHOL context) := by
  induction arguments with
  | nil => simp only [compileExpExactHOLList,List.map_nil]
  | cons expression rest ih => simp only [compileExpExactHOLList,List.map_cons,ih]

/-- Original Primitive compiler-correctness case, HOL592-612. The original
state relation/source run/non-Error premises suffice: argument equality and
successful target primitive/validity are derived internally, with no extra IH. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Primitive {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (name : MlS) (operator : PrimOp)
    (arguments : List (ExpHOL width)) :
    ∀ (res : Option (PanSemResultExact width)) (context : PanGlobalsContextExact width)
      (target post : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true context source target ∧
        evaluateHOLFiniteState source (.primitive name operator arguments) = (res,post) ∧
        res ≠ some .error →
      ∃ targetPost,
        evaluateHOLFiniteState target (compileProgExactHOL context (.primitive name operator arguments)) = (res,targetPost) ∧
        panGlobalsStateRelHOLExact (goodResHOL res) context post targetPost := by
  classical
  intro res context target post ⟨hrel,hev,hne⟩
  rw [evaluateHOLFiniteState_primitive] at hev
  cases ha : @evalListHOLExact width σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) arguments with
  | none =>
    simp only [ha] at hev
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
    exact False.elim (hne rfl)
  | some values =>
    simp only [ha] at hev
    cases hp : panPrimopHOLExact operator values with
    | none =>
      simp only [hp] at hev
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
      exact False.elim (hne rfl)
    | some value =>
      simp only [hp] at hev
      by_cases hv : isValidValueHOLFinite source .local name value = true
      · simp only [hv,ite_true] at hev
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
        have ht := PanGlobalsOptMmapEvalCorrect.optMmapEvalCorrectHOL context source target arguments values ⟨hrel,ha⟩
        change @evalListHOLExact width σ _ target.toExact
          (fun a => Classical.propDecidable (target.memaddrs a))
          (arguments.map (compileExpExactHOL context)) = some values at ht
        have hl := hrel.2.1 rfl
        have hvalid : isValidValueHOLFinite target .local name value = true := by
          simpa only [isValidValueHOLFinite,lookupKvarHOLFinite,← hl] using hv
        refine ⟨setVarHOLFinite name value target, ?_, ?_⟩
        · simp only [compileProgExactHOL,evaluateHOLFiniteState_primitive,compileList_eq_map,ht,hp,hvalid,ite_true]
        · exact stateRelLocalSetVar context source target name value hrel
      · simp only [hv] at hev
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
        exact False.elim (hne rfl)

end Flapjack.PanGlobalsCompileCorrectPrimitive
