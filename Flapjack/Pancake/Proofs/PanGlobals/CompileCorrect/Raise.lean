import Flapjack.Pancake.Proofs.PanGlobals.CompileExpCorrect
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Base
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationLocals

namespace Flapjack.PanGlobalsCompileCorrectRaise
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

/-- Original Raise case of HOL866-870. Only the original state relation,
source run and non-Error conjunction are premises; target exception lookup,
value, shape/size validity, execution and post relation are derived internally. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Raise {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (exceptionId : MlS) (expression : ExpHOL width) :
    ∀ (res : Option (PanSemResultExact width)) (context : PanGlobalsContextExact width)
      (target post : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true context source target ∧
        evaluateHOLFiniteState source (.raise exceptionId expression) = (res,post) ∧
        res ≠ some .error →
      ∃ targetPost,
        evaluateHOLFiniteState target (compileProgExactHOL context (.raise exceptionId expression)) = (res,targetPost) ∧
        panGlobalsStateRelHOLExact (goodResHOL res) context post targetPost := by
  classical
  intro res context target post ⟨hrel,hev,hne⟩
  rw [evaluateHOLFiniteState_raise] at hev
  cases hs : source.eshapes.lookup exceptionId with
  | none =>
    simp only [hs] at hev
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
    exact False.elim (hne rfl)
  | some shape =>
    simp only [hs] at hev
    cases he : @evalHOLExact width σ _ source.toExact
        (fun a => Classical.propDecidable (source.memaddrs a)) expression with
    | none =>
      simp only [he] at hev
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
      exact False.elim (hne rfl)
    | some value =>
      simp only [he] at hev
      by_cases hv : shapeOfHOLExact value = shape ∧
          sizeOfShapeWithContextHOL source.structs (shapeOfHOLExact value) ≤ 32
      · rw [if_pos hv] at hev
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
        have ht := PanGlobalsCompileExpCorrect.compileExpCorrectHOL source expression value context target ⟨hrel,he⟩
        change @evalHOLExact width σ _ target.toExact
          (fun a => Classical.propDecidable (target.memaddrs a)) (compileExpExactHOL context expression) = some value at ht
        have heshapes := hrel.2.2.2.2.1
        have hstructs := panGlobalsStateRelStructsHOLExact true context source target hrel
        have hvalid : shapeOfHOLExact value = shape ∧
            sizeOfShapeWithContextHOL target.structs (shapeOfHOLExact value) ≤ 32 := by
          simpa only [hstructs.1,hstructs.2] using hv
        refine ⟨emptyLocalsHOLFinite target, ?_, ?_⟩
        · simp only [compileProgExactHOL,evaluateHOLFiniteState_raise,← heshapes,hs,ht]
          exact if_pos hvalid
        · exact (PanGlobalsStateRelationLocals.stateRelEmptyLocalsHOL context source target
            (goodResHOL (some (.exception exceptionId value)))).1 hrel
      · rw [if_neg hv] at hev
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
        exact False.elim (hne rfl)

end Flapjack.PanGlobalsCompileCorrectRaise
