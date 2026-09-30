import Flapjack.Pancake.Proofs.PanGlobals.CompileExpCorrect
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Base

namespace Flapjack.PanGlobalsCompileCorrectAssignLocal
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
private theorem stateRelLocalUpdate {width : Nat} {σ : Type} [NeZero width]
    (context : PanGlobalsContextExact width) (source target : PanSemStateFiniteExact width σ)
    (name : MlS) (value : ValueHOL width)
    (h : panGlobalsStateRelHOLExact true context source target) :
    panGlobalsStateRelHOLExact true context
      (setKvarHOLFinite .local name value source)
      (setKvarHOLFinite .local name value target) := by
  have hl := h.2.1 rfl
  exact ⟨h.1, fun _ => congrArg (fun locals => locals.update (name,value)) hl, h.2.2⟩

/-- Local-variable branch of the original Assign case, HOL535-596.
Original source state relation, evaluation and non-Error conjunction imply
existential compiled evaluation and full post-state relation. Initializer
correspondence and target validity are proved internally; no extra premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_AssignLocal {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (name : MlS) (expression : ExpHOL width) :
    ∀ (res : Option (PanSemResultExact width)) (context : PanGlobalsContextExact width)
      (target post : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true context source target ∧
        evaluateHOLFiniteState source (.assign .local name expression) = (res,post) ∧
        res ≠ some .error →
      ∃ targetPost,
        evaluateHOLFiniteState target (compileProgExactHOL context (.assign .local name expression)) = (res,targetPost) ∧
        panGlobalsStateRelHOLExact (goodResHOL res) context post targetPost := by
  classical
  intro res context target post ⟨hrel,hev,hne⟩
  rw [evaluateHOLFiniteState_assign] at hev
  cases hi : @evalHOLExact width σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) expression with
  | none =>
    simp only [hi] at hev
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
    exact False.elim (hne rfl)
  | some value =>
    simp only [hi] at hev
    by_cases hv : isValidValueHOLFinite source .local name value = true
    · simp only [hv,ite_true] at hev
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
      have he := PanGlobalsCompileExpCorrect.compileExpCorrectHOL source expression value context target ⟨hrel,hi⟩
      change @evalHOLExact width σ _ target.toExact
        (fun a => Classical.propDecidable (target.memaddrs a)) (compileExpExactHOL context expression) = some value at he
      have hl := hrel.2.1 rfl
      have hvalid : isValidValueHOLFinite target .local name value = true := by
        simpa only [isValidValueHOLFinite,lookupKvarHOLFinite,← hl] using hv
      refine ⟨setKvarHOLFinite .local name value target, ?_, ?_⟩
      · simp only [compileProgExactHOL,evaluateHOLFiniteState_assign,he,hvalid,ite_true]
      · exact stateRelLocalUpdate context source target name value hrel
    · simp only [hv] at hev
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj hev
      exact False.elim (hne rfl)

end Flapjack.PanGlobalsCompileCorrectAssignLocal
