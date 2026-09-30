import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Base
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.ResVar
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpCorrect

namespace Flapjack.PanGlobalsCompileCorrectDec
open Flapjack.Pancake.PanLang PanSemStateFiniteExact
open PanGlobalsCompileCorrect

/-- Canonical owning-state roundtrip re-export; Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Canonical owning-context roundtrip re-export; Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

/-- Original Dec624-633 case. The only IH is the literal evaluate_ind Dec
guard: initializer evaluation and shape equality imply the original goal at
the body state with the bound local updated. Target execution and the restored
post-state relation are derived, including restoration after non-good results. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Dec {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL width) (body : ProgHOL width)
    (source : PanSemStateFiniteExact width σ)
    (ih : ∀ value,
      @evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a)) initializer = some value ∧
        shape = shapeOfHOLExact value →
      compileCorrectGoal body (setVarHOLFinite name value source)) :
    ∀ (res : Option (PanSemResultExact width)) (context : PanGlobalsContextExact width)
      (target post : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true context source target ∧
        evaluateHOLFiniteState source (.dec name shape initializer body) = (res, post) ∧
        res ≠ some .error →
      ∃ targetPost,
        evaluateHOLFiniteState target
          (compileProgExactHOL context (.dec name shape initializer body)) = (res, targetPost) ∧
        panGlobalsStateRelHOLExact (goodResHOL res) context post targetPost := by
  classical
  intro res context target post ⟨hrel, hev, hne⟩
  rw [evaluateHOLFiniteState_dec_total] at hev
  dsimp only at hev
  cases hi : @evalHOLExact width σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) initializer with
  | none =>
    simp only [hi] at hev
    exact False.elim (hne (Prod.mk.inj hev).1.symm)
  | some value =>
    simp only [hi] at hev
    by_cases hs : shapeEqHOL shape (shapeOfHOLExact value) = true
    · simp only [hs, ite_true] at hev
      have hinit : @evalHOLFinite width σ _ source
          (fun a => Classical.propDecidable (source.memaddrs a)) initializer = some value := hi
      have htinit := PanGlobalsCompileExpCorrect.compileExpCorrectHOL
        source initializer value context target ⟨hrel, hinit⟩
      have htinitExact : @evalHOLExact width σ _ target.toExact
          (fun a => Classical.propDecidable (target.memaddrs a))
          (compileExpExactHOL context initializer) = some value := htinit
      have hbodyRel := PanGlobalsStateRelationLocals.stateRelSetVarHOL
        context source target true name value hrel
      rcases hbody : evaluateHOLFiniteState (setVarHOLFinite name value source) body with
        ⟨bodyRes, bodyPost⟩
      rw [hbody] at hev
      dsimp only at hev
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
      obtain ⟨targetBodyPost, htBody, hpostRel⟩ :=
        ih value ⟨hinit, (shapeEqHOL_eq_true _ _).mp hs⟩
          bodyRes context (setVarHOLFinite name value target) bodyPost ⟨hbodyRel, hbody, hne⟩
      refine ⟨{targetBodyPost with
        locals := HolFiniteMapExact.resVarEq targetBodyPost.locals
          (name, target.locals.lookup name)}, ?_, ?_⟩
      · simp only [compileProgExactHOL, evaluateHOLFiniteState_dec_total,
          htinitExact, hs, ite_true, htBody]
      · exact PanGlobalsCompileCorrectResVar.stateRelResVar (goodResHOL bodyRes)
          context bodyPost targetBodyPost source target name name ⟨hpostRel, hrel⟩
    · simp only [hs, Bool.false_eq_true, ite_false] at hev
      exact False.elim (hne (Prod.mk.inj hev).1.symm)

end Flapjack.PanGlobalsCompileCorrectDec
