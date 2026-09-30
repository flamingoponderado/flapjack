import Flapjack.Pancake.Proofs.PanGlobals.StateRelationLocals

namespace Flapjack.PanGlobalsCompileCorrectResVar

open Flapjack

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

/-- HOL613-621: restore the same local name using bindings saved from states
related with the true locals flag. The current states retain their original flag;
all non-local relation conjuncts remain those of the current states. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_res_var"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem stateRelResVar {width : Nat} {σ : Type} [NeZero width]
    (flag : Bool) (context : PanGlobalsContextExact width)
    (source target savedSource savedTarget : PanSemStateFiniteExact width σ)
    (name savedName : Flapjack.Pancake.PanLang.MlS) :
    panGlobalsStateRelHOLExact flag context source target ∧
      panGlobalsStateRelHOLExact true context savedSource savedTarget →
    panGlobalsStateRelHOLExact flag context
      {source with locals := (HolFiniteMapExact.resVarEq source.locals
        (name, savedSource.locals.lookup savedName))}
      {target with locals := (HolFiniteMapExact.resVarEq target.locals
        (name, savedTarget.locals.lookup savedName))} := by
  intro ⟨hrel, hsaved⟩
  refine ⟨hrel.1, ?_, hrel.2.2⟩
  intro hflag
  have hlocals := hrel.2.1 hflag
  have hsavedLocals := hsaved.2.1 rfl
  simp only [hlocals, hsavedLocals]

end Flapjack.PanGlobalsCompileCorrectResVar
