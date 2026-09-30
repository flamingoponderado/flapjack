import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact

namespace Flapjack.PanGlobalsStateRelationCode

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

open Flapjack.Pancake.PanLang

/-- HOL934: original successful code lookup is preserved under state_rel,
    with compiled body and identical canonical callee locals and return shape. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_lookup_code"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals, callee])
  (words_as_type_indexed_bitvec)]
theorem stateRelLookupCodeHOL {width : Nat} {σ : Type} [NeZero width]
    (context : PanGlobalsContextExact width)
    (source target : PanSemStateFiniteExact width σ) (flag : Bool)
    (name : MlS) (arguments : List (ValueHOL width)) (body : ProgHOL width)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL) :
    panGlobalsStateRelHOLExact flag context source target ∧
      PanSemStateFiniteExact.lookupCodeHOLFinite source.code.lookup name arguments =
        some (body, callee, returnShape) →
    PanSemStateFiniteExact.lookupCodeHOLFinite target.code.lookup name arguments =
      some (compileProgExactHOL context body, callee, returnShape) := by
  intro ⟨hrel, heval⟩
  rcases hrel with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hcode, _⟩
  have hraw := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    source.code.lookup name arguments body callee returnShape heval
  cases hs : source.code.lookup name with
  | none => simp [lookupCodeHOLExact, hs] at hraw
  | some entry =>
    rcases entry with ⟨parameters, program, resultShape⟩
    have ht := hcode name parameters program resultShape hs
    simp only [lookupCodeHOLExact, hs] at hraw
    split at hraw
    · rename_i hvalid
      simp only [Option.some.injEq, Prod.mk.injEq] at hraw
      rcases hraw with ⟨hb, hl, hr⟩
      subst body
      subst returnShape
      have htRaw : lookupCodeHOLExact target.code.lookup name arguments =
          some (compileProgExactHOL context program, callee.lookup, resultShape) := by
        simp [lookupCodeHOLExact, ht, hvalid, hl]
      unfold PanSemStateFiniteExact.lookupCodeHOLFinite
      split
      · rename_i hn
        rw [htRaw] at hn
        contradiction
      · rename_i b locals r hsome
        have heq := Option.some.inj (hsome.symm.trans htRaw)
        rcases Prod.mk.inj heq with ⟨hb, htail⟩
        rcases Prod.mk.inj htail with ⟨hl, hr⟩
        subst b
        subst locals
        subst r
        cases callee
        rfl
    · simp at hraw

end Flapjack.PanGlobalsStateRelationCode
