module

public import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact

@[expose] public section

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

/-- Flapjack-only inverse of `lookupCodeHOLFinite_eq_some`: a raw
    `lookupCodeHOLExact` result carrying the canonical callee map rebuilds the
    finite lookup. HOL's `lookup_code_def` rewrites the same equation. -/
private theorem lookupCodeHOLFinite_of_exact {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (fname : MlS) (values : List (ValueHOL width)) (body : ProgHOL width)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
    (h : lookupCodeHOLExact code fname values =
      some (body, callee.lookup, returnShape)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code fname values =
      some (body, callee, returnShape) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i hn
    rw [h] at hn
    contradiction
  · rename_i b locals r hsome
    have heq := Option.some.inj (hsome.symm.trans h)
    rcases Prod.mk.inj heq with ⟨hb, htail⟩
    rcases Prod.mk.inj htail with ⟨hl, hr⟩
    subst b
    subst locals
    subst r
    cases callee
    rfl

/-- HOL934: original successful code lookup is preserved under state_rel,
    with compiled body and identical canonical callee locals and return shape.
    NOT an exact port (tag withdrawn in task 169): the typed capture gives
    `args :γ v list` with the value type γ independent of the state's word
    type, while Lean's executed lookup is width-indexed (`ValueHOL width`), so
    the statement is the used instance of a more general HOL theorem. -/
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
      exact lookupCodeHOLFinite_of_exact target.code.lookup name arguments
        (compileProgExactHOL context program) callee resultShape htRaw
    · simp at hraw

end Flapjack.PanGlobalsStateRelationCode
