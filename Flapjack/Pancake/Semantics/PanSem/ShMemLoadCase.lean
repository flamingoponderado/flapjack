import Flapjack.Pancake.Semantics.PanSem.EvaluateFinite

/-!
# The HOL `evaluate_def` ShMemLoad equation

This case is kept in its own module so case work can proceed independently of
the shared `EvaluateFinite` clause file. Its conclusion spells out the two
source matches from `panSemScript.sml:605-610`: first `eval s ad`, then
`lookup_kvar vk v s`; each failed check returns `(SOME Error, s)`.

The state carrier is `PanSemStateFiniteExact`; its four finite maps are the
reviewed canonical `HolFiniteMapExact` translation. The successful branch calls
the finite-carrier `shMemLoadHOLFiniteExact`, which directly expresses
`sh_mem_load_def`; it does not route through the broad function-backed helper.
This theorem does not add a decidability premise: the shared-memory predicate
is decided classically, as the pair evaluator does.
-/

namespace Flapjack.Pancake.Semantics.PanSem.ShMemLoadCase

open Flapjack.Pancake.PanLang (ExpHOL MlS ProgHOL)

theorem ofExact_toExact_any {width : Nat} {σ : Type} [NeZero width]
    (state : Flapjack.PanSemStateFiniteExact width σ)
    (support : state.toExact.FiniteSupport) :
    Flapjack.PanSemStateFiniteExact.ofExact state.toExact support = state := by
  cases state
  rfl

/- The checker requires the canonical representation witness to live beside
   every declaration using the finite-map qualifier. This names the imported
   carrier and its actual `toExact`/`ofExact` roundtrip. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : Flapjack.PanSemStateFiniteExact width σ),
        Flapjack.PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) := by
  intro state
  exact Flapjack.PanSemStateFiniteExact.ofExact_toExact state

/-- HOL `evaluate_def`'s `ShMemLoad` clause (`panSemScript.sml:605-610`).
    The two nested matches and both error/original-state branches are the
    source equation itself. The word/word branch calls the direct finite-carrier
    `sh_mem_load_def` port at `nb_op op`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evaluateHOLFiniteState_shMemLoad_source {width : Nat} {σ : Type}
    [NeZero width] (state : Flapjack.PanSemStateFiniteExact width σ)
    (operator : Flapjack.OpSize) (kind : Flapjack.VarKind) (name : MlS)
    (address : ExpHOL width) :
    Flapjack.PanSemStateFiniteExact.evaluateHOLFiniteState state
        (.shMemLoad operator kind name address : ProgHOL width) =
      match @Flapjack.PanSemStateFiniteExact.evalHOLFinite width σ _ state
          (fun current => Classical.propDecidable (state.memaddrs current)) address with
      | some (.val (.word addr)) =>
          match Flapjack.PanSemStateFiniteExact.lookupKvarHOLFinite kind name state with
          | some (.val (.word _)) =>
              let loaded := @Flapjack.PanSemStateFiniteExact.shMemLoadHOLFiniteExact
                width σ _ state
                (fun current => Classical.propDecidable (state.shMemaddrs current))
                kind name addr (Flapjack.nbOpHOL operator)
              (loaded.1, loaded.2)
          | _ => (some .error, state)
      | _ => (some .error, state) := by
  classical
  simp [Flapjack.PanSemStateFiniteExact.evaluateHOLFiniteState,
    Flapjack.PanSemStateFiniteExact.evaluateHOLFiniteStateWithDeciders,
    Flapjack.PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext,
    Flapjack.shMemLoadClauseHOLExact,
    Flapjack.PanSemStateFiniteExact.evalHOLFinite_eq_toExact] <;>
    repeat' split <;> simp_all <;> try apply ofExact_toExact_any
  case h_1 =>
    exact (Prod.mk.inj
      (Flapjack.PanSemStateFiniteExact.shMemLoadHOLFiniteExact_repack
        state kind name _ (Flapjack.nbOpHOL operator)))

end Flapjack.Pancake.Semantics.PanSem.ShMemLoadCase
