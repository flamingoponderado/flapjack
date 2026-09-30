import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationClock

/-!
# pan_globals `compile_correct`: goal and the leaf cases

Counterpart of `cakeml/pancake/proofs/pan_globalsProofScript.sml:164-242`
(bead `flapjack-pxn.18.5.2.26`): the HOL goal of
`compile_correct` (`gen_goal` instantiated with `pan_globals$compile`, lines
172-184) and its `Skip`, `Break`, `Continue`, `Annot` and `Tick` `Resume` cases.
The source evaluator is the tagged finite-support `evaluateHOLFiniteState`
(`panSem$evaluate_def`), the compiler the tagged `compileProgExactHOL`
(`pan_globals$compile_def`) and the relation the tagged
`panGlobalsStateRelHOLExact` (`state_rel_def`), and `good_res` the tagged
`goodResHOL` (`Proofs/PanGlobals.lean`).  Each case states HOL's goal
for its constructor, as in HOL's `evaluate_ind` conjunct; these leaf
constructors carry no induction hypothesis.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open PanSemStateFiniteExact

namespace PanGlobalsCompileCorrect

/-- Canonical state roundtrip, re-exported for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Canonical context roundtrip, re-exported for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

/-- HOL's `gen_goal pan_globals$compile` (`pan_globalsProofScript.sml:172-182`)
    for one program and source state; the shared conclusion of every
    `compile_correct` case.  Untagged: HOL's `goal` is an ML value, not a
    declaration. -/
def compileCorrectGoal {width : Nat} {σ : Type} [NeZero width]
    (p : ProgHOL width) (s : PanSemStateFiniteExact width σ) : Prop :=
  ∀ (res : Option (PanSemResultExact width)) (ctxt : PanGlobalsContextExact width)
    (t s' : PanSemStateFiniteExact width σ),
    panGlobalsStateRelHOLExact true ctxt s t ∧
      evaluateHOLFiniteState s p = (res, s') ∧ res ≠ some .error →
    ∃ t', evaluateHOLFiniteState t (compileProgExactHOL ctxt p) = (res, t') ∧
      panGlobalsStateRelHOLExact (goodResHOL res) ctxt s' t'

/-- A leaf whose source and compiled evaluations return the state unchanged
    with a good result.  Local support; no HOL original. -/
private theorem unchanged_leaf {width : Nat} {σ : Type} [NeZero width]
    (p : ProgHOL width) (s : PanSemStateFiniteExact width σ)
    (r : Option (PanSemResultExact width))
    (hsource : ∀ st : PanSemStateFiniteExact width σ, evaluateHOLFiniteState st p = (r, st))
    (hcompile : ∀ ctxt : PanGlobalsContextExact width, compileProgExactHOL ctxt p = p)
    (hgood : goodResHOL r = true) :
    compileCorrectGoal p s := by
  intro res ctxt t s' ⟨hrel, hev, _⟩
  rw [hsource] at hev
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
  refine ⟨t, by rw [hcompile, hsource], ?_⟩
  rw [hgood]
  exact hrel

/-- `Skip` case of HOL `compile_correct` (`pan_globalsProofScript.sml:186`,
    resumed at `:214-218`); no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Skip {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) :
    ∀ (res : Option (PanSemResultExact width)) (ctxt : PanGlobalsContextExact width)
      (t s' : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true ctxt s t ∧
        evaluateHOLFiniteState s .skip = (res, s') ∧ res ≠ some .error →
      ∃ t', evaluateHOLFiniteState t (compileProgExactHOL ctxt .skip) = (res, t') ∧
        panGlobalsStateRelHOLExact (goodResHOL res) ctxt s' t' :=
  unchanged_leaf .skip s none (fun st => evaluateHOLFiniteState_skip st)
    (fun _ => by simp [compileProgExactHOL]) rfl

/-- `Break` case of HOL `compile_correct` (resumed at `:220-224`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Break {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) :
    ∀ (res : Option (PanSemResultExact width)) (ctxt : PanGlobalsContextExact width)
      (t s' : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true ctxt s t ∧
        evaluateHOLFiniteState s .break = (res, s') ∧ res ≠ some .error →
      ∃ t', evaluateHOLFiniteState t (compileProgExactHOL ctxt .break) = (res, t') ∧
        panGlobalsStateRelHOLExact (goodResHOL res) ctxt s' t' :=
  unchanged_leaf .break s (some .break) (fun st => evaluateHOLFiniteState_break st)
    (fun _ => by simp [compileProgExactHOL]) rfl

/-- `Continue` case of HOL `compile_correct` (resumed at `:226-230`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Continue {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) :
    ∀ (res : Option (PanSemResultExact width)) (ctxt : PanGlobalsContextExact width)
      (t s' : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true ctxt s t ∧
        evaluateHOLFiniteState s .continue = (res, s') ∧ res ≠ some .error →
      ∃ t', evaluateHOLFiniteState t (compileProgExactHOL ctxt .continue) = (res, t') ∧
        panGlobalsStateRelHOLExact (goodResHOL res) ctxt s' t' :=
  unchanged_leaf .continue s (some .continue) (fun st => evaluateHOLFiniteState_continue st)
    (fun _ => by simp [compileProgExactHOL]) rfl

/-- `Annot` case of HOL `compile_correct` (resumed at `:232-236`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Annot {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (tag text : MlS) :
    ∀ (res : Option (PanSemResultExact width)) (ctxt : PanGlobalsContextExact width)
      (t s' : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true ctxt s t ∧
        evaluateHOLFiniteState s (.annot tag text) = (res, s') ∧ res ≠ some .error →
      ∃ t', evaluateHOLFiniteState t (compileProgExactHOL ctxt (.annot tag text)) = (res, t') ∧
        panGlobalsStateRelHOLExact (goodResHOL res) ctxt s' t' :=
  unchanged_leaf (.annot tag text) s none (fun st => evaluateHOLFiniteState_annot st tag text)
    (fun _ => by simp [compileProgExactHOL]) rfl

/-- `Tick` case of HOL `compile_correct` (resumed at `:238-242`): both clocks
    agree by `state_rel`; a zero clock times out with cleared locals (relation
    at flag `F`), otherwise both clocks decrease (`state_rel_dec_clock`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Tick {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) :
    ∀ (res : Option (PanSemResultExact width)) (ctxt : PanGlobalsContextExact width)
      (t s' : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true ctxt s t ∧
        evaluateHOLFiniteState s .tick = (res, s') ∧ res ≠ some .error →
      ∃ t', evaluateHOLFiniteState t (compileProgExactHOL ctxt .tick) = (res, t') ∧
        panGlobalsStateRelHOLExact (goodResHOL res) ctxt s' t' := by
  intro res ctxt t s' ⟨hrel, hev, _⟩
  have hclock : s.clock = t.clock := hrel.2.2.2.2.2.1
  have hcompile : compileProgExactHOL ctxt (.tick : ProgHOL width) = .tick := by
    simp [compileProgExactHOL]
  rw [evaluateHOLFiniteState_tick] at hev
  rw [hcompile, evaluateHOLFiniteState_tick, ← hclock]
  by_cases hz : s.clock = 0
  · rw [if_pos hz] at hev ⊢
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
    refine ⟨_, rfl, ?_⟩
    exact ⟨hrel.1, fun h => absurd h (by simp [goodResHOL]), hrel.2.2⟩
  · rw [if_neg hz] at hev ⊢
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
    exact ⟨_, rfl, Flapjack.PanGlobalsStateRelationClock.stateRelDecClockHOL ctxt s t true hrel⟩

end PanGlobalsCompileCorrect

end Flapjack
