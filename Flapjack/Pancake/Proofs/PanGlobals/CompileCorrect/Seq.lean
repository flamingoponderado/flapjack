import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Base
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

/-!
# pan_globals `compile_correct`: the `Seq` case

`Resume compile_correct[Seq]` (`cakeml/pancake/proofs/pan_globalsProofScript.sml:872-878`,
bead `flapjack-pxn.18.5.2.31.1`).  The case needs only the `evaluate_ind` Seq
induction hypotheses and `good_res`; it does not use `compile_exp_correct`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open PanSemStateFiniteExact

namespace PanGlobalsCompileCorrectSeqWitnesses

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

end PanGlobalsCompileCorrectSeqWitnesses

namespace PanGlobalsCompileCorrect

/-- `Seq` case of HOL `compile_correct`.  HOL's printed `evaluate_ind` Seq
    conjunct is `!c1 c2 s. (!res s1. (res,s1) = evaluate (c1,s) /\ res = NONE ==>
    P (c2,s1)) /\ P (c1,s) ==> P (Seq c1 c2,s)`; the IHs are transcribed in that
    order and orientation at `P = compileCorrectGoal`, and the conclusion is
    `P (Seq c1 c2, s)` unfolded as in the leaf cases. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Seq {width : Nat} {σ : Type} [NeZero width] :
    ∀ (c1 c2 : ProgHOL width) (s : PanSemStateFiniteExact width σ),
      (∀ (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ),
          (res, s1) = evaluateHOLFiniteState s c1 ∧ res = none →
          compileCorrectGoal c2 s1) ∧
        compileCorrectGoal c1 s →
      ∀ (res : Option (PanSemResultExact width)) (ctxt : PanGlobalsContextExact width)
        (t s' : PanSemStateFiniteExact width σ),
        panGlobalsStateRelHOLExact true ctxt s t ∧
          evaluateHOLFiniteState s (.seq c1 c2) = (res, s') ∧ res ≠ some .error →
        ∃ t', evaluateHOLFiniteState t (compileProgExactHOL ctxt (.seq c1 c2)) = (res, t') ∧
          panGlobalsStateRelHOLExact (goodResHOL res) ctxt s' t' := by
  intro c1 c2 s ⟨ih2, ih1⟩ res ctxt t s' ⟨hrel, hev, hne⟩
  have hcompile : compileProgExactHOL ctxt (.seq c1 c2 : ProgHOL width) =
      .seq (compileProgExactHOL ctxt c1) (compileProgExactHOL ctxt c2) := by
    simp [compileProgExactHOL]
  rw [evaluateHOLFiniteState_seq_line780] at hev
  rw [hcompile, evaluateHOLFiniteState_seq_line780]
  rcases hfirst : evaluateHOLFiniteState s c1 with ⟨r1, s1⟩
  rw [hfirst] at hev
  cases r1 with
  | none =>
      obtain ⟨t1, ht1, hrel1⟩ := ih1 none ctxt t s1 ⟨hrel, hfirst, by simp⟩
      simp only at hev
      obtain ⟨t', ht', hrel'⟩ := ih2 none s1 ⟨hfirst.symm, rfl⟩ res ctxt t1 s'
        ⟨hrel1, hev, hne⟩
      refine ⟨t', ?_, hrel'⟩
      simp only [ht1]
      exact ht'
  | some r =>
      simp only at hev
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
      obtain ⟨t1, ht1, hrel1⟩ := ih1 (some r) ctxt t s1 ⟨hrel, hfirst, hne⟩
      exact ⟨t1, by simp only [ht1], hrel1⟩

end PanGlobalsCompileCorrect

end Flapjack
