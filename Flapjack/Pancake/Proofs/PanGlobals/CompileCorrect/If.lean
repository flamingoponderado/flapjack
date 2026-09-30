import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Base
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpCorrect

namespace Flapjack.PanGlobalsCompileCorrectIf
open Flapjack.Pancake.PanLang PanSemStateFiniteExact PanGlobalsCompileCorrect

/-- Canonical owning-state roundtrip; Flapjack qualifier infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Canonical owning-context roundtrip; Flapjack qualifier infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

/-- Original If880-889 case, with the literal evaluate_ind constructor
witnesses and selected-branch IH. The target condition and execution are
derived from the source premises; non-word condition failures are retained. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_If {width : Nat} {σ : Type} [NeZero width]
    (condition : ExpHOL width) (thenBranch elseBranch : ProgHOL width)
    (source : PanSemStateFiniteExact width σ)
    (ih : ∀ (value : ValueHOL width) (payload : HolWordLab width) (word : BitVec width),
      @evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a)) condition = some value ∧
        value = .val payload ∧ payload = .word word →
      compileCorrectGoal (if word ≠ 0 then thenBranch else elseBranch) source) :
    ∀ (res : Option (PanSemResultExact width)) (context : PanGlobalsContextExact width)
      (target post : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true context source target ∧
        evaluateHOLFiniteState source (.ite condition thenBranch elseBranch) = (res, post) ∧
        res ≠ some .error →
      ∃ targetPost,
        evaluateHOLFiniteState target
          (compileProgExactHOL context (.ite condition thenBranch elseBranch)) = (res, targetPost) ∧
        panGlobalsStateRelHOLExact (goodResHOL res) context post targetPost := by
  classical
  intro res context target post ⟨hrel, hev, hne⟩
  rw [evaluateHOLFiniteState_ite] at hev
  cases hi : @evalHOLExact width σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) condition with
  | none =>
    simp only [hi] at hev
    exact False.elim (hne (Prod.mk.inj hev).1.symm)
  | some value =>
    cases value with
    | rStruct fields =>
      simp only [hi] at hev
      exact False.elim (hne (Prod.mk.inj hev).1.symm)
    | nStruct name fields =>
      simp only [hi] at hev
      exact False.elim (hne (Prod.mk.inj hev).1.symm)
    | val payload =>
      cases payload with
      | word word =>
        simp only [hi] at hev
        have hinit : @evalHOLFinite width σ _ source
            (fun a => Classical.propDecidable (source.memaddrs a)) condition =
              some (.val (.word word)) := hi
        have htinit : @evalHOLExact width σ _ target.toExact
            (fun a => Classical.propDecidable (target.memaddrs a))
            (compileExpExactHOL context condition) = some (.val (.word word)) :=
          PanGlobalsCompileExpCorrect.compileExpCorrectHOL source condition
            (.val (.word word)) context target ⟨hrel, hinit⟩
        have hbranch := ih (.val (.word word)) (.word word) word ⟨hinit, rfl, rfl⟩
        by_cases hz : word = 0
        · simp only [hz, ite_true] at hev
          simp only [hz, ne_eq, not_true_eq_false, ite_false] at hbranch
          obtain ⟨targetPost, ht, hr⟩ := hbranch res context target post ⟨hrel, hev, hne⟩
          exact ⟨targetPost, by simp only [compileProgExactHOL,
            evaluateHOLFiniteState_ite, htinit, hz, ite_true, ht], hr⟩
        · simp only [hz, ite_false] at hev
          simp only [hz, ne_eq, not_false_eq_true, ite_true] at hbranch
          obtain ⟨targetPost, ht, hr⟩ := hbranch res context target post ⟨hrel, hev, hne⟩
          exact ⟨targetPost, by simp only [compileProgExactHOL,
            evaluateHOLFiniteState_ite, htinit, hz, ite_false, ht], hr⟩

end Flapjack.PanGlobalsCompileCorrectIf
