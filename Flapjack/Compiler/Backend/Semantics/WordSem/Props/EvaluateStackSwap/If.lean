import Flapjack.HolRef
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap.Leaves
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd

/-!
# `evaluate_stack_swap` `If` case

The `If` case of `wordPropsScript.sml:2316-2363` `evaluate_stack_swap`
(proof `wordPropsScript.sml:2529-2532`), with the induction hypotheses of HOL
`evaluate_ind`.
-/

namespace Flapjack

namespace WordSemStackEq

open WordSemStateFiniteExact

namespace EvaluateStackSwapIfWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end EvaluateStackSwapIfWitnesses

open EvaluateStackSwapIfWitnesses

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `If` case
(proof `wordPropsScript.sml:2529-2532`): the HOL conclusion at
`If cmp r1 ri c1 c2`, from exactly HOL `evaluate_ind`'s two guarded `If`
induction hypotheses; no extra premise. The guard reads only locals, so the
stack-swapped run takes the same branch. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_stack_swap"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateStackSwap_If {width : Nat} [NeZero width] {C F : Type} (cmp : Cmp) (r1 : Nat)
    (ri : WordRegImm (BitVec width)) (c1 c2 : WordLangProgHOL (BitVec width)) :
    ∀ s : WordSemStateFiniteExact width C F,
      (∀ v3 v4 x y v, (getVar r1 s, WordSemStateFiniteExact.getVarImm ri s) = (v3, v4) ∧
          v3 = some x ∧ v4 = some y ∧ wordSemWordCmp cmp x y = some v ∧ v = true →
          stackSwapPost c1 s) ∧
        (∀ v3 v4 x y v, (getVar r1 s, WordSemStateFiniteExact.getVarImm ri s) = (v3, v4) ∧
          v3 = some x ∧ v4 = some y ∧ wordSemWordCmp cmp x y = some v ∧ ¬ v = true →
          stackSwapPost c2 s) →
      stackSwapPost (.ite cmp r1 ri c1 c2) s := by
  rintro s ⟨ih1, ih2⟩
  have hg : ∀ xs, getVar r1 { s with stack := xs } = getVar r1 s := fun _ => rfl
  have hi : ∀ xs, WordSemStateFiniteExact.getVarImm ri { s with stack := xs } =
      WordSemStateFiniteExact.getVarImm ri s := by
    intro xs; cases ri <;> rfl
  have hb : ∀ c : WordLangProgHOL (BitVec width),
      (∀ t : WordSemStateFiniteExact width C F, getVar r1 t = getVar r1 s →
        WordSemStateFiniteExact.getVarImm ri t = WordSemStateFiniteExact.getVarImm ri s →
        evaluate (.ite cmp r1 ri c1 c2) t = evaluate c t) →
      stackSwapPost c s → stackSwapPost (.ite cmp r1 ri c1 c2) s := by
    intro c hev hc
    rw [stackSwapPost_iff] at hc ⊢
    rw [hev s rfl rfl]
    have : (fun xs => evaluate (.ite cmp r1 ri c1 c2) { s with stack := xs }) =
        fun xs => evaluate c { s with stack := xs } :=
      funext fun xs => hev _ (hg xs) (hi xs)
    rw [this]
    exact hc
  cases hv : getVar r1 s with
  | none =>
    rw [stackSwapPost_iff, evaluate, hv]
    trivial
  | some x =>
  cases hvi : WordSemStateFiniteExact.getVarImm ri s with
  | none =>
    rw [stackSwapPost_iff, evaluate, hv, hvi]
    trivial
  | some y =>
  cases hc : wordSemWordCmp cmp x y with
  | none =>
    rw [stackSwapPost_iff, evaluate, hv, hvi]
    dsimp only
    rw [hc]
    trivial
  | some b =>
  cases b with
  | true =>
    refine hb c1 (fun t h1 h2 => ?_) (ih1 _ _ x y true ⟨by rw [hv, hvi], rfl, rfl, hc, rfl⟩)
    rw [evaluate, h1, h2, hv, hvi]
    dsimp only
    rw [hc]
  | false =>
    refine hb c2 (fun t h1 h2 => ?_)
      (ih2 _ _ x y false ⟨by rw [hv, hvi], rfl, rfl, hc, Bool.false_ne_true⟩)
    rw [evaluate, h1, h2, hv, hvi]
    dsimp only
    rw [hc]

end WordSemStackEq

end Flapjack
