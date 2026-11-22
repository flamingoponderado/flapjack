module

public import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

@[expose] public section

/-!
# HOL `evaluate_Loop_body_same`

Exact port of `cakeml/pancake/semantics/loopPropsScript.sml:112-133` over the
faithful `HolLoopProg` and `LoopSemStateFiniteExact` carriers: replacing the
body of a `Loop` with a program that behaves identically on every state leaves
the loop's evaluation unchanged.  HOL proves it by complete induction on
`s.clock`; the Lean proof uses the same clock-lexicographic induction as the
other exact evaluator lemmas, with the recursive calls discharged by the
induction hypothesis at the strictly smaller clock produced by `cut_res`'s
`dec_clock`.
-/

namespace Flapjack

namespace LoopSemStateFiniteExact

variable {width : Nat} [NeZero width] {F : Type}

namespace LoopBodySameFiniteSupport

/-- Local same-module witness for the canonical finite-support
`LoopSemStateFiniteExact` carrier used by the `fmap_as_finite_support := [globals]`
qualified port in this module (re-exports the checked witness of
`Flapjack/Pancake/Semantics/LoopSemStateExact.lean`). -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

end LoopBodySameFiniteSupport

/-- Exact port of HOL `loopProps$evaluate_Loop_body_same`
    (`cakeml/pancake/semantics/loopPropsScript.sml:112-133`):
    `(∀s. evaluate (body,s) = evaluate (body',s)) ⇒
     ∀s. evaluate (Loop l1 body l2,s) = evaluate (Loop l1 body' l2,s)`.
    The binders follow the captured free-variable order
    (`evaluate_Loop_body_same_vars=l2,l1,body',body`), `Loop` is
    `HolLoopProg.loop`, `evaluate` is the tagged exact evaluator, `cut_res` is
    `cutRes` and `fix_clock` is `fixClock`.  The induction is on the same
    clock-lexicographic measure HOL's `completeInduct_on s.clock` uses; the
    two recursive `Loop` clauses are discharged at the state `cut_res` has
    already decremented. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "evaluate_Loop_body_same"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluate_Loop_body_same (liveOut : NumSet) (liveIn : NumSet)
    (body' : HolLoopProg width) (body : HolLoopProg width)
    (hbody : ∀ s : LoopSemStateFiniteExact width F, evaluate body s = evaluate body' s) :
    ∀ s : LoopSemStateFiniteExact width F,
      evaluate (.loop liveIn body liveOut) s = evaluate (.loop liveIn body' liveOut) s := by
  have key : ∀ (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F),
      p = HolLoopProg.loop liveIn body liveOut →
        evaluate p s = evaluate (HolLoopProg.loop liveIn body' liveOut) s := by
    refine clockSizeLexInduction (α := HolLoopProg width) (·.clock) (motive := fun p s =>
      p = HolLoopProg.loop liveIn body liveOut →
        evaluate p s = evaluate (HolLoopProg.loop liveIn body' liveOut) s) ?_
    intro p s ih hp
    subst hp
    rw [evaluate, evaluate]
    split
    · rename_i s1 hcut
      rw [hbody s1]
      split
      · rename_i s2 hfix
        exact ih (.loop liveIn body liveOut) s2
          (lexLtClock (by
            have hdec := cutRes_none_clock hcut
            have hle := fixClock_eq_clock_le hfix
            omega)) rfl
      · rename_i s2 hfix
        exact ih (.loop liveIn body liveOut) s2
          (lexLtClock (by
            have hdec := cutRes_none_clock hcut
            have hle := fixClock_eq_clock_le hfix
            omega)) rfl
      · rfl
      · rfl
    · rfl
  intro s
  exact key (.loop liveIn body liveOut) s rfl

end LoopSemStateFiniteExact
end Flapjack
