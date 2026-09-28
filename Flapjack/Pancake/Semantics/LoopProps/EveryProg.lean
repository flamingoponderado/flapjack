import Flapjack.Pancake.Semantics.LoopProps

namespace Flapjack

/-- Exact HOL `loopProps$every_prog_def` over the faithful width-indexed
    `HolLoopProg` and `NumSet = Spt Unit` carriers. HOL
    (`cakeml/pancake/semantics/loopPropsScript.sml:10-24`) is a mutual
    `Definition` whose clauses are:

    * `Seq p1 p2` holds when `p (Seq p1 p2)` and both branches hold;
    * `Loop l1 body l2` holds when `p (Loop l1 body l2)` and the body holds;
    * `If x1 x2 x3 p1 p2 l1` holds when `p (If …)` and both branches hold;
    * `Mark p1` holds when `p (Mark p1)` and `p1` holds;
    * `Call ret dest args handler` holds when `p (Call …)` and, for
      `handler = SOME (n, q, r, l)`, both `q` and `r` hold (`NONE` contributes
      `T`);
    * every other program satisfies exactly `p prog`.

    This is a `Prop`-valued combinator, so the HOL boolean result is rendered
    as a `Prop`; the only carrier translation is HOL's positive word dimension
    to `BitVec width`. It is used by `crep_to_loopProofScript.sml:575` in the
    `ncompile_correct` proof. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "every_prog_def"
  (words_as_type_indexed_bitvec)]
def everyProgHOL {width : Nat} [NeZero width]
    (predicate : HolLoopProg width → Prop) : HolLoopProg width → Prop
  | .seq first second =>
      predicate (.seq first second) ∧ everyProgHOL predicate first ∧
        everyProgHOL predicate second
  | .loop liveIn body liveOut =>
      predicate (.loop liveIn body liveOut) ∧ everyProgHOL predicate body
  | .ite operator condition right thenBranch elseBranch live =>
      predicate (.ite operator condition right thenBranch elseBranch live) ∧
        everyProgHOL predicate thenBranch ∧ everyProgHOL predicate elseBranch
  | .mark body =>
      predicate (.mark body) ∧ everyProgHOL predicate body
  | .call returns target arguments handler =>
      predicate (.call returns target arguments handler) ∧
        (match handler with
         | some (_, first, second, _) =>
             everyProgHOL predicate first ∧ everyProgHOL predicate second
         | none => True)
  | program => predicate program
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

end Flapjack