import Flapjack.Pancake.Semantics.LoopProps.CutSets

namespace Flapjack

noncomputable section

local instance classicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- HOL booleans may contain non-computable existential tests. This
    Flapjack-specific embedding maps a Prop truth value to Bool; it has no
    separate HOL declaration and makes no executable-evaluation claim. -/
noncomputable def holPropBool (p : Prop) : Bool := if p then true else false

/-!
# Exact compiler-syntax predicate from loopProps

Counterpart of `cakeml/pancake/semantics/loopPropsScript.sml:57-73` over the
width-indexed `HolLoopProg` and tree-backed `NumSet`. The `If` clause retains
HOL's existential list extension exactly; it is represented as a Lean `Bool`
through `holPropBool`. Consequently Lean's direct replay keeps
the same residual existential that HOL `EVAL` leaves for `If` cases. This is a
proof-side definition: no claim is made that production optimization calls it.
-/

/-- Exact HOL `comp_syntax_ok_def`. In particular, `Seq` checks the second
    statement under `cutSetsHOL live first`; `Loop` requires both live-set
    equalities; and `If` preserves the existential `FOLDL insert` extension. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "comp_syntax_ok_def"
  (words_as_type_indexed_bitvec)]
noncomputable def compSyntaxOkHOL {width : Nat} [NeZero width]
    (live : NumSet) : HolLoopProg width → Bool
  | .skip => true
  | .assign _ _ => true
  | .loop liveIn body liveOut =>
      decide (live = liveIn) && decide (live = liveOut) &&
        compSyntaxOkHOL liveIn body
  | .arith _ => true
  | .break _ => true
  | .locValue _ _ => true
  | .load32 _ _ => true
  | .loadByte _ _ => true
  | .seq first second =>
      compSyntaxOkHOL live first &&
        compSyntaxOkHOL (cutSetsHOL live first) second
  | .ite _ _ _ thenBranch elseBranch nextLive =>
      compSyntaxOkHOL live thenBranch &&
        compSyntaxOkHOL live elseBranch &&
        holPropBool (∃ names : List Nat,
          nextLive = sptListInsert names live)
  | _ => false
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

end

end Flapjack
