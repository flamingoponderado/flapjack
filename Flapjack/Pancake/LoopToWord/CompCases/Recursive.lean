import Flapjack.Pancake.LoopToWord

/-!
# Recursive constructor cases of `loop_to_word$comp`

This is a HOL-native case slice for `cakeml/pancake/loop_to_wordScript.sml`.
It ports the recursive `Seq`, `If`, `Loop`, and `Mark` clauses of `comp_def`
(lines 107-120 and 138) over `HolLoopProg` and `WordLangProgHOL`. It delegates
covered leaves to `compInitialHOL`, so `none` means a leaf constructor is not
yet in the assembled partial port. This intentionally remains untagged and
does not claim to define total HOL `comp`; the later clause slices must be
assembled before that tag is appropriate.

The source clauses compile `Seq` children left-to-right while threading the
label pair, compile `If` branches in the same order before appending `Tick`,
wrap a compiled `Loop` body as `Seq Tick (Seq Loop Tick)`, and erase `Mark`.
The definitions below preserve those outputs, including the exact live-set
carrier and the ignored `If`/`Loop` annotations.
-/

namespace Flapjack.LoopToWord

/-- Partial, exact case slice for the recursive constructors of HOL
`loop_to_word$comp_def`. Recursive children must be supported by an existing
case slice; unsupported leaves propagate `none`. -/
def compRecursiveCasesHOL {width : Nat} [NeZero width] (context : Spt Nat)
    (labels : Nat × Nat) : HolLoopProg width →
      Option (WordLangProgHOL (BitVec width) × (Nat × Nat))
  | .seq first second =>
      match compRecursiveCasesHOL context labels first with
      | none => none
      | some (wordFirst, labels') =>
          match compRecursiveCasesHOL context labels' second with
          | none => none
          | some (wordSecond, labels'') =>
              some (.seq wordFirst wordSecond, labels'')
  | .ite operator condition right thenBranch elseBranch _ =>
      match compRecursiveCasesHOL context labels thenBranch with
          | none => none
          | some (wordThen, labels') =>
          match compRecursiveCasesHOL context labels' elseBranch with
          | none => none
          | some (wordElse, labels'') =>
              some (.seq
                (.ite operator (findVarHOL context condition)
                  (match right with
                   | .imm value => .imm value
                   | .reg name => .reg (findVarHOL context name))
                  wordThen wordElse)
                .tick, labels'')
  | .loop liveIn body liveOut =>
      match compRecursiveCasesHOL context labels body with
      | none => none
      | some (wordBody, labels') =>
          some (.seq .tick
            (.seq (.loop (mkNewCutsetHOL context liveIn) wordBody
              (mkNewCutsetHOL context liveOut)) .tick), labels')
  | .mark body => compRecursiveCasesHOL context labels body
  | program => compInitialHOL context labels program
  termination_by program => sizeOf program
  decreasing_by all_goals decreasing_trivial

end Flapjack.LoopToWord
