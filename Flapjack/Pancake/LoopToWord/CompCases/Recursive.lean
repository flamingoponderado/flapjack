import Flapjack.Pancake.LoopToWord

/-!
# Recursive constructor cases of `loop_to_word$comp`

This is a HOL-native case slice for `cakeml/pancake/loop_to_wordScript.sml`.
It ports the recursive `Seq`, `If`, `Loop`, and `Mark` clauses of `comp_def`
(lines 107-120 and 138), and the `Call` clauses (lines 145-166), over
`HolLoopProg` and `WordLangProgHOL`. It delegates
covered leaves to `compInitialHOL`, so `none` means a leaf constructor is not
yet in the assembled partial port. This intentionally remains untagged; it is a
superseded partial slice helper, not a HOL port. The reviewed total port of
`comp_def` is the tagged `compHOL` in `Flapjack/Pancake/LoopToWord.lean`.

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
  | .call returns target arguments handler =>
      let mappedArguments := arguments.map (findVarHOL context)
      match returns with
      | none =>
          some (.call none target (0 :: mappedArguments) none, labels)
      | some (vs, live) =>
          let mappedReturns := vs.map (findVarHOL context)
          let cutset := mkNewCutsetHOL context live
          let newLabels := (labels.1, labels.2 + 1)
          match handler with
          | none =>
              some (.call (some (mappedReturns, (cutset, .ln), .skip, labels))
                target mappedArguments none, newLabels)
          | some (n, p1, p2, _) =>
              match compRecursiveCasesHOL context newLabels p1 with
              | none => none
              | some (wordP1, labels1) =>
                  match compRecursiveCasesHOL context labels1 p2 with
                  | none => none
                  | some (wordP2, labels2) =>
                      let finalLabels := (labels2.1, labels2.2 + 1)
                      some (.seq
                        (.call (some (mappedReturns, (cutset, .ln), wordP2, labels))
                          target mappedArguments
                          (some (findVarHOL context n, wordP1, labels2)))
                        .tick, finalLabels)
  | program => compInitialHOL context labels program
  termination_by program => sizeOf program
  decreasing_by all_goals decreasing_trivial

end Flapjack.LoopToWord
