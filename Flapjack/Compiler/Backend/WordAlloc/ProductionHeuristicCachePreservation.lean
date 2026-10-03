import Flapjack.Compiler.Backend.WordAlloc.ProductionCallCache

namespace Flapjack.WordAlloc
open RiscV

/-! Full actual heuristic traversal preserves the cache mirror used by the
executed accelerator. This invariant has no separate HOL original: the native
analysis has no redundant TreeSet cache. It is established from the input
cache invariant and remains valid for every actual program, without assuming
an encoder accepts it or supplying a post-traversal invariant. -/

theorem heuristicCache_preserved (functionName : Nat) (program : WordProg α)
    (counts : WordHeuristicCountMap) (calls : WordHeuristicCallSet)
    (valid : StackCacheRep calls.names calls.seen) :
    StackCacheRep (wordHeuristicFast functionName program (counts, calls)).2.names
      (wordHeuristicFast functionName program (counts, calls)).2.seen := by
  cases program
  all_goals try simpa only [wordHeuristicFast] using valid
  case set store expression =>
    cases expression <;> simpa only [wordHeuristicFast] using valid
  case shareInst operator name address =>
    cases operator <;> simpa only [wordHeuristicFast] using valid
  case mustTerminate body =>
    simpa only [wordHeuristicFast] using heuristicCache_preserved functionName body counts calls valid
  case loop names body exits =>
    simpa only [wordHeuristicFast] using heuristicCache_preserved functionName body counts calls valid
  case seq first second =>
    simpa only [wordHeuristicFast, Prod.eta] using
      heuristicCache_preserved functionName second
        (wordHeuristicFast functionName first (counts, calls)).1
        (wordHeuristicFast functionName first (counts, calls)).2
        (heuristicCache_preserved functionName first counts calls valid)
  case ite compare condition right yes no =>
    have joined := (callCache_merge
      (wordHeuristicFast functionName yes (counts, calls)).2
      (wordHeuristicFast functionName no (counts, calls)).2.names
      (heuristicCache_preserved functionName yes counts calls valid)).2
    cases right <;> simpa only [wordHeuristicFast] using joined
  case call returns target arguments handler =>
    let incoming := match target with
      | some name => if name = functionName then calls.addCall counts else calls
      | none => calls
    have incomingValid : StackCacheRep incoming.names incoming.seen := by
      cases target with
      | none => exact valid
      | some name =>
          by_cases same : name = functionName
          · simpa only [incoming, same, if_true, WordHeuristicCallSet.addCall] using
              (callCache_merge calls counts.keys valid).2
          · simpa only [incoming, same, if_false] using valid
    cases returns with
    | none =>
        cases target with
        | none => simpa only [wordHeuristicFast] using valid
        | some name =>
            by_cases same : name = functionName <;>
              simpa only [wordHeuristicFast, incoming, same, if_true, if_false] using incomingValid
    | some returning =>
        rcases returning with ⟨values, sets, body, label1, label2⟩
        cases handler with
        | none =>
            cases target with
            | none => simpa only [wordHeuristicFast] using valid
            | some name =>
                by_cases same : name = functionName <;>
                  simpa only [wordHeuristicFast, incoming, same, if_true, if_false] using incomingValid
        | some exception =>
            rcases exception with ⟨name, exceptionBody, handler1, handler2⟩
            have merged := (callCache_merge
              (wordHeuristicFast functionName body (counts, incoming)).2
              (wordHeuristicFast functionName exceptionBody (counts, incoming)).2.names
              (heuristicCache_preserved functionName body counts incoming incomingValid)).2
            cases target with
            | none => simpa only [wordHeuristicFast, incoming] using merged
            | some name =>
                by_cases same : name = functionName <;>
                  simpa only [wordHeuristicFast, incoming, same, if_true, if_false] using merged
termination_by sizeOf program
decreasing_by all_goals decreasing_trivial

end Flapjack.WordAlloc
