import Flapjack.Compiler.Backend.WordAlloc.HeuCounters
import Flapjack.Misc.Sptree.Mapi

namespace Flapjack.WordAlloc

/-- Literal componentwise maximum of the five natural heuristic counters. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "heu_max_def"]
def heuMax (left right : HeuData) : HeuData :=
  let (c1, r1, m1, rr1, rm1) := left
  let (c2, r2, m2, rr2, rm2) := right
  (max c1 c2, max r1 r2, max m1 m2, max rr1 rr2, max rm1 rm2)

/-- Literal branch-counter join. The left-only remainder is unioned with an
indexed map of the right tree; overlapping values use right then left operands.
Raw tree behavior is retained, including the difference between an untouched
left tree and the smart-constructor normalization of the mapped right tree.
No well-formedness premise is added. Executed allocator routing remains open. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "heu_max_all_def"]
def heuMaxAll (left right : Spt HeuData) : Spt HeuData :=
  let remainder := sptDifference left right
  sptUnion remainder (sptMapi (fun key value =>
    match sptLookup key left with
    | none => value
    | some other => heuMax value other) right)

end Flapjack.WordAlloc
