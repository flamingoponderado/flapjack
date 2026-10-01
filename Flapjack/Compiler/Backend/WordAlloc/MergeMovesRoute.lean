import Flapjack.Compiler.Backend.WordAlloc.SSAMergeMoves

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Executed association-list boundary for the reviewed native merge_moves.
First-match encoding preserves duplicate keys. Decoding uses the native tree
traversal; clients observe maps by lookup, rather than list storage order.
This codec has no independent HOL original and is intentionally untagged. -/
def mergeMovesExecutable (names : List Nat) (left right : List (Nat × Nat)) (next : Nat) :
    List (Nat × Nat) × List (Nat × Nat) × Nat × List (Nat × Nat) × List (Nat × Nat) :=
  let (leftMoves,rightMoves,next,left,right) :=
    mergeMoves names (sptFromAList left) (sptFromAList right) next
  (leftMoves,rightMoves,next,sptToAList left,sptToAList right)

/-- Unconditional input-codec law, including duplicate association keys. -/
theorem mergeMovesInputLookup (entries : List (Nat × Nat)) (key : Nat) :
    sptLookup key (sptFromAList entries) = sptAListLookup key entries :=
  sptLookup_sptFromAList key entries

/-- Whole native result observations are preserved: both ordered move lists,
the unbounded fresh counter, and both maps at every key. This is an executed
codec law, not the SSA simulation theorem or an invented tagged HOL port. -/
theorem mergeMovesExecutableCorresponds (names : List Nat)
    (left right : List (Nat × Nat)) (next : Nat) :
    let native := mergeMoves names (sptFromAList left) (sptFromAList right) next
    let executed := mergeMovesExecutable names left right next
    executed.1 = native.1 ∧ executed.2.1 = native.2.1 ∧
    executed.2.2.1 = native.2.2.1 ∧
    (∀ key, sptAListLookup key executed.2.2.2.1 = sptLookup key native.2.2.2.1) ∧
    (∀ key, sptAListLookup key executed.2.2.2.2 = sptLookup key native.2.2.2.2) := by
  unfold mergeMovesExecutable
  obtain ⟨lm,rm,n,l,r⟩ := mergeMoves names (sptFromAList left) (sptFromAList right) next
  simp only
  refine ⟨True.intro,True.intro,True.intro,?_,?_⟩
  · intro key
    simpa only [sptLookup_sptFromAList] using sptLookup_sptFromAList_sptToAList key l
  · intro key
    simpa only [sptLookup_sptFromAList] using sptLookup_sptFromAList_sptToAList key r
end Flapjack.Compiler.Backend.WordAlloc
