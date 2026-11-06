import Flapjack.Compiler.Backend.CopyingGc

/-! Prefix independence of the abstract collector's copied heap. -/
namespace Flapjack.Compiler.Backend.CopyingGc
open Flapjack Flapjack.Compiler.Backend

/-- Moving one address appends the newly copied cells to the input prefix. -/
@[hol "cakeml/compiler/backend/gc/copying_gcScript.sml" "gc_move_ALT"]
theorem gcMove_alt {α β : Type} (root : HeapAddress α) (copied : List (HeapElement α β))
    (a n : Nat) (heap : List (HeapElement α β)) (ok : Bool) (limit : Nat) :
    gcMove (root, copied, a, n, heap, ok, limit) =
      (let (root', added, a', n', heap', ok') := gcMove (root, [], a, n, heap, ok, limit)
       (root', copied ++ added, a', n', heap', ok')) := by
  cases root with
  | data value => simp [gcMove]
  | pointer ptr value =>
    cases found : heapLookup ptr heap with
    | none => simp [gcMove, found]
    | some element =>
      cases element with
      | unused len => simp [gcMove, found]
      | forwardPointer ptr' value' len => simp [gcMove, found]
      | dataElement roots len data =>
        simp only [gcMove, found, List.nil_append]

/-- Moving any list of roots leaves an existing copied-heap prefix intact. -/
@[hol "cakeml/compiler/backend/gc/copying_gcScript.sml" "gc_move_list_ALT"]
theorem gcMoveList_alt {α β γ δ ε ζ η θ : Type}
    (roots : List (HeapAddress α)) (copied : List (HeapElement α β))
    (a n : Nat) (heap : List (HeapElement α β)) (ok : Bool) (limit : Nat)
    (_ys3 : γ) (_xs3 : δ) (_a3 : ε) (_n3 : ζ) (_heap3 : η) (_c3 : θ) :
    gcMoveList (roots, copied, a, n, heap, ok, limit) =
      (let (roots', added, a', n', heap', ok') := gcMoveList (roots, [], a, n, heap, ok, limit)
       (roots', copied ++ added, a', n', heap', ok')) := by
  induction roots generalizing copied a n heap ok with
  | nil => simp [gcMoveList]
  | cons root roots ih =>
    simp only [gcMoveList]
    rw [gcMove_alt root copied]
    cases moved : gcMove (root, [], a, n, heap, ok, limit) with
    | mk root1 rest =>
      rcases rest with ⟨added, a1, n1, heap1, ok1⟩
      rw [ih (copied ++ added), ih added]
      cases tail : gcMoveList (roots, [], a1, n1, heap1, ok1, limit) with
      | mk roots1 rest =>
        rcases rest with ⟨added1, a2, n2, heap2, ok2⟩
        simp only [List.append_assoc]

end Flapjack.Compiler.Backend.CopyingGc
