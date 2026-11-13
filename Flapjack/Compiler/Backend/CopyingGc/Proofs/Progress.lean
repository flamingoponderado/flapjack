module

public import Flapjack.Compiler.Backend.CopyingGc
public import Flapjack.Compiler.Backend.GcShared.ForwardPtr

@[expose] public section

/-! Progress and root-count invariants used by the word-level GC simulation. -/
namespace Flapjack.Compiler.Backend.CopyingGc
open Flapjack

@[hol "cakeml/compiler/backend/gc/copying_gcScript.sml" "gc_move_ok"]
theorem gcMove_ok {α β : Type} (root root' : HeapAddress α)
    (copied copied' heap heap' : List (HeapElement α β)) (a n limit a' n' b : Nat) (ok : Bool)
    (run : gcMove (root, copied, a, n, heap, ok, limit) = (root', copied', a', n', heap', true)) :
    ok = true ∧ (a = b + heapLength copied → a' = b + heapLength copied') := by
  cases root with
  | data d =>
    simp only [gcMove, Prod.mk.injEq] at run
    obtain ⟨_, rfl, rfl, _, _, rfl⟩ := run
    exact ⟨rfl, id⟩
  | pointer ptr d =>
    simp only [gcMove] at run
    cases lookup : heapLookup ptr heap with
    | none => simp [lookup] at run
    | some element =>
      cases element with
      | unused len => simp [lookup] at run
      | forwardPointer addr value len =>
        simp only [lookup, Prod.mk.injEq] at run
        obtain ⟨_, rfl, rfl, _, _, rfl⟩ := run
        exact ⟨rfl, id⟩
      | dataElement xs len payload =>
        simp only [lookup] at run
        cases update : gcForwardPtr ptr heap a d
            (ok && decide (len + 1 ≤ n) && decide (a + n = limit)) with
        | mk updated status =>
          simp only [update, Prod.mk.injEq] at run
          obtain ⟨_, rfl, rfl, _, _, rfl⟩ := run
          have checks := gcForwardPtr_ok heap ptr a d
            (ok && decide (len + 1 ≤ n) && decide (a + n = limit)) updated update
          simp only [Bool.and_eq_true] at checks
          refine ⟨checks.1.1, ?_⟩
          intro h
          simp [heapLength, elLength] at h ⊢
          omega

/-- Root traversal preserves list length even when collection fails. -/
theorem gcMoveList_length {α β : Type} (roots : List (HeapAddress α))
    (copied : List (HeapElement α β)) (a n : Nat) (heap : List (HeapElement α β))
    (ok : Bool) (limit : Nat) :
    (gcMoveList (roots, copied, a, n, heap, ok, limit)).1.length = roots.length := by
  induction roots generalizing copied a n heap ok with
  | nil => simp [gcMoveList]
  | cons root roots ih =>
    simp only [gcMoveList, List.length_cons, ih]

@[hol "cakeml/compiler/backend/gc/copying_gcScript.sml" "gc_move_list_ok"]
theorem gcMoveList_ok {α β γ : Type} (roots roots' : List (HeapAddress α))
    (copied copied' heap heap' : List (HeapElement α β)) (a n limit a' n' b : Nat) (ok : Bool)
    (_unused : γ)
    (run : gcMoveList (roots, copied, a, n, heap, ok, limit) = (roots', copied', a', n', heap', true)) :
    ok = true ∧ (a = b + heapLength copied → a' = b + heapLength copied') := by
  induction roots generalizing roots' copied copied' heap heap' a n a' n' ok with
  | nil =>
    simp only [gcMoveList, Prod.mk.injEq] at run
    obtain ⟨_, rfl, rfl, _, _, rfl⟩ := run
    exact ⟨rfl, id⟩
  | cons root roots ih =>
    simp only [gcMoveList] at run
    cases move : gcMove (root, copied, a, n, heap, ok, limit) with
    | mk root1 rest =>
      rcases rest with ⟨copied1, a1, n1, heap1, ok1⟩
      simp only [move] at run
      cases tail : gcMoveList (roots, copied1, a1, n1, heap1, ok1, limit) with
      | mk roots1 rest =>
        rcases rest with ⟨copied2, a2, n2, heap2, ok2⟩
        simp only [tail, Prod.mk.injEq] at run
        obtain ⟨_, rfl, rfl, rfl, rfl, rfl⟩ := run
        have tailOk := ih roots1 copied1 copied2 heap1 heap2 a1 n1 a2 n2 ok1 tail
        have moveTrue : gcMove (root, copied, a, n, heap, ok, limit) =
            (root1, copied1, a1, n1, heap1, true) := by simpa [tailOk.1] using move
        have headOk := gcMove_ok root root1 copied copied1 heap heap1 a n limit a1 n1 b ok moveTrue
        exact ⟨headOk.1, fun h => tailOk.2 (headOk.2 h)⟩

/-- A successful abstract scan started with a successful status. -/
@[hol "cakeml/compiler/backend/gc/copying_gcScript.sml" "gc_move_loop_ok"]
theorem gcMoveLoop_ok {α β : Type} (scanned pending heap resultHeap : List (HeapElement α β))
    (a n limit resultA resultN : Nat) (ok : Bool)
    (result : List (HeapElement α β))
    (run : gcMoveLoop (scanned, pending, a, n, heap, ok, limit) =
      (result, resultA, resultN, resultHeap, true)) : ok = true := by
  have invariant : ∀ input : List (HeapElement α β) × List (HeapElement α β) × Nat × Nat ×
      List (HeapElement α β) × Bool × Nat,
      (gcMoveLoop input).2.2.2.2 = true → input.2.2.2.2.2.1 = true := by
    intro input
    induction input using gcMoveLoop.induct with
    | case1 scanned a n heap ok limit => simp [gcMoveLoop]
    | case2 scanned h pending a n heap ok limit overflow => cases h <;> simp [gcMoveLoop, overflow]
    | case3 scanned pending a n heap ok limit xs len payload roots copied a1 n1 heap1 ok1 bound move ok2 ih =>
      simp only [gcMoveLoop, ite_eq_right bound, move]
      intro successful
      have copiedEq : (gcMoveList (xs, .dataElement xs len payload :: pending, a, n, heap, ok, limit)).2.1 = copied := by
        rw [move]
      rw [copiedEq] at successful
      have status := ih successful
      dsimp only [ok2] at status
      simp only [Bool.and_eq_true] at status
      have moveTrue : gcMoveList (xs, .dataElement xs len payload :: pending, a, n, heap, ok, limit) =
          (roots, copied, a1, n1, heap1, true) := by simpa [status.1.1] using move
      exact (gcMoveList_ok xs roots (.dataElement xs len payload :: pending) copied heap heap1
        a n limit a1 n1 0 ok () moveTrue).1
    | case4 scanned h pending a n heap ok limit bound notData =>
      cases h <;> simp_all [gcMoveLoop]
  have status := invariant (scanned, pending, a, n, heap, ok, limit)
  simp only [run] at status
  exact status trivial

@[hol "cakeml/compiler/backend/gc/copying_gcScript.sml" "gc_move_list_IMP_LENGTH"]
theorem gcMoveList_imp_length {α β : Type} (roots result : List (HeapAddress α))
    (copied copied' heap heap' : List (HeapElement α β)) (a n limit a' n' : Nat) (ok ok' : Bool)
    (run : gcMoveList (roots, copied, a, n, heap, ok, limit) = (result, copied', a', n', heap', ok')) :
    result.length = roots.length := by
  have length := gcMoveList_length roots copied a n heap ok limit
  simpa only [run] using length

@[hol "cakeml/compiler/backend/gc/copying_gcScript.sml" "full_gc_IMP_LENGTH"]
theorem fullGc_imp_length {α β : Type} (roots result : List (HeapAddress α))
    (heap heap' : List (HeapElement α β)) (limit a : Nat)
    (run : fullGc (roots, heap, limit) = (result, heap', a, true)) : result.length = roots.length := by
  have length := gcMoveList_length roots ([] : List (HeapElement α β)) 0 limit heap true limit
  simp only [fullGc, Prod.mk.injEq] at run
  rcases run with ⟨rfl, _⟩
  exact length

end Flapjack.Compiler.Backend.CopyingGc
