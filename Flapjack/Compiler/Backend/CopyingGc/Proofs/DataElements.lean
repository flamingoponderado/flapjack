module

public import Flapjack.Compiler.Backend.CopyingGc.Proofs.Progress
public import Mathlib.Data.List.Forall2

@[expose] public section

/-! Copied and scanned heaps contain only data elements. -/
namespace Flapjack.Compiler.Backend.CopyingGc
open Flapjack

@[hol "cakeml/compiler/backend/gc/copying_gcScript.sml" "gc_move_IMP_isDataElement"]
theorem gcMove_imp_isDataElement {α β : Type} (root root' : HeapAddress α)
    (copied copied' heap heap' : List (HeapElement α β)) (a n limit a' n' : Nat) (ok ok' : Bool)
    (data : ∀ element ∈ copied, isDataElement element)
    (run : gcMove (root, copied, a, n, heap, ok, limit) = (root', copied', a', n', heap', ok')) :
    ∀ element ∈ copied', isDataElement element := by
  cases root with
  | data d =>
    simp only [gcMove, Prod.mk.injEq] at run
    obtain ⟨_, rfl, _⟩ := run
    exact data
  | pointer ptr d =>
    simp only [gcMove] at run
    cases lookup : heapLookup ptr heap with
    | none =>
      simp only [lookup, Prod.mk.injEq] at run
      obtain ⟨_, rfl, _⟩ := run
      exact data
    | some element =>
      cases element with
      | unused len =>
        simp only [lookup, Prod.mk.injEq] at run
        obtain ⟨_, rfl, _⟩ := run
        exact data
      | forwardPointer addr value len =>
        simp only [lookup, Prod.mk.injEq] at run
        obtain ⟨_, rfl, _⟩ := run
        exact data
      | dataElement xs len payload =>
        simp only [lookup] at run
        cases update : gcForwardPtr ptr heap a d
            (ok && decide (len + 1 ≤ n) && decide (a + n = limit)) with
        | mk updated status =>
          simp only [update, Prod.mk.injEq] at run
          obtain ⟨_, rfl, _⟩ := run
          intro element member
          simp only [List.mem_append, List.mem_singleton] at member
          rcases member with member | rfl
          · exact data element member
          · exact ⟨xs, len, payload, rfl⟩

@[hol "cakeml/compiler/backend/gc/copying_gcScript.sml" "gc_move_list_IMP_isDataElement"]
theorem gcMoveList_imp_isDataElement {α β : Type} (roots roots' : List (HeapAddress α))
    (copied copied' heap heap' : List (HeapElement α β)) (a n limit a' n' : Nat) (ok ok' : Bool)
    (data : ∀ element ∈ copied, isDataElement element)
    (run : gcMoveList (roots, copied, a, n, heap, ok, limit) = (roots', copied', a', n', heap', ok')) :
    ∀ element ∈ copied', isDataElement element := by
  induction roots generalizing roots' copied copied' heap heap' a n a' n' ok ok' with
  | nil =>
    simp only [gcMoveList, Prod.mk.injEq] at run
    obtain ⟨_, rfl, _⟩ := run
    exact data
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
        have copiedData := gcMove_imp_isDataElement root root1 copied copied1 heap heap1
          a n limit a1 n1 ok ok1 data move
        exact ih roots1 copied1 copied2 heap1 heap2 a1 n1 a2 n2 ok1 ok2 copiedData tail

@[hol "cakeml/compiler/backend/gc/copying_gcScript.sml" "gc_move_loop_IMP_isDataElement"]
theorem gcMoveLoop_imp_isDataElement {α β γ : Type}
    (scanned pending heap resultHeap : List (HeapElement α β)) (a n limit resultA resultN : Nat)
    (ok : Bool) (result : List (HeapElement α β)) (_unused : γ)
    (scannedData : ∀ element ∈ scanned, isDataElement element)
    (pendingData : ∀ element ∈ pending, isDataElement element)
    (run : gcMoveLoop (scanned, pending, a, n, heap, ok, limit) =
      (result, resultA, resultN, resultHeap, true)) :
    ∀ element ∈ result, isDataElement element := by
  have invariant : ∀ input : List (HeapElement α β) × List (HeapElement α β) × Nat × Nat ×
      List (HeapElement α β) × Bool × Nat,
      (∀ element ∈ input.1, isDataElement element) →
      (∀ element ∈ input.2.1, isDataElement element) →
      (gcMoveLoop input).2.2.2.2 = true →
      ∀ element ∈ (gcMoveLoop input).1, isDataElement element := by
    intro input
    induction input using gcMoveLoop.induct with
    | case1 scanned a n heap ok limit =>
      simp only [gcMoveLoop]
      intro valid _ _
      exact valid
    | case2 scanned h pending a n heap ok limit overflow =>
      cases h <;> simp [gcMoveLoop, overflow]
    | case3 scanned pending a n heap ok limit xs len payload roots copied a1 n1 heap1 ok1 bound move ok2 ih =>
      intro scannedData pendingData
      simp only [gcMoveLoop, ite_eq_right bound, move]
      intro successful
      have copiedEq : (gcMoveList (xs, .dataElement xs len payload :: pending, a, n, heap, ok, limit)).2.1 = copied := by
        rw [move]
      rw [copiedEq] at successful ⊢
      have copiedData := gcMoveList_imp_isDataElement xs roots (.dataElement xs len payload :: pending)
        copied heap heap1 a n limit a1 n1 ok ok1 pendingData move
      have newScanned : ∀ element ∈ scanned ++ [.dataElement roots len payload], isDataElement element := by
        intro element member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with member | rfl
        · exact scannedData element member
        · exact ⟨roots, len, payload, rfl⟩
      have newPending : ∀ element ∈ copied.drop 1, isDataElement element := by
        intro element member
        exact copiedData element (List.mem_of_mem_drop member)
      exact ih newScanned newPending successful
    | case4 scanned h pending a n heap ok limit bound notData =>
      cases h <;> simp_all [gcMoveLoop]
  have valid := invariant (scanned, pending, a, n, heap, ok, limit) scannedData pendingData
  simp only [run] at valid
  exact valid trivial

@[hol "cakeml/compiler/backend/gc/copying_gcScript.sml" "full_gc_IMP_isDataElement"]
theorem fullGc_imp_isDataElement {α β : Type} (roots roots' : List (HeapAddress α))
    (heap heap' : List (HeapElement α β)) (limit a : Nat)
    (run : fullGc (roots, heap, limit) = (roots', heap', a, true)) :
    ∀ element ∈ heap', isDataElement element := by
  simp only [fullGc] at run
  cases move : gcMoveList (roots, ([] : List (HeapElement α β)), 0, limit, heap, true, limit) with
  | mk moved rest =>
    rcases rest with ⟨pending, a1, n1, heap1, ok1⟩
    simp only [move] at run
    cases scan : gcMoveLoop ([], pending, a1, n1, heap1, ok1, limit) with
    | mk scanned rest =>
      rcases rest with ⟨a2, n2, heap2, ok2⟩
      simp only [scan, Prod.mk.injEq] at run
      obtain ⟨_, rfl, rfl, checks⟩ := run
      simp only [Bool.and_eq_true] at checks
      have scanTrue : gcMoveLoop ([], pending, a1, n1, heap1, ok1, limit) =
          (scanned, a2, n2, heap2, true) := by simpa [checks.1.1.1.1.1] using scan
      have pendingData := gcMoveList_imp_isDataElement roots moved [] pending heap heap1
        0 limit limit a1 n1 true ok1 (by simp) move
      exact gcMoveLoop_imp_isDataElement [] pending heap1 heap2 a1 n1 limit a2 n2 ok1 scanned ()
        (by simp) pendingData scanTrue

end Flapjack.Compiler.Backend.CopyingGc
