module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.HeapPointerSizes

@[expose] public section

/-! Heap traversal and the collector reachability graph. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend

/-- Traverse data and pointer roots, recording addresses as they are visited. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "traverse_heap"]
inductive traverseHeap {α β : Type} (heap : List (HeapElement α β)) :
    List Nat → List (HeapAddress α) → List Nat → Prop where
  | empty (visited) : traverseHeap heap visited [] visited
  | append {before middle after : List Nat} {first second vars : List (HeapAddress α)} :
      traverseHeap heap before first middle → traverseHeap heap middle second after →
      ({v | v ∈ vars} : Set (HeapAddress α)) = {v | v ∈ first ++ second} →
      traverseHeap heap before vars after
  | data (visited value) : traverseHeap heap visited [.data value] visited
  | seen (visited ptr value) : ptr ∈ visited → traverseHeap heap visited [.pointer ptr value] visited
  | visit {visited after : List Nat} {ptr len : Nat} {value : α} {children : List (HeapAddress α)} {payload : β} :
      heapLookup ptr heap = some (.dataElement children len payload) →
      traverseHeap heap (ptr :: visited) children after → traverseHeap heap visited [.pointer ptr value] after

/-- Traversal never removes previously visited addresses. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "traverse_heap_reachable_set_mono"]
theorem traverseHeap_visited_mono {α β : Type} (heap : List (HeapElement α β))
    (before : List Nat) (roots : List (HeapAddress α)) (after : List Nat)
    (run : traverseHeap heap before roots after) :
    ({ptr | ptr ∈ before} : Set Nat) ⊆ {ptr | ptr ∈ after} := by
  induction run with
  | empty => exact fun _ member => member
  | append first second _ ih1 ih2 => exact fun _ member => ih2 (ih1 member)
  | data => exact fun _ member => member
  | seen => exact fun _ member => member
  | visit found traverse ih => exact fun _ member => ih (List.mem_cons_of_mem _ member)

/-- Flapjack infrastructure: a curried form of traversal edge closure. -/
theorem traverseHeap_reachable_aux {α β : Type} (heap : List (HeapElement α β))
    (before : List Nat) (roots : List (HeapAddress α)) (after : List Nat)
    (run : traverseHeap heap before roots after) (remaining : List (HeapAddress α))
    (closed : ∀ y z, y ∈ before → gcEdge heap y z →
      z ∈ before ∨ ∃ value, .pointer z value ∈ roots ++ remaining) :
    (∀ ptr ∈ before, ptr ∈ after) ∧
    (∀ y value, .pointer y value ∈ roots → y ∈ after ∨ ∃ value, .pointer y value ∈ remaining) ∧
    (∀ y z, y ∈ after → gcEdge heap y z → z ∈ after ∨ ∃ value, .pointer z value ∈ remaining) := by
  induction run generalizing remaining with
  | empty visited =>
    refine ⟨fun _ member => member, ?_, ?_⟩
    · simp
    · simpa using closed
  | @append before middle after first second vars firstRun secondRun same ih1 ih2 =>
    have membership : ∀ v, v ∈ vars ↔ v ∈ first ++ second := fun v => Iff.of_eq (congrFun same v)
    have firstClosed : ∀ y z, y ∈ before → gcEdge heap y z →
        z ∈ before ∨ ∃ value, .pointer z value ∈ first ++ (second ++ remaining) := by
      intro y z member edge
      rcases closed y z member edge with present | ⟨value, pending⟩
      · exact Or.inl present
      · refine Or.inr ⟨value, ?_⟩
        simp only [List.mem_append] at pending ⊢
        rcases pending with root | later
        · have original := (membership _).mp root
          simp only [List.mem_append] at original
          tauto
        · tauto
    obtain ⟨mono1, root1, edges1⟩ := ih1 (second ++ remaining) firstClosed
    obtain ⟨mono2, root2, edges2⟩ := ih2 remaining (by simpa [List.append_assoc] using edges1)
    refine ⟨fun ptr member => mono2 ptr (mono1 ptr member), ?_, edges2⟩
    intro y value member
    have either := (membership _).mp member
    simp only [List.mem_append] at either
    rcases either with firstMember | secondMember
    · rcases root1 y value firstMember with visited | ⟨other, pending⟩
      · exact Or.inl (mono2 y visited)
      · simp only [List.mem_append] at pending
        rcases pending with inSecond | inRemaining
        · exact root2 y other inSecond
        · exact Or.inr ⟨other, inRemaining⟩
    · exact root2 y value secondMember
  | data visited value =>
    refine ⟨fun _ member => member, ?_, ?_⟩
    · intro y v member
      simp at member
    · intro y z member edge
      rcases closed y z member edge with present | ⟨other, pending⟩
      · exact Or.inl present
      · simp only [List.cons_append, List.mem_cons] at pending
        rcases pending with impossible | inRemaining
        · cases impossible
        · exact Or.inr ⟨other, inRemaining⟩
  | seen visited ptr value present =>
    refine ⟨fun _ member => member, ?_, ?_⟩
    · intro y v member
      simp only [List.mem_singleton, HeapAddress.pointer.injEq] at member
      exact Or.inl (by rcases member with ⟨rfl, _⟩; exact present)
    · intro y z member edge
      rcases closed y z member edge with inVisited | ⟨other, pending⟩
      · exact Or.inl inVisited
      · simp only [List.cons_append, List.mem_cons] at pending
        rcases pending with same | later
        · cases same
          exact Or.inl present
        · exact Or.inr ⟨other, later⟩
  | @visit visited after ptr len value children payload found traversal ih =>
    have stepClosed : ∀ y z, y ∈ ptr :: visited → gcEdge heap y z →
        z ∈ ptr :: visited ∨ ∃ v, .pointer z v ∈ children ++ remaining := by
      intro y z member edge
      simp only [List.mem_cons] at member
      rcases member with rfl | inVisited
      · obtain ⟨xs, size, data, other, lookup, child⟩ := edge
        have same := Option.some.inj (found.symm.trans lookup)
        cases same
        exact Or.inr ⟨other, List.mem_append.mpr (Or.inl child)⟩
      · rcases closed y z inVisited edge with present | ⟨other, pending⟩
        · exact Or.inl (by simp [present])
        · simp only [List.cons_append, List.mem_cons] at pending
          rcases pending with same | later
          · cases same
            exact Or.inl (by simp)
          · exact Or.inr ⟨other, List.mem_append.mpr (Or.inr later)⟩
    obtain ⟨mono, _, edges⟩ := ih remaining stepClosed
    refine ⟨fun p member => mono p (by simp [member]), ?_, edges⟩
    intro y v member
    simp only [List.mem_singleton, HeapAddress.pointer.injEq] at member
    rcases member with ⟨rfl, _⟩
    exact Or.inl (mono y (by simp))

/-- Traversal retains visited addresses and closes their outgoing edges,
except for pointers still waiting in the supplied suffix. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "traverse_heap_reachable_aux_vars_gc_edge"]
theorem traverseHeap_reachable_aux_source {α β : Type} (heap : List (HeapElement α β))
    (before : List Nat) (roots : List (HeapAddress α)) (after : List Nat)
    (run : traverseHeap heap before roots after) (remaining : List (HeapAddress α))
    (closed : ∀ y z, y ∈ before ∧ gcEdge heap y z →
      z ∈ before ∨ ∃ value, .pointer z value ∈ roots ++ remaining) :
    ({ptr | ptr ∈ before} : Set Nat) ⊆ {ptr | ptr ∈ after} ∧
    (∀ y value, .pointer y value ∈ roots → y ∈ after ∨ ∃ value, .pointer y value ∈ remaining) ∧
    (∀ y z, y ∈ after ∧ gcEdge heap y z → z ∈ after ∨ ∃ value, .pointer z value ∈ remaining) := by
  obtain ⟨mono, root, edges⟩ := traverseHeap_reachable_aux heap before roots after run remaining
    (fun y z member edge => closed y z ⟨member, edge⟩)
  exact ⟨mono, root, fun y z pair => edges y z pair.1 pair.2⟩

/-- Traversal from an empty visited list closes the visited addresses under
any finite sequence of heap edges. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "traverse_heap_reachable_RTC_gc_edge"]
theorem traverseHeap_reachable_rtc {α β : Type} (heap : List (HeapElement α β))
    (roots : List (HeapAddress α)) (after : List Nat)
    (run : traverseHeap heap [] roots after) :
    ∀ p x, Relation.ReflTransGen (gcEdge heap) p x → p ∈ after → x ∈ after := by
  have closed := (traverseHeap_reachable_aux heap [] roots after run [] (by simp)).2.2
  intro p x path member
  induction path with
  | refl => exact member
  | @tail middle target path edge ih =>
    rcases closed middle target ih edge with present | ⟨_, impossible⟩
    · exact present
    · simp at impossible

/-- Every heap address reachable from the roots is visited by traversal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "traverse_heap_reachable"]
theorem traverseHeap_reachable {α β : Type} (heap : List (HeapElement α β))
    (roots : List (HeapAddress α)) (after : List Nat) (ptr : Nat)
    (run : traverseHeap heap [] roots after) (reachable : reachableAddresses roots heap ptr) : ptr ∈ after := by
  obtain ⟨value, root, rootMember, path⟩ := reachable
  have rootsVisited := (traverseHeap_reachable_aux heap [] roots after run [] (by simp)).2.1
  rcases rootsVisited root value rootMember with present | ⟨_, impossible⟩
  · exact traverseHeap_reachable_rtc heap roots after run root ptr path present
  · simp at impossible

/-- Flapjack infrastructure: a traversal from roots that reach every data
object accounts for at least the data length of the heap. -/
theorem traverseHeap_dataLength_le {α β : Type} (heap : List (HeapElement α β))
    (roots : List (HeapAddress α)) (after : List Nat)
    (run : traverseHeap heap [] roots after)
    (reachable : Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.allReachableFromRoots roots heap) :
    Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.dataLength heap ≤
      (after.map (Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.lookupLen heap)).sum := by
  exact dataLength_le_reachableCover roots heap after reachable
    (fun ptr reach => traverseHeap_reachable heap roots after ptr run reach)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
