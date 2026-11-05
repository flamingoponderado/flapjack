import Flapjack.Compiler.Backend.GenGcPartial.Proofs.Similarity
import Flapjack.Compiler.Backend.GcShared.ForwardPtr

/-! Data-mass preservation for partial generational collection. -/
namespace Flapjack.Compiler.Backend.GenGcPartial

open Classical in
/-- Total encoded size of the data elements in a heap. -/
noncomputable def dataMass {α β : Type} (heap : List (HeapElement α β)) : Nat :=
  heapLength (heap.filter (fun element => decide (isDataElement element)))

/-- The data mass distributes over a concatenation. -/
theorem dataMass_append {α β : Type} (xs ys : List (HeapElement α β)) :
    dataMass (xs ++ ys) = dataMass xs + dataMass ys := by
  classical
  simp [dataMass, List.filter_append, heapLength_append]

/-- Filtering a heap consisting entirely of data preserves its encoded size. -/
theorem dataMass_of_allData {α β : Type} (heap : List (HeapElement α β))
    (allData : ∀ element ∈ heap, isDataElement element) : dataMass heap = heapLength heap := by
  classical
  unfold dataMass
  congr 1
  rw [List.filter_eq_self]
  simpa using allData

/-- Forwarding a data element moves exactly its encoded size out of the
source heap's data mass. -/
theorem forwardPtr_dataMass {α β : Type} (heap newHeap : List (HeapElement α β))
    (ptr address : Nat) (value : α) (roots : List (HeapAddress α)) (len : Nat) (payload : β) (ok : Bool)
    (found : heapLookup ptr heap = some (.dataElement roots len payload))
    (run : gcForwardPtr ptr heap address value ok = (newHeap, ok)) :
    dataMass heap = dataMass newHeap + (len + 1) := by
  classical
  obtain ⟨before, after, heapEq, ptrEq⟩ := heapLookup_split heap ptr _ found
  rw [heapEq, ptrEq, gcForwardPtr_thm] at run
  simp only [Prod.mk.injEq] at run
  obtain ⟨rfl, _⟩ := run
  simp [heapEq, dataMass, List.filter_append, isDataElement, heapLength, elLength]
  omega

/-- One root move conserves the total size of data still in the source heap
plus copied data. -/
theorem gcMove_dataMass {α β : Type} (conf : Config β) (state state1 : GcState α β)
    (root root1 : HeapAddress α) (run : gcMove conf state root = (root1, state1)) :
    dataMass state.heap + heapLength state.h1 + heapLength state.h2 =
      dataMass state1.heap + heapLength state1.h1 + heapLength state1.h2 := by
  classical
  cases root with
  | data value => simp [gcMove, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
  | pointer ptr value =>
    by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
    · simp [gcMove, outside, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
    · cases found : heapLookup ptr state.heap with
      | none => simp [gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
      | some element =>
        cases element with
        | unused len => simp [gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
        | forwardPointer dest old len => simp [gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
        | dataElement roots len payload =>
          obtain ⟨before, after, heapEq, ptrEq⟩ := heapLookup_split state.heap ptr _ found
          have direct := gcForwardPtr_thm before after roots len payload state.a value
            ((state.ok && decide (ptr < heapLength state.heap)) && decide (len + 1 ≤ state.n) && !(conf.isRef payload))
          have forward : gcForwardPtr ptr state.heap state.a value
              ((state.ok && decide (ptr < heapLength state.heap)) && decide (len + 1 ≤ state.n) && !(conf.isRef payload)) =
              (before ++ .forwardPointer state.a value len :: after,
                ((state.ok && decide (ptr < heapLength state.heap)) && decide (len + 1 ≤ state.n) && !(conf.isRef payload))) := by
            simpa only [← heapEq, ← ptrEq] using direct
          simp only [gcMove, outside, ↓reduceIte, found, forward, Prod.mk.injEq] at run
          obtain ⟨_, rfl⟩ := run
          simp [heapEq, dataMass, List.filter_append, isDataElement, heapLength, elLength]
          omega

/-- Moving a list of roots conserves data mass. -/
theorem gcMoveList_dataMass {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (state state1 : GcState α β)
    (run : gcMoveList conf state roots = (roots1, state1)) :
    dataMass state.heap + heapLength state.h1 + heapLength state.h2 =
      dataMass state1.heap + heapLength state1.h1 + heapLength state1.h2 := by
  induction roots generalizing roots1 state state1 with
  | nil => simp [gcMoveList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
  | cons root roots ih =>
    simp only [gcMoveList] at run
    generalize headRun : gcMove conf state root = headResult at run
    obtain ⟨root1, middle⟩ := headResult
    generalize tailRun : gcMoveList conf middle roots = tailResult at run
    obtain ⟨tail, final⟩ := tailResult
    simp only [Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    exact (gcMove_dataMass conf state middle root root1 headRun).trans
      (ih tail middle final tailRun)

/-- Scanning reference elements conserves data mass. -/
theorem gcMoveRefList_dataMass {α β γ : Type} (conf : Config γ)
    (refs refs1 : List (HeapElement α β)) (state state1 : GcState α γ)
    (run : gcMoveRefList conf state refs = (refs1, state1)) :
    dataMass state.heap + heapLength state.h1 + heapLength state.h2 =
      dataMass state1.heap + heapLength state1.h1 + heapLength state1.h2 := by
  induction refs generalizing refs1 state state1 with
  | nil => simp [gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
  | cons head tail ih =>
    cases head with
    | unused len => simp [gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
    | forwardPointer ptr value len => simp [gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
    | dataElement roots len payload =>
      simp only [gcMoveRefList] at run
      generalize headRun : gcMoveList conf state roots = headResult at run
      obtain ⟨roots1, middle⟩ := headResult
      generalize tailRun : gcMoveRefList conf middle tail = tailResult at run
      obtain ⟨tail1, final⟩ := tailResult
      simp only [Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      exact (gcMoveList_dataMass conf roots roots1 state middle headRun).trans
        (ih tail1 middle final tailRun)

/-- Moving a root preserves data-object membership in the source heap and
pending copied objects. The local HOL proof has not yet been replayed. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_data_pres"]
theorem gcMove_dataMem {α β : Type} (conf : Config β) (state state1 : GcState α β)
    (root root1 : HeapAddress α) (children : List (HeapAddress α)) (size : Nat) (data : β)
    (run : gcMove conf state root = (root1, state1)) :
    (.dataElement children size data ∈ state1.heap ++ state1.h2) ↔
      (.dataElement children size data ∈ state.heap ++ state.h2) := by
  classical
  cases root with
  | data value => simp [gcMove, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
  | pointer ptr value =>
    by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
    · simp [gcMove, outside, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
    · cases found : heapLookup ptr state.heap with
      | none => simp [gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
      | some element =>
        cases element with
        | unused len => simp [gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
        | forwardPointer dest old len => simp [gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
        | dataElement roots len payload =>
          obtain ⟨before, after, heapEq, ptrEq⟩ := heapLookup_split state.heap ptr _ found
          have direct := gcForwardPtr_thm before after roots len payload state.a value
            ((state.ok && decide (ptr < heapLength state.heap)) && decide (len + 1 ≤ state.n) && !(conf.isRef payload))
          have forward : gcForwardPtr ptr state.heap state.a value
              ((state.ok && decide (ptr < heapLength state.heap)) && decide (len + 1 ≤ state.n) && !(conf.isRef payload)) =
              (before ++ .forwardPointer state.a value len :: after,
                ((state.ok && decide (ptr < heapLength state.heap)) && decide (len + 1 ≤ state.n) && !(conf.isRef payload))) := by
            simpa only [← heapEq, ← ptrEq] using direct
          simp only [gcMove, outside, ↓reduceIte, found, forward, Prod.mk.injEq] at run
          obtain ⟨_, rfl⟩ := run
          simp [heapEq, List.mem_append, or_comm, or_left_comm]

/-- Moving a root list preserves pending data membership. The local HOL proof
has not yet been replayed. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_list_data_pres"]
theorem gcMoveList_dataMem {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (state state1 : GcState α β)
    (children : List (HeapAddress α)) (size : Nat) (data : β)
    (run : gcMoveList conf state roots = (roots1, state1)) :
    (.dataElement children size data ∈ state1.heap ++ state1.h2) ↔
      (.dataElement children size data ∈ state.heap ++ state.h2) := by
  induction roots generalizing roots1 state state1 with
  | nil => simp [gcMoveList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
  | cons root roots ih =>
    simp only [gcMoveList] at run
    generalize headRun : gcMove conf state root = headResult at run
    obtain ⟨root1, middle⟩ := headResult
    generalize tailRun : gcMoveList conf middle roots = tailResult at run
    obtain ⟨tail, final⟩ := tailResult
    simp only [Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    exact (ih tail middle final tailRun).trans
      (gcMove_dataMem conf state middle root root1 children size data headRun)

/-- Reference scanning preserves pending data membership. The local HOL proof
has not yet been replayed. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_ref_list_data_pres"]
theorem gcMoveRefList_dataMem {α β γ : Type} (conf : Config γ)
    (refs refs1 : List (HeapElement α β)) (state state1 : GcState α γ)
    (children : List (HeapAddress α)) (size : Nat) (data : γ)
    (run : gcMoveRefList conf state refs = (refs1, state1)) :
    (.dataElement children size data ∈ state1.heap ++ state1.h2) ↔
      (.dataElement children size data ∈ state.heap ++ state.h2) := by
  induction refs generalizing refs1 state state1 with
  | nil => simp [gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
  | cons head tail ih =>
    cases head with
    | unused len => simp [gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
    | forwardPointer ptr value len => simp [gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
    | dataElement roots len payload =>
      simp only [gcMoveRefList] at run
      generalize headRun : gcMoveList conf state roots = headResult at run
      obtain ⟨roots1, middle⟩ := headResult
      generalize tailRun : gcMoveRefList conf middle tail = tailResult at run
      obtain ⟨tail1, final⟩ := tailResult
      simp only [Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      exact (ih tail1 middle final tailRun).trans
        (gcMoveList_dataMem conf roots roots1 state middle children size data headRun)

end Flapjack.Compiler.Backend.GenGcPartial
