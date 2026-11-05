import Flapjack.Compiler.Backend.GenGcPartial.Proofs.Accumulator
import Batteries.Data.List.Basic

/-! Shape preservation of partial-collector reference traversals. -/
namespace Flapjack.Compiler.Backend.GenGcPartial

/-- Pointer locations may change, but their payloads must remain equal. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "similar_ptr_def"]
def similarPtr {α σ : Type} (_conf : σ) : HeapAddress α → HeapAddress α → Prop
  | .pointer _ v, .pointer _ w => w = v
  | x, y => x = y

/-- Data elements retain their size and payload while their pointers may move. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "similar_data_def"]
def similarData {α β σ : Type} (conf : σ) : HeapElement α β → HeapElement α β → Prop
  | .dataElement xs len payload, .dataElement ys len1 payload1 =>
      len1 = len ∧ payload1 = payload ∧ List.Forall₂ (similarPtr conf) xs ys
  | x, y => x = y

/-- Moving one root preserves its pointer payload. This is local factoring of
the reference-list similarity proof. -/
theorem gcMove_similar {α β : Type} (conf : Config β) (state state1 : GcState α β)
    (root root1 : HeapAddress α) (run : gcMove conf state root = (root1, state1)) :
    similarPtr conf root root1 := by
  cases root with
  | data value => simp [gcMove, Prod.mk.injEq] at run; obtain ⟨rfl, _⟩ := run; rfl
  | pointer ptr value =>
    by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
    · simp [gcMove, outside, Prod.mk.injEq] at run; obtain ⟨rfl, _⟩ := run; rfl
    · cases found : heapLookup ptr state.heap with
      | none => simp [gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨rfl, _⟩ := run; rfl
      | some element =>
        cases element with
        | unused len => simp [gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨rfl, _⟩ := run; rfl
        | forwardPointer dest old len => simp [gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨rfl, _⟩ := run; rfl
        | dataElement xs len payload =>
          cases forward : gcForwardPtr ptr state.heap state.a value
              ((state.ok && decide (ptr < heapLength state.heap)) && decide (len + 1 ≤ state.n) && !(conf.isRef payload)) with
          | mk newHeap status =>
            simp only [gcMove, outside, ↓reduceIte, found, forward, Prod.mk.injEq] at run
            obtain ⟨rfl, _⟩ := run
            rfl

/-- Partial root traversal preserves pointer payloads and list structure.
The local HOL proof has not yet been replayed. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_list_similar"]
theorem gcMoveList_similar {α β : Type} (conf : Config β) (roots roots1 : List (HeapAddress α))
    (state state1 : GcState α β) (run : gcMoveList conf state roots = (roots1, state1)) :
    List.Forall₂ (similarPtr conf) roots roots1 := by
  induction roots generalizing roots1 state state1 with
  | nil => simp [gcMoveList, Prod.mk.injEq] at run; obtain ⟨rfl, _⟩ := run; exact .nil
  | cons root roots ih =>
    simp only [gcMoveList] at run
    generalize headRun : gcMove conf state root = headResult at run
    obtain ⟨root1, middle⟩ := headResult
    generalize tailRun : gcMoveList conf middle roots = tailResult at run
    obtain ⟨tail, final⟩ := tailResult
    simp only [Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    exact .cons (gcMove_similar conf state middle root root1 headRun) (ih tail middle final tailRun)

/-- Every element is similar to itself. -/
theorem similarData_refl {α β σ : Type} (conf : σ) (element : HeapElement α β) : similarData conf element element := by
  cases element with
  | unused len => rfl
  | forwardPointer ptr value len => rfl
  | dataElement roots len payload =>
    refine ⟨rfl, rfl, ?_⟩
    induction roots with
    | nil => exact .nil
    | cons root roots ih =>
      apply List.Forall₂.cons
      · cases root <;> rfl
      · exact ih

/-- A list is pointwise similar to itself. -/
theorem similarData_listRefl {α β σ : Type} (conf : σ) (elements : List (HeapElement α β)) :
    List.Forall₂ (similarData conf) elements elements := by
  induction elements with
  | nil => exact .nil
  | cons head tail ih => exact .cons (similarData_refl conf head) ih

/-- Reference traversal preserves element sizes, payloads, and pointer
payloads. The local HOL proof has not yet been replayed. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_ref_list_similar"]
theorem gcMoveRefList_similar {α β γ : Type} (conf : Config γ)
    (refs refs1 : List (HeapElement α β)) (state state1 : GcState α γ)
    (run : gcMoveRefList conf state refs = (refs1, state1)) :
    List.Forall₂ (similarData conf) refs refs1 := by
  induction refs generalizing refs1 state state1 with
  | nil => simp [gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨rfl, _⟩ := run; exact .nil
  | cons head tail ih =>
    cases head with
    | unused len =>
      simp [gcMoveRefList, Prod.mk.injEq] at run
      obtain ⟨rfl, _⟩ := run
      exact similarData_listRefl conf _
    | forwardPointer ptr value len =>
      simp [gcMoveRefList, Prod.mk.injEq] at run
      obtain ⟨rfl, _⟩ := run
      exact similarData_listRefl conf _
    | dataElement roots len payload =>
      simp only [gcMoveRefList] at run
      generalize headRun : gcMoveList conf state roots = headResult at run
      obtain ⟨roots1, middle⟩ := headResult
      generalize tailRun : gcMoveRefList conf middle tail = tailResult at run
      obtain ⟨tail1, final⟩ := tailResult
      simp only [Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      exact .cons ⟨rfl, rfl, gcMoveList_similar conf roots roots1 state middle headRun⟩
        (ih tail1 middle final tailRun)

/-- Partial collection preserves the number of roots, including failure. -/
theorem partialGc_length {α β : Type} (conf : Config β) (roots roots1 : List (HeapAddress α))
    (heap : List (HeapElement α β)) (state : GcState α β)
    (run : partialGc conf (roots, heap) = (roots1, state)) : roots1.length = roots.length := by
  classical
  simp only [partialGc] at run
  cases segment : heapSegment (conf.genStart, conf.refsStart) heap with
  | none => simp [segment, Prod.mk.injEq] at run; obtain ⟨rfl, _⟩ := run; rfl
  | some parts =>
    obtain ⟨old, current, refs⟩ := parts
    simp only [segment] at run
    generalize move : gcMoveList conf
      { emptyGcState with heap := heap, old := old, r2 := refs, a := conf.genStart, n := heapLength current }
      roots = moved at run
    obtain ⟨roots2, middle⟩ := moved
    cases scan : gcMoveRefList conf middle refs with
    | mk refs1 afterRefs =>
      simp only [scan, Prod.mk.injEq] at run
      obtain ⟨rfl, _⟩ := run
      have related := gcMoveList_similar conf roots roots2 _ middle move
      clear move
      induction related with
      | nil => rfl
      | cons head tail ih => simp [ih]

open Classical in
/-- Similar heaps have the same total size and the same size after filtering
to data elements. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "LIST_REL_similar_data_IMP"]
theorem similarData_lengths {α β σ : Type} (conf : σ) (xs ys : List (HeapElement α β))
    (related : List.Forall₂ (similarData conf) xs ys) :
    heapLength xs = heapLength ys ∧
      heapLength (xs.filter (fun element => decide (isDataElement element))) =
        heapLength (ys.filter (fun element => decide (isDataElement element))) := by
  induction related with
  | nil => simp [heapLength]
  | @cons x y xs ys head tail ih =>
    cases x <;> cases y <;>
      simp_all [similarData, isDataElement, heapLength, elLength]

open Classical in
/-- A partial reference traversal preserves the data-element length of the
reference list, including on failing runs. -/
theorem gcMoveRefList_dataLength {α β γ : Type} (conf : Config γ)
    (refs refs1 : List (HeapElement α β)) (state state1 : GcState α γ)
    (run : gcMoveRefList conf state refs = (refs1, state1)) :
    heapLength (refs.filter (fun element => decide (isDataElement element))) =
      heapLength (refs1.filter (fun element => decide (isDataElement element))) :=
  (similarData_lengths conf refs refs1 (gcMoveRefList_similar conf refs refs1 state state1 run)).2

end Flapjack.Compiler.Backend.GenGcPartial
