module

public import Flapjack.Compiler.Backend.GenGcPartial
public import Flapjack.Compiler.Backend.GcShared.ForwardPtr

@[expose] public section

/-!
# Status preservation for the partial generational collector

A successful source traversal can only start from a successful state: the
collector's status flag is never turned back on.  The two private helpers below
record the failure direction, from which each public theorem follows.
-/

namespace Flapjack.Compiler.Backend.GenGcPartial

/-- Forwarding from a failing status keeps reporting failure. -/
private theorem gcForwardPtr_ok_false {α β : Type} (offset : Nat)
    (heap : List (HeapElement α β)) (ptr : Nat) (value : α) :
    (gcForwardPtr offset heap ptr value false).2 = false := by
  induction heap generalizing offset with
  | nil => rfl
  | cons head tail ih =>
    simp only [gcForwardPtr]
    split
    · simp
    · split
      · rfl
      · exact ih _

/-- Moving one root from a failing status keeps reporting failure. -/
private theorem gcMove_ok_false {α β : Type} (conf : Config β) (state : GcState α β)
    (root : HeapAddress α) (stateOk : state.ok = false) :
    (gcMove conf state root).2.ok = false := by
  cases root with
  | data value => exact stateOk
  | pointer ptr value =>
    simp only [gcMove, stateOk, Bool.false_and]
    by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
    · simp [outside]
    · simp only [outside, if_false]
      cases found : heapLookup ptr state.heap with
      | none => simp
      | some element =>
        cases element with
        | unused len => simp
        | forwardPointer newPtr addr len => exact stateOk
        | dataElement xs len payload => simp [gcForwardPtr_ok_false]

/-- A successful root move started from a successful state. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_ok'"]
theorem gcMove_ok' {α β : Type} (conf : Config β) (root root1 : HeapAddress α)
    (state state1 : GcState α β)
    (h : gcMove conf state root = (root1, state1) ∧ state1.ok = true) :
    state.ok = true := by
  obtain ⟨run, ok⟩ := h
  cases stateOk : state.ok
  · have contra := gcMove_ok_false conf state root stateOk
    rw [run] at contra
    rw [contra] at ok
    simp at ok
  · rfl

/-- A successful root move of an in-range pointer started from a successful
state. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_ok"]
theorem gcMove_ok {α β : Type} (conf : Config β) (root root1 : HeapAddress α)
    (state state1 : GcState α β)
    (h : gcMove conf state root = (root1, state1) ∧ state1.ok = true ∧
      ∀ ptr value, root = .pointer ptr value → ptr < heapLength state.heap) :
    state.ok = true := by
  obtain ⟨run, ok, _⟩ := h
  exact gcMove_ok' conf root root1 state state1 ⟨run, ok⟩

/-- A successful root-list move started from a successful state. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_list_ok'"]
theorem gcMoveList_ok' {α β : Type} (conf : Config β) (roots roots1 : List (HeapAddress α))
    (state state1 : GcState α β)
    (h : gcMoveList conf state roots = (roots1, state1) ∧ state1.ok = true) :
    state.ok = true := by
  obtain ⟨run, ok⟩ := h
  induction roots generalizing state roots1 state1 with
  | nil =>
    simp only [gcMoveList, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ok
  | cons root roots ih =>
    simp only [gcMoveList] at run
    generalize headRun : gcMove conf state root = result at run
    obtain ⟨rootMid, middle⟩ := result
    generalize tailRun : gcMoveList conf middle roots = result at run
    obtain ⟨tail, final⟩ := result
    simp only [Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    exact gcMove_ok' conf root rootMid state middle
      ⟨headRun, ih (state := middle) (roots1 := tail) (state1 := final) tailRun ok⟩

/-- A successful root-list move of in-range pointers started from a successful
state. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_list_ok"]
theorem gcMoveList_ok {α β : Type} (roots roots1 : List (HeapAddress α))
    (state state1 : GcState α β) (conf : Config β)
    (h : gcMoveList conf state roots = (roots1, state1) ∧ state1.ok = true ∧
      ∀ ptr value, .pointer ptr value ∈ roots → ptr < heapLength state.heap) :
    state.ok = true := by
  obtain ⟨run, ok, _⟩ := h
  exact gcMoveList_ok' conf roots roots1 state state1 ⟨run, ok⟩

/-- A successful reference-list move started from a successful state. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_ref_list_ok'"]
theorem gcMoveRefList_ok' {α β γ : Type} (conf : Config γ)
    (refs refs1 : List (HeapElement α β)) (state state1 : GcState α γ)
    (h : gcMoveRefList conf state refs = (refs1, state1) ∧ state1.ok = true) :
    state.ok = true := by
  obtain ⟨run, ok⟩ := h
  induction refs generalizing state refs1 state1 with
  | nil =>
    simp only [gcMoveRefList, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ok
  | cons head tail ih =>
    cases head with
    | unused len =>
      simp only [gcMoveRefList, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      simp at ok
    | forwardPointer ptr value len =>
      simp only [gcMoveRefList, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      simp at ok
    | dataElement roots len payload =>
      simp only [gcMoveRefList] at run
      generalize headRun : gcMoveList conf state roots = result at run
      obtain ⟨rootsMid, middle⟩ := result
      generalize tailRun : gcMoveRefList conf middle tail = result at run
      obtain ⟨tail1, final⟩ := result
      simp only [Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      exact gcMoveList_ok' conf roots rootsMid state middle
        ⟨headRun, ih (state := middle) (refs1 := tail1) (state1 := final) tailRun ok⟩

/-- A successful copied-data scan started from a successful state. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_data_ok'"]
theorem gcMoveData_ok' {α β : Type} (conf : Config β) (state state1 : GcState α β)
    (h : gcMoveData conf state = state1 ∧ state1.ok = true) : state.ok = true := by
  obtain ⟨run, ok⟩ := h
  classical
  induction state using gcMoveData.induct conf with
  | case1 state empty =>
    unfold gcMoveData at run
    simp only [empty] at run
    rw [← run] at ok
    exact ok
  | case2 state head tail heap over =>
    unfold gcMoveData at run
    simp only [heap, over, ↓reduceIte] at run
    rw [← run] at ok
    simp at ok
  | case3 state tail roots len payload roots1 middle move heap bounded flag ih =>
    cases state with
    | mk old h1 h2 r4 r3 r2 r1 a n status origHeap heap0 =>
      simp only at heap
      subst h2
      unfold gcMoveData at run
      simp only [bounded, ↓reduceIte, move] at run
      have step := ih run
      simp only [flag, Bool.and_eq_true] at step
      exact gcMoveList_ok' conf roots roots1
        (GcState.mk old h1 (.dataElement roots len payload :: tail) r4 r3 r2 r1 a n status
          origHeap heap0) middle ⟨move, step.1.1⟩
  | case4 state head tail heap bounded notData =>
    cases head with
    | unused len =>
      unfold gcMoveData at run
      simp only [heap, bounded, ↓reduceIte] at run
      rw [← run] at ok
      simp at ok
    | forwardPointer ptr value len =>
      unfold gcMoveData at run
      simp only [heap, bounded, ↓reduceIte] at run
      rw [← run] at ok
      simp at ok
    | dataElement roots len payload => exact False.elim (notData roots len payload rfl)

end Flapjack.Compiler.Backend.GenGcPartial
