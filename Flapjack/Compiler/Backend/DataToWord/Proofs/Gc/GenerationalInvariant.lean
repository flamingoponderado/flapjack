import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalList

/-! Structural invariants for major generational collection. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend

/-- Moving a root advances the data allocation index by exactly the size
appended to the copied-data work list. -/
theorem genMove_dataIndex {α β : Type} (conf : GenGc.Config β) (root root1 : HeapAddress α)
    (state state1 : GcState α β) (run : GenGc.gcMove conf state root = (root1, state1)) :
    state1.a + heapLength state.h1 + heapLength state.h2 =
      state.a + heapLength state1.h1 + heapLength state1.h2 := by
  cases root with
  | data d => simp [GenGc.gcMove, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
  | pointer ptr d =>
    cases found : heapLookup ptr state.heap with
    | none => simp [GenGc.gcMove, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
    | some element =>
      cases element with
      | unused len => simp [GenGc.gcMove, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
      | forwardPointer dest old len => simp [GenGc.gcMove, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
      | dataElement xs len payload =>
        cases test : conf.isRef payload <;>
          simp [GenGc.gcMove, found, test, Prod.mk.injEq] at run <;>
          obtain ⟨_, rfl⟩ := run
        all_goals simp [heapLength, elLength]
        all_goals omega

/-- Root traversal preserves the allocation-index/work-list relationship. -/
theorem genMoveList_dataIndex {α β : Type} (conf : GenGc.Config β) (roots roots1 : List (HeapAddress α))
    (state state1 : GcState α β) (run : GenGc.gcMoveList conf state roots = (roots1, state1)) :
    state1.a + heapLength state.h1 + heapLength state.h2 =
      state.a + heapLength state1.h1 + heapLength state1.h2 := by
  induction roots generalizing roots1 state state1 with
  | nil => simp [GenGc.gcMoveList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
  | cons root roots ih =>
    simp only [GenGc.gcMoveList] at run
    generalize headRun : GenGc.gcMove conf state root = headResult at run
    obtain ⟨root1, middle⟩ := headResult
    generalize tailRun : GenGc.gcMoveList conf middle roots = tailResult at run
    obtain ⟨tail, final⟩ := tailResult
    simp only [Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    have first := genMove_dataIndex conf root root1 state middle headRun
    have second := ih tail middle final tailRun
    omega

/-- Reference scanning preserves the allocation-index/work-list relationship. -/
theorem genMoveRefs_dataIndex {α β : Type} (conf : GenGc.Config β) (state : GcState α β) :
    (GenGc.gcMoveRefs conf state).a + heapLength state.h1 + heapLength state.h2 =
      state.a + heapLength (GenGc.gcMoveRefs conf state).h1 + heapLength (GenGc.gcMoveRefs conf state).h2 := by
  induction state using GenGc.gcMoveRefs.induct conf with
  | case1 state empty =>
    cases state with
    | mk old h1 h2 r4 r3 r2 r1 a n ok heap heap0 =>
      simp only at empty
      subst r2
      rw [GenGc.gcMoveRefs]
  | case2 state tail roots len payload refs roots1 middle move refsAgain ih =>
    have moved := genMoveList_dataIndex conf roots roots1 state middle move
    cases state with
    | mk old h1 h2 r4 r3 r2 r1 a n ok heap heap0 =>
      simp only at refs
      subst r2
      rw [GenGc.gcMoveRefs]
      simp only [move]
      dsimp at ih moved
      omega
  | case3 state head tail refs refsAgain notData =>
    cases head with
    | unused len =>
      cases state with
      | mk old h1 h2 r4 r3 r2 r1 a n ok heap heap0 =>
        simp only at refs
        subst r2
        rw [GenGc.gcMoveRefs]
    | forwardPointer ptr value len =>
      cases state with
      | mk old h1 h2 r4 r3 r2 r1 a n ok heap heap0 =>
        simp only at refs
        subst r2
        rw [GenGc.gcMoveRefs]
    | dataElement roots len payload => exact False.elim (notData roots len payload refs rfl (by rfl))

/-- Root movement leaves the scanned heap and processed reference lists unchanged. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_move_const"]
theorem genMove_const {α β : Type} (conf : GenGc.Config β) (root root1 : HeapAddress α)
    (state state1 : GcState α β) (run : GenGc.gcMove conf state root = (root1, state1)) :
    state1.h1 = state.h1 ∧ state1.r1 = state.r1 ∧ state1.r2 = state.r2 ∧ state1.r3 = state.r3 := by
  cases root with
  | data d => simp [GenGc.gcMove, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; exact ⟨rfl, rfl, rfl, rfl⟩
  | pointer ptr d =>
    cases found : heapLookup ptr state.heap with
    | none => simp [GenGc.gcMove, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; exact ⟨rfl, rfl, rfl, rfl⟩
    | some element =>
      cases element with
      | unused len => simp [GenGc.gcMove, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; exact ⟨rfl, rfl, rfl, rfl⟩
      | forwardPointer dest old len => simp [GenGc.gcMove, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; exact ⟨rfl, rfl, rfl, rfl⟩
      | dataElement xs len payload =>
        cases test : conf.isRef payload <;> simp [GenGc.gcMove, found, test, Prod.mk.injEq] at run <;>
          obtain ⟨_, rfl⟩ := run <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Traversing roots preserves the already processed heap and reference lists. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_move_list_const"]
theorem genMoveList_const {α β : Type} (conf : GenGc.Config β) (roots roots1 : List (HeapAddress α))
    (state state1 : GcState α β) (run : GenGc.gcMoveList conf state roots = (roots1, state1)) :
    state1.h1 = state.h1 ∧ state1.r1 = state.r1 ∧ state1.r2 = state.r2 ∧ state1.r3 = state.r3 := by
  induction roots generalizing roots1 state state1 with
  | nil =>
    simp only [GenGc.gcMoveList, Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    exact ⟨rfl, rfl, rfl, rfl⟩
  | cons root roots ih =>
    simp only [GenGc.gcMoveList] at run
    generalize headRun : GenGc.gcMove conf state root = headResult at run
    rcases headResult with ⟨root1, middle⟩
    generalize tailRun : GenGc.gcMoveList conf middle roots = tailResult at run
    rcases tailResult with ⟨tail, final⟩
    simp only [Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    obtain ⟨h1, r1, r2, r3⟩ := genMove_const conf root root1 state middle headRun
    obtain ⟨h1Tail, r1Tail, r2Tail, r3Tail⟩ := ih tail middle final tailRun
    exact ⟨h1Tail.trans h1, r1Tail.trans r1, r2Tail.trans r2, r3Tail.trans r3⟩

/-- Scanning reference objects leaves the already scanned heap unchanged. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_move_refs_const"]
theorem genMoveRefs_const {α β : Type} (conf : GenGc.Config β) (state state1 : GcState α β)
    (run : GenGc.gcMoveRefs conf state = state1) : state1.h1 = state.h1 := by
  subst state1
  induction state using GenGc.gcMoveRefs.induct conf with
  | case1 state empty =>
    cases state with
    | mk old h1 h2 r4 r3 r2 r1 a n ok heap heap0 =>
      simp only at empty
      subst r2
      rw [GenGc.gcMoveRefs]
  | case2 state tail roots len payload refs roots1 middle move refsAgain ih =>
    cases state with
    | mk old h1 h2 r4 r3 r2 r1 a n ok heap heap0 =>
      simp only at refs
      subst r2
      rw [GenGc.gcMoveRefs]
      simp only [move]
      exact ih.trans (genMoveList_const conf roots roots1 _ middle move).1
  | case3 state head tail refs refsAgain notData =>
    cases head with
    | unused len =>
      cases state with
      | mk old h1 h2 r4 r3 r2 r1 a n ok heap heap0 =>
        simp only at refs
        subst r2
        rw [GenGc.gcMoveRefs]
    | forwardPointer ptr value len =>
      cases state with
      | mk old h1 h2 r4 r3 r2 r1 a n ok heap heap0 =>
        simp only at refs
        subst r2
        rw [GenGc.gcMoveRefs]
    | dataElement roots len payload =>
      exact False.elim (notData roots len payload refs rfl (by rfl))

/-- Scanning copied data preserves the processed reference lists. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_move_data_const"]
theorem genMoveData_const {α β : Type} (conf : GenGc.Config β) (state state1 : GcState α β)
    (run : GenGc.gcMoveData conf state = state1) :
    state1.r1 = state.r1 ∧ state1.r2 = state.r2 ∧ state1.r3 = state.r3 := by
  classical
  subst state1
  induction state using GenGc.gcMoveData.induct conf with
  | case1 state empty => rw [GenGc.gcMoveData]; simp [empty]
  | case2 state head tail heap over => rw [GenGc.gcMoveData]; simp [heap, over]
  | case3 state tail roots len payload roots1 middle move heap bounded flag ih =>
    cases state with
    | mk old h1 h2 r4 r3 r2 r1 a n ok origHeap heap0 =>
      simp only at heap
      subst h2
      rw [GenGc.gcMoveData]
      simp only [bounded, ↓reduceIte, move]
      dsimp only [flag] at ih
      obtain ⟨_, eq1, eq2, eq3⟩ := genMoveList_const conf roots roots1 _ middle move
      exact ⟨ih.1.trans eq1, ih.2.1.trans eq2, ih.2.2.trans eq3⟩
  | case4 state head tail heap bounded notData =>
    cases head with
    | unused len => rw [GenGc.gcMoveData]; simp [heap, bounded]
    | forwardPointer ptr value len => rw [GenGc.gcMoveData]; simp [heap, bounded]
    | dataElement roots len payload => exact False.elim (notData roots len payload rfl)

/-- A successful forwarding update preserves heap length and its input status. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "heap_length_gc_forward_ptr"]
theorem heapLength_gcForwardPtr {α β : Type} (heap : List (HeapElement α β))
    (offset address : Nat) (value : α) (ok : Bool) (result : List (HeapElement α β))
    (run : gcForwardPtr offset heap address value ok = (result, true)) :
    heapLength result = heapLength heap ∧ ok = true := by
  induction heap generalizing offset result with
  | nil => simp [gcForwardPtr] at run
  | cons head tail ih =>
    simp only [gcForwardPtr] at run
    split at run
    · cases head <;> simp_all [heapLength, elLength]
      obtain ⟨rfl, _⟩ := run
      simp [elLength]
    · split at run
      · simp at run
      · cases next : gcForwardPtr (offset - elLength head) tail address value ok with
        | mk tailResult status =>
          simp only [next, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          obtain ⟨lengthEq, okEq⟩ := ih _ tailResult next
          exact ⟨by simpa [heapLength] using congrArg (elLength head + ·) lengthEq, okEq⟩

/-- Successful movement of a root preserves the collector's length invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_move_thm"]
theorem genMove_lenInv {α β : Type} (conf : GenGc.Config β) (root root1 : HeapAddress α)
    (state state1 : GcState α β) (run : GenGc.gcMove conf state root = (root1, state1))
    (ok : state1.ok = true) (inv : genLenInv state) : genLenInv state1 := by
  cases root with
  | data d =>
    simp only [GenGc.gcMove, Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    exact inv
  | pointer ptr d =>
    cases found : heapLookup ptr state.heap with
    | none => simp [GenGc.gcMove, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; simp at ok
    | some element =>
      cases element with
      | unused len => simp [GenGc.gcMove, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; simp at ok
      | forwardPointer dest old len =>
        simp [GenGc.gcMove, found, Prod.mk.injEq] at run
        obtain ⟨_, rfl⟩ := run
        exact inv
      | dataElement xs len payload =>
        cases isRef : conf.isRef payload <;>
          simp only [GenGc.gcMove, found, isRef, Bool.false_eq_true, ↓reduceIte] at run
        all_goals
          simp only [Prod.mk.injEq] at run
          obtain ⟨_, rfl⟩ := run
        all_goals
          first
          | have test : conf.isRef payload = false := isRef
            generalize forward : gcForwardPtr ptr state.heap state.a d
              (state.ok && decide (len + 1 ≤ state.n)) = pair at ok ⊢
          | have test : conf.isRef payload = true := isRef
            generalize forward : gcForwardPtr ptr state.heap (state.a + (state.n - (len + 1))) d
              (state.ok && decide (len + 1 ≤ state.n)) = pair at ok ⊢
          cases pair with
          | mk heap1 status =>
            change status = true at ok
            subst status
            obtain ⟨heapEq, flags⟩ := heapLength_gcForwardPtr state.heap ptr _ d _ heap1 forward
            simp only [Bool.and_eq_true, decide_eq_true_eq] at flags
            simp [genLenInv, heapLength, List.map_append, List.sum_append, elLength] at inv ⊢
            simp [heapLength] at heapEq
            omega

/-- Successful root traversal preserves the major collector's length invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_move_list_thm"]
theorem genMoveList_lenInv {α β : Type} (conf : GenGc.Config β)
    (roots roots1 : List (HeapAddress α)) (state state1 : GcState α β)
    (run : GenGc.gcMoveList conf state roots = (roots1, state1))
    (ok : state1.ok = true) (inv : genLenInv state) : genLenInv state1 := by
  induction roots generalizing roots1 state state1 with
  | nil =>
    simp only [GenGc.gcMoveList, Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    exact inv
  | cons root roots ih =>
    simp only [GenGc.gcMoveList] at run
    generalize headRun : GenGc.gcMove conf state root = headResult at run
    rcases headResult with ⟨root1, middle⟩
    generalize tailRun : GenGc.gcMoveList conf middle roots = tailResult at run
    rcases tailResult with ⟨tail, final⟩
    simp only [Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    have middleOk := GenGc.gcMoveList_ok conf roots tail middle final tailRun ok
    exact ih tail middle final tailRun ok (genMove_lenInv conf root root1 state middle headRun middleOk inv)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
