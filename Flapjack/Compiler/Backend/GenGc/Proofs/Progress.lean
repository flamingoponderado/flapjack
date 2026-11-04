import Flapjack.Compiler.Backend.GenGc
import Flapjack.Compiler.Backend.GcShared.ForwardPtr

/-! Success preservation for the major collector. -/
namespace Flapjack.Compiler.Backend.GenGc

/-- A successful root move started from a successful state. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "gc_move_ok"]
theorem gcMove_ok {α β : Type} (conf : Config β) (state state1 : GcState α β)
    (root root1 : HeapAddress α) (run : gcMove conf state root = (root1, state1))
    (ok : state1.ok = true) : state.ok = true := by
  cases root with
  | data value =>
    simp only [gcMove, Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    exact ok
  | pointer ptr value =>
    cases found : heapLookup ptr state.heap with
    | none => simp [gcMove, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; simp at ok
    | some element =>
      cases element with
      | unused len => simp [gcMove, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; simp at ok
      | forwardPointer dest old len =>
        simp [gcMove, found, Prod.mk.injEq] at run
        obtain ⟨_, rfl⟩ := run
        exact ok
      | dataElement xs len payload =>
        have forwardOk (address : Nat) :
            (gcForwardPtr ptr state.heap address value (state.ok && decide (len + 1 ≤ state.n))).2 = true →
              state.ok = true := by
          cases forward : gcForwardPtr ptr state.heap address value (state.ok && decide (len + 1 ≤ state.n)) with
          | mk heap1 status =>
            intro statusTrue
            change status = true at statusTrue
            subst status
            have check := gcForwardPtr_ok state.heap ptr address value
              (state.ok && decide (len + 1 ≤ state.n)) heap1 forward
            simp only [Bool.and_eq_true] at check
            exact check.1
        cases isRef : conf.isRef payload <;> simp only [gcMove, found, isRef, Bool.false_eq_true,
          ↓reduceIte] at run
        all_goals simp only [Prod.mk.injEq] at run
        all_goals obtain ⟨_, rfl⟩ := run
        all_goals exact forwardOk _ ok

/-- A successful root-list move started from a successful state. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "gc_move_list_ok"]
theorem gcMoveList_ok {α β : Type} (conf : Config β) (roots roots1 : List (HeapAddress α))
    (state state1 : GcState α β) (run : gcMoveList conf state roots = (roots1, state1))
    (ok : state1.ok = true) : state.ok = true := by
  induction roots generalizing state roots1 state1 with
  | nil =>
    simp only [gcMoveList, Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    exact ok
  | cons root roots ih =>
    simp only [gcMoveList] at run
    generalize headRun : gcMove conf state root = headResult at run
    rcases headResult with ⟨root1, middle⟩
    generalize tailRun : gcMoveList conf middle roots = tailResult at run
    rcases tailResult with ⟨tail, final⟩
    simp only [Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    exact gcMove_ok conf state middle root root1 headRun (ih (state := middle) (roots1 := tail) (state1 := final) tailRun ok)

/-- A successful reference scan started from a successful state. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "gc_move_refs_ok"]
theorem gcMoveRefs_ok {α β : Type} (conf : Config β) (state : GcState α β)
    (ok : (gcMoveRefs conf state).ok = true) : state.ok = true := by
  induction state using gcMoveRefs.induct conf with
  | case1 state empty =>
    cases state with
    | mk old h1 h2 r4 r3 r2 r1 a n status heap heap0 =>
      simp only at empty
      subst r2
      rw [gcMoveRefs] at ok
      exact ok
  | case2 state tail roots len payload refs roots1 middle move refsAgain ih =>
    cases state with
    | mk old h1 h2 r4 r3 r2 r1 a n status heap heap0 =>
      simp only at refs
      subst r2
      rw [gcMoveRefs] at ok
      simp only [move] at ok
      have middleOk := ih ok
      exact gcMoveList_ok conf roots roots1 _ middle move middleOk
  | case3 state head tail refs refsAgain notData =>
    cases head with
    | unused len =>
      cases state with
      | mk old h1 h2 r4 r3 r2 r1 a n status heap heap0 =>
        simp only at refs
        subst r2
        rw [gcMoveRefs] at ok
        contradiction
    | forwardPointer ptr value len =>
      cases state with
      | mk old h1 h2 r4 r3 r2 r1 a n status heap heap0 =>
        simp only at refs
        subst r2
        rw [gcMoveRefs] at ok
        contradiction
    | dataElement roots len payload =>
      exact False.elim (notData roots len payload refs rfl (by rfl))

/-- A successful data scan started from a successful state. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "gc_move_data_ok"]
theorem gcMoveData_ok {α β : Type} (conf : Config β) (state : GcState α β)
    (ok : (gcMoveData conf state).ok = true) : state.ok = true := by
  classical
  induction state using gcMoveData.induct conf with
  | case1 state empty => rw [gcMoveData] at ok; simpa [empty] using ok
  | case2 state head tail heap over => rw [gcMoveData] at ok; simp [heap, over] at ok
  | case3 state tail roots len payload roots1 middle move heap bounded flag ih =>
    cases state with
    | mk old h1 h2 r4 r3 r2 r1 a n status origHeap heap0 =>
      simp only at heap
      subst h2
      rw [gcMoveData] at ok
      simp only [bounded, ↓reduceIte, move] at ok
      have check := ih ok
      dsimp only [flag] at check
      simp only [Bool.and_eq_true] at check
      exact gcMoveList_ok conf roots roots1 _ middle move check.1.1
  | case4 state head tail heap bounded notData =>
    cases head with
    | unused len => rw [gcMoveData] at ok; simp [heap, bounded] at ok
    | forwardPointer ptr value len => rw [gcMoveData] at ok; simp [heap, bounded] at ok
    | dataElement roots len payload => exact False.elim (notData roots len payload rfl)

/-- A successful data scan has processed all pending data objects. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "gc_move_data_h2"]
theorem gcMoveData_h2 {α β : Type} (conf : Config β) (state : GcState α β)
    (ok : (gcMoveData conf state).ok = true) : (gcMoveData conf state).h2 = [] := by
  classical
  induction state using gcMoveData.induct conf with
  | case1 state empty => rw [gcMoveData]; simp [empty]
  | case2 state head tail heap over => rw [gcMoveData] at ok; simp [heap, over] at ok
  | case3 state tail roots len payload roots1 middle move heap bounded flag ih =>
    cases state with
    | mk old h1 h2 r4 r3 r2 r1 a n status origHeap heap0 =>
      simp only at heap
      subst h2
      rw [gcMoveData] at ok ⊢
      simp only [bounded, ↓reduceIte, move] at ok ⊢
      exact ih ok
  | case4 state head tail heap bounded notData =>
    cases head with
    | unused len => rw [gcMoveData] at ok; simp [heap, bounded] at ok
    | forwardPointer ptr value len => rw [gcMoveData] at ok; simp [heap, bounded] at ok
    | dataElement roots len payload => exact False.elim (notData roots len payload rfl)

end Flapjack.Compiler.Backend.GenGc
