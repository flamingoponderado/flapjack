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

end Flapjack.Compiler.Backend.GenGc
