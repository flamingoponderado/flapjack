import Flapjack.Compiler.Backend.GcShared

/-! Status preservation for abstract forwarding-pointer updates. -/
namespace Flapjack.Compiler.Backend

@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "gc_forward_ptr_ok"]
theorem gcForwardPtr_ok {α β : Type} (heap : List (HeapElement α β))
    (offset address : Nat) (value : α) (ok : Bool) (result : List (HeapElement α β))
    (run : gcForwardPtr offset heap address value ok = (result, true)) : ok = true := by
  induction heap generalizing offset result with
  | nil => simp [gcForwardPtr] at run
  | cons head tail ih =>
    simp only [gcForwardPtr] at run
    split at run
    · cases head <;> simp_all
    · split at run
      · simp at run
      · cases next : gcForwardPtr (offset - elLength head) tail address value ok with
        | mk tail' status =>
          simp only [next, Prod.mk.injEq] at run
          obtain ⟨_, rfl⟩ := run
          exact ih _ tail' next

end Flapjack.Compiler.Backend
