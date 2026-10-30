import Flapjack.Compiler.Backend.BvlInline.Proofs.Total
import Flapjack.Compiler.Backend.BvlHandle.Proofs.Total

/-! Fuel sufficiency of the complete executable BVL inlining pipeline.
This does not establish HOL correspondence or pass correctness. -/
namespace Flapjack.Compiler.Backend.BvlInline
open Bvl

private theorem mapM_succeeds {α β : Type} (xs : List α) (f : α → Option β)
    (h : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := ih (by intro z hz; exact h z (by simp [hz]))
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

/-- The full executable BVL inlining and handler pipeline cannot fail from
traversal fuel, for any input program or caller budget. -/
theorem compileProgFuel_succeeds (fuel inlineLimit cutSize : Nat) (splitSeq : Bool)
    (prog : List (Nat × Nat × Exp)) :
    ∃ result, compileProgFuel fuel inlineLimit cutSize splitSeq prog = some result := by
  obtain ⟨⟨cache, code⟩, h⟩ := compileWithoutHandleFuel_succeeds fuel inlineLimit prog
  obtain ⟨code', hc⟩ := mapM_succeeds code (fun p => do
    pure (p.1, p.2.1, ← BvlHandle.compileAnyFuel fuel splitSeq cutSize p.2.1 p.2.2)) (by
      intro p _
      obtain ⟨name, arity, body⟩ := p
      obtain ⟨body', hb⟩ := BvlHandle.compileAnyFuel_succeeds fuel splitSeq cutSize arity body
      exact ⟨_, by simp [hb]; rfl⟩)
  refine ⟨(cache, code'), ?_⟩
  unfold compileProgFuel
  rw [h]
  change (code.mapM (fun (p : Nat × Nat × Exp) => do
    pure (p.1, p.2.1, ← BvlHandle.compileAnyFuel fuel splitSeq cutSize p.2.1 p.2.2))).bind
      (fun result => some (cache, result)) = some (cache, code')
  rw [hc]
  rfl

end Flapjack.Compiler.Backend.BvlInline
