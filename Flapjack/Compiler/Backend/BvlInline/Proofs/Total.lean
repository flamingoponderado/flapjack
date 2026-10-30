import Flapjack.Compiler.Backend.BvlInline.Proofs.TraversalTotal
import Flapjack.Compiler.Backend.BvlInline.Proofs.SmallTotal
import Flapjack.Compiler.Backend.BvlInline.Proofs.RecursiveTotal

/-! Totality of the checked BVL inliner through let-operation reduction.
HOL correspondence and handler-pass correctness remain separate obligations. -/
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

/-- Inlining and cache construction succeed on every program. -/
theorem tickInlineAllFuel_succeeds (fuel limit : Nat) (cache : Spt (Nat × Exp))
    (prog : List (Nat × Nat × Exp)) : ∃ result, tickInlineAllFuel fuel limit cache prog = some result := by
  induction prog generalizing cache with
  | nil => exact ⟨_, rfl⟩
  | cons p ps ih =>
    obtain ⟨name, arity, body⟩ := p
    obtain ⟨body', hb⟩ := inlineExpBounded_succeeds fuel cache body
    obtain ⟨size, hs⟩ := smallExpBounded_succeeds fuel limit body'
    obtain ⟨recurs, hr⟩ := recursiveBounded_succeeds fuel name body'
    by_cases zero : size = 0
    · obtain ⟨⟨next, rest⟩, hn⟩ := ih cache
      exact ⟨_, by simp [tickInlineAllFuel, hb, hs, zero, hn]; rfl⟩
    · obtain ⟨⟨next, rest⟩, hn⟩ := ih (if size != 0 && !recurs then
        sptInsert name (arity, body') cache else cache)
      cases recurs <;> simp_all [tickInlineAllFuel] <;> exact ⟨_, rfl⟩

/-- The inlining, tick-removal, and let-operation portion of the production
pipeline cannot fail from traversal fuel. The later handler pass is separate. -/
theorem compileWithoutHandleFuel_succeeds (fuel limit : Nat) (prog : List (Nat × Nat × Exp)) :
    ∃ result, compileWithoutHandleFuel fuel limit prog = some result := by
  obtain ⟨⟨cache, code⟩, h⟩ := tickInlineAllFuel_succeeds fuel limit .ln prog
  obtain ⟨code', hc⟩ := mapM_succeeds code (fun p => do
    let body ← removeTicksBounded fuel p.2.2
    pure (p.1, p.2.1, ← letOpBounded fuel body)) (by
      intro p _
      obtain ⟨name, arity, body⟩ := p
      obtain ⟨body', hb⟩ := removeTicksBounded_succeeds fuel body
      obtain ⟨body'', hl⟩ := letOpBounded_succeeds fuel body'
      exact ⟨_, by simp [hb, hl]; rfl⟩)
  refine ⟨(cache, code'), ?_⟩
  unfold compileWithoutHandleFuel
  rw [h]
  change (code.mapM (fun (p : Nat × Nat × Exp) => do
    let body ← removeTicksBounded fuel p.2.2
    pure (p.1, p.2.1, ← letOpBounded fuel body))).bind
      (fun result => some (cache, result)) = some (cache, code')
  rw [hc]
  rfl

end Flapjack.Compiler.Backend.BvlInline
