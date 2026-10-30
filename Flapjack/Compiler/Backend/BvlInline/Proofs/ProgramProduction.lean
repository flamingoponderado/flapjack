import Flapjack.Compiler.Backend.BvlInline.Program
import Flapjack.Compiler.Backend.BvlInline.Proofs.RecursionProduction

/-! The production and original-shaped BVL program inliners agree. -/
namespace Flapjack.Compiler.Backend.BvlInline
open Bvl

/-- Accumulating a prefix is equivalent to prepending it after a run. This
helper has no standalone HOL declaration. -/
theorem tickInlineAll_acc (limit : Nat) (program : List (Nat × Nat × Exp))
    (cache : Spt (Nat × Exp)) (acc : List (Nat × Nat × Exp)) :
    tickInlineAll limit cache program acc =
      let result := tickInlineAll limit cache program []
      (result.1, acc.reverse ++ result.2) := by
  induction program generalizing cache acc with
  | nil => simp [tickInlineAll]
  | cons entry rest ih =>
    obtain ⟨name, arity, body⟩ := entry
    simp only [tickInlineAll]
    rw [ih _ ((name, arity, tickInlineSing cache body) :: acc),
      ih _ [(name, arity, tickInlineSing cache body)]]
    simp [List.reverse_cons, List.append_assoc]

/-- For every program and fuel, the executed inliner produces the same
cache and program as the total source traversal. This executable
correspondence has no standalone HOL declaration. -/
theorem tickInlineAllFuel_eq (fuel limit : Nat) (cache : Spt (Nat × Exp))
    (program : List (Nat × Nat × Exp)) :
    tickInlineAllFuel fuel limit cache program = some (tickCompileProg limit cache program) := by
  induction program generalizing cache with
  | nil => simp [tickInlineAllFuel, tickCompileProg, tickInlineAll]
  | cons entry rest ih =>
    obtain ⟨name, arity, body⟩ := entry
    simp only [tickInlineAllFuel, inlineExpBounded_eq]
    simp only [bind, Option.bind]
    rw [tickCompileProg, tickInlineAll, tickInlineAll_acc]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    simp [smallExpBounded_eq, recursiveBounded_eq, mustInline, isSmall, isRec, isRecList, ih]
    by_cases zero : isSmallSing limit (tickInlineSing cache body) = 0 <;>
      simp [zero, tickCompileProg]

/-- Inlining preserves program entry names and accumulator order. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "tick_inline_all_names"]
theorem tickInlineAllNames {A : Type} (limit : Nat) (cache : Spt (Nat × Exp))
    (program : List (Nat × Nat × Exp)) (_unused : A) (finalCache : Spt (Nat × Exp))
    (output acc : List (Nat × Nat × Exp))
    (run : tickInlineAll limit cache program acc = (finalCache, output)) :
    acc.reverse.map Prod.fst ++ program.map Prod.fst = output.map Prod.fst := by
  induction program generalizing cache acc with
  | nil =>
    simp [tickInlineAll] at run
    rcases run with ⟨_, rfl⟩
    simp
  | cons entry rest ih =>
    obtain ⟨name, arity, body⟩ := entry
    simp only [tickInlineAll] at run
    have result := ih _ _ run
    simpa [List.reverse_cons, List.map_append, List.append_assoc] using result

end Flapjack.Compiler.Backend.BvlInline
