import Flapjack.Compiler.Backend.SourceToFlat.Proofs.GlobalWeakening

/-! Kernel checks for the slot behavior captured by the pinned HOL probe. -/
namespace Flapjack.Test.CakeSubglobalsParity
open Flapjack.Compiler.Backend.SourceToFlat

example : subglobals ([some 1, none] : List (Option Nat)) [some 1, some 2] := by
  constructor
  · simp
  · intro n ⟨bound, initialized⟩
    have cases : n = 0 ∨ n = 1 := by simp at bound; omega
    rcases cases with rfl | rfl <;> simp_all

example : subglobals ([some 1, none] : List (Option Nat)) [some 1, some 2, some 3] := by
  constructor
  · simp
  · intro n ⟨bound, initialized⟩
    have cases : n = 0 ∨ n = 1 := by simp at bound; omega
    rcases cases with rfl | rfl <;> simp_all

example : ¬ subglobals ([none, none] : List (Option Nat)) [none] := by
  intro h
  have := h.1
  simp at this

example : ¬ subglobals ([some 1, none] : List (Option Nat)) [some 2, none] := by
  intro h
  have bad := h.2 0 (by simp)
  simp at bad

example : ¬ subglobals ([some 1] : List (Option Nat)) [none] := by
  intro h
  have bad := h.2 0 (by simp)
  simp at bad

end Flapjack.Test.CakeSubglobalsParity
