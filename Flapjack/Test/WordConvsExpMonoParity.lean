import Flapjack.Pancake.WordConvs.ExpressionMonotonicity
namespace Flapjack.Test.WordConvsExpMonoParity
-- Original em_var
private def em_var : WordLangExpHOL (BitVec 64) := .var 3
example : everyVarExpHOL (fun x => decide (x ≤ 3)) em_var = true ∧
    everyVarExpHOL (fun x => decide (x ≤ 9)) em_var = true := by
  have hp : everyVarExpHOL (fun x => decide (x ≤ 3)) em_var = true := by decide +kernel
  exact ⟨hp, everyVarExpMono _ _ _ ⟨by intro x hx; simp_all <;> omega, hp⟩⟩
-- Original em_nested
private def em_nested : WordLangExpHOL (BitVec 64) := .op .add [.var 2,.load (.var 7),.shift .lsl (.var 9) (.var 1)]
example : everyVarExpHOL (fun x => decide (x ≤ 9)) em_nested = true ∧
    everyVarExpHOL (fun x => decide (x ≤ 99)) em_nested = true := by
  have hp : everyVarExpHOL (fun x => decide (x ≤ 9)) em_nested = true := by decide +kernel
  exact ⟨hp, everyVarExpMono _ _ _ ⟨by intro x hx; simp_all <;> omega, hp⟩⟩
-- Original em_empty
private def em_empty : WordLangExpHOL (BitVec 1) := .op .sub []
example : everyVarExpHOL (fun x => decide (x ≤ 0)) em_empty = true ∧
    everyVarExpHOL (fun x => decide (x ≤ 0)) em_empty = true := by
  have hp : everyVarExpHOL (fun x => decide (x ≤ 0)) em_empty = true := by decide +kernel
  exact ⟨hp, everyVarExpMono _ _ _ ⟨by intro x hx; simp_all <;> omega, hp⟩⟩
-- Original em_const
private def em_const : WordLangExpHOL (BitVec 32) := .const 999
example : everyVarExpHOL (fun x => decide (x ≤ 0)) em_const = true ∧
    everyVarExpHOL (fun x => decide (x ≤ 1)) em_const = true := by
  have hp : everyVarExpHOL (fun x => decide (x ≤ 0)) em_const = true := by decide +kernel
  exact ⟨hp, everyVarExpMono _ _ _ ⟨by intro x hx; simp_all <;> omega, hp⟩⟩
-- Original em_lookup
private def em_lookup : WordLangExpHOL (BitVec 64) := .lookup .currHeap
example : everyVarExpHOL (fun x => decide (x ≤ 0)) em_lookup = true ∧
    everyVarExpHOL (fun x => decide (x ≤ 0)) em_lookup = true := by
  have hp : everyVarExpHOL (fun x => decide (x ≤ 0)) em_lookup = true := by decide +kernel
  exact ⟨hp, everyVarExpMono _ _ _ ⟨by intro x hx; simp_all <;> omega, hp⟩⟩
-- Original em_duplicate
private def em_duplicate : WordLangExpHOL (BitVec 80) := .op .add [.var 4,.var 4,.op .sub [.var 1]]
example : everyVarExpHOL (fun x => decide (x ≤ 4)) em_duplicate = true ∧
    everyVarExpHOL (fun x => decide (x ≤ 8)) em_duplicate = true := by
  have hp : everyVarExpHOL (fun x => decide (x ≤ 4)) em_duplicate = true := by decide +kernel
  exact ⟨hp, everyVarExpMono _ _ _ ⟨by intro x hx; simp_all <;> omega, hp⟩⟩
-- Original em_large
private def em_large : WordLangExpHOL (BitVec 64) := .load (.var (2^80))
example : everyVarExpHOL (fun x => decide (x ≤ 1208925819614629174706176)) em_large = true ∧
    everyVarExpHOL (fun x => decide (x ≤ 2417851639229258349412352)) em_large = true := by
  have hp : everyVarExpHOL (fun x => decide (x ≤ 1208925819614629174706176)) em_large = true := by decide +kernel
  exact ⟨hp, everyVarExpMono _ _ _ ⟨by intro x hx; simp_all <;> omega, hp⟩⟩
-- Original em_guard_needed
private def em_guard_needed : WordLangExpHOL (BitVec 64) := .var 7
example : everyVarExpHOL (fun x => decide (x ≤ 9)) em_guard_needed = true ∧
    everyVarExpHOL (fun x => decide (x ≤ 3)) em_guard_needed = false := by decide +kernel
end Flapjack.Test.WordConvsExpMonoParity
