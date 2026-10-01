import Flapjack.Pancake.WordConvs.ProgramMonotonicity
namespace Flapjack.Test.WordConvsProgramMonoParity
private def pm_skip : WordLangProgHOL (BitVec 1) := .skip
example : everyVarHOL (fun x => decide (x ≤ 0)) pm_skip = true ∧
    everyVarHOL (fun x => decide (x ≤ 1)) pm_skip = true := by
  have h : everyVarHOL (fun x => decide (x ≤ 0)) pm_skip = true := by decide +kernel
  exact ⟨h, everyVarMono _ _ _ ⟨by intro x hx; simp only [decide_eq_true_eq] at hx ⊢; omega, h⟩⟩
private def pm_moves : WordLangProgHOL (BitVec 32) := .move 99 [(1,3),(3,2)]
example : everyVarHOL (fun x => decide (x ≤ 3)) pm_moves = true ∧
    everyVarHOL (fun x => decide (x ≤ 9)) pm_moves = true := by
  have h : everyVarHOL (fun x => decide (x ≤ 3)) pm_moves = true := by decide +kernel
  exact ⟨h, everyVarMono _ _ _ ⟨by intro x hx; simp only [decide_eq_true_eq] at hx ⊢; omega, h⟩⟩
private def pm_inst : WordLangProgHOL (BitVec 64) := .inst (.const 7 123)
example : everyVarHOL (fun x => decide (x ≤ 7)) pm_inst = true ∧
    everyVarHOL (fun x => decide (x ≤ 8)) pm_inst = true := by
  have h : everyVarHOL (fun x => decide (x ≤ 7)) pm_inst = true := by decide +kernel
  exact ⟨h, everyVarMono _ _ _ ⟨by intro x hx; simp only [decide_eq_true_eq] at hx ⊢; omega, h⟩⟩
private def pm_assign : WordLangProgHOL (BitVec 80) := .assign 4 (.load (.var 8))
example : everyVarHOL (fun x => decide (x ≤ 8)) pm_assign = true ∧
    everyVarHOL (fun x => decide (x ≤ 99)) pm_assign = true := by
  have h : everyVarHOL (fun x => decide (x ≤ 8)) pm_assign = true := by decide +kernel
  exact ⟨h, everyVarMono _ _ _ ⟨by intro x hx; simp only [decide_eq_true_eq] at hx ⊢; omega, h⟩⟩
private def pm_seq : WordLangProgHOL (BitVec 64) := .seq (.set .currHeap (.var 5)) (.store (.var 9) 3)
example : everyVarHOL (fun x => decide (x ≤ 9)) pm_seq = true ∧
    everyVarHOL (fun x => decide (x ≤ 99)) pm_seq = true := by
  have h : everyVarHOL (fun x => decide (x ≤ 9)) pm_seq = true := by decide +kernel
  exact ⟨h, everyVarMono _ _ _ ⟨by intro x hx; simp only [decide_eq_true_eq] at hx ⊢; omega, h⟩⟩
private def pm_alloc : WordLangProgHOL (BitVec 1) := .alloc 0 (.ls (), .ln)
example : everyVarHOL (fun x => decide (x ≤ 0)) pm_alloc = true ∧
    everyVarHOL (fun x => decide (x ≤ 1)) pm_alloc = true := by
  have h : everyVarHOL (fun x => decide (x ≤ 0)) pm_alloc = true := by decide +kernel
  exact ⟨h, everyVarMono _ _ _ ⟨by intro x hx; simp only [decide_eq_true_eq] at hx ⊢; omega, h⟩⟩
private def pm_loop : WordLangProgHOL (BitVec 32) := .loop (.ls ()) (.mustTerminate (.return 2 [1,3])) (.ls ())
example : everyVarHOL (fun x => decide (x ≤ 3)) pm_loop = true ∧
    everyVarHOL (fun x => decide (x ≤ 7)) pm_loop = true := by
  have h : everyVarHOL (fun x => decide (x ≤ 3)) pm_loop = true := by decide +kernel
  exact ⟨h, everyVarMono _ _ _ ⟨by intro x hx; simp only [decide_eq_true_eq] at hx ⊢; omega, h⟩⟩
private def pm_call_none : WordLangProgHOL (BitVec 64) := .call none (some 999) [2] (some (999,.assign 999 (.var 999),999,999))
example : everyVarHOL (fun x => decide (x ≤ 2)) pm_call_none = true ∧
    everyVarHOL (fun x => decide (x ≤ 4)) pm_call_none = true := by
  have h : everyVarHOL (fun x => decide (x ≤ 2)) pm_call_none = true := by decide +kernel
  exact ⟨h, everyVarMono _ _ _ ⟨by intro x hx; simp only [decide_eq_true_eq] at hx ⊢; omega, h⟩⟩
private def pm_call_return : WordLangProgHOL (BitVec 80) := .call (some ([1,2],(.ls (),.ln),.assign 3 (.var 4),999,999)) none [2] none
example : everyVarHOL (fun x => decide (x ≤ 4)) pm_call_return = true ∧
    everyVarHOL (fun x => decide (x ≤ 8)) pm_call_return = true := by
  have h : everyVarHOL (fun x => decide (x ≤ 4)) pm_call_return = true := by decide +kernel
  exact ⟨h, everyVarMono _ _ _ ⟨by intro x hx; simp only [decide_eq_true_eq] at hx ⊢; omega, h⟩⟩
private def pm_call_handler : WordLangProgHOL (BitVec 64) := .call (some ([1],(.ln,.ls ()),.assign 3 (.var 4),999,999)) (some 999) [2] (some (5,.assign 6 (.var 7),999,999))
example : everyVarHOL (fun x => decide (x ≤ 7)) pm_call_handler = true ∧
    everyVarHOL (fun x => decide (x ≤ 9)) pm_call_handler = true := by
  have h : everyVarHOL (fun x => decide (x ≤ 7)) pm_call_handler = true := by decide +kernel
  exact ⟨h, everyVarMono _ _ _ ⟨by intro x hx; simp only [decide_eq_true_eq] at hx ⊢; omega, h⟩⟩
example : everyVarHOL (fun x => decide (x ≤ 7)) (WordLangProgHOL.assign 7 (.var 7) : WordLangProgHOL (BitVec 64)) = true ∧
    everyVarHOL (fun x => decide (x ≤ 3)) (WordLangProgHOL.assign 7 (.var 7) : WordLangProgHOL (BitVec 64)) = false := by decide +kernel
end Flapjack.Test.WordConvsProgramMonoParity
