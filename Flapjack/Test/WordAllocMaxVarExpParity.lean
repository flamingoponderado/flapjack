import Flapjack.Compiler.Backend.WordAlloc.Proofs.MaxVarExp
namespace Flapjack.Test.WordAllocMaxVarExpParity
open Flapjack.Compiler.Backend.WordAlloc
-- Original me_const
private def me_const : WordLangExpHOL (BitVec 64) := .const 999
example : maxVarExpHOL me_const = 0 ∧
    everyVarExpHOL (fun x => decide (x ≤ maxVarExpHOL me_const)) me_const = true ∧
    everyVarExpHOL (fun x => decide (x < maxVarExpHOL me_const)) me_const = true := by
  exact ⟨by decide +kernel, maxVarExpMax _, by decide +kernel⟩
-- Original me_lookup
private def me_lookup : WordLangExpHOL (BitVec 64) := .lookup .currHeap
example : maxVarExpHOL me_lookup = 0 ∧
    everyVarExpHOL (fun x => decide (x ≤ maxVarExpHOL me_lookup)) me_lookup = true ∧
    everyVarExpHOL (fun x => decide (x < maxVarExpHOL me_lookup)) me_lookup = true := by
  exact ⟨by decide +kernel, maxVarExpMax _, by decide +kernel⟩
-- Original me_var
private def me_var : WordLangExpHOL (BitVec 64) := .var (2^80)
example : maxVarExpHOL me_var = 1208925819614629174706176 ∧
    everyVarExpHOL (fun x => decide (x ≤ maxVarExpHOL me_var)) me_var = true ∧
    everyVarExpHOL (fun x => decide (x < maxVarExpHOL me_var)) me_var = false := by
  exact ⟨by decide +kernel, maxVarExpMax _, by decide +kernel⟩
-- Original me_load
private def me_load : WordLangExpHOL (BitVec 32) := .load (.load (.var 7))
example : maxVarExpHOL me_load = 7 ∧
    everyVarExpHOL (fun x => decide (x ≤ maxVarExpHOL me_load)) me_load = true ∧
    everyVarExpHOL (fun x => decide (x < maxVarExpHOL me_load)) me_load = false := by
  exact ⟨by decide +kernel, maxVarExpMax _, by decide +kernel⟩
-- Original me_empty
private def me_empty : WordLangExpHOL (BitVec 64) := .op .add []
example : maxVarExpHOL me_empty = 0 ∧
    everyVarExpHOL (fun x => decide (x ≤ maxVarExpHOL me_empty)) me_empty = true ∧
    everyVarExpHOL (fun x => decide (x < maxVarExpHOL me_empty)) me_empty = true := by
  exact ⟨by decide +kernel, maxVarExpMax _, by decide +kernel⟩
-- Original me_nested
private def me_nested : WordLangExpHOL (BitVec 64) := .op .add [.var 2,.op .sub [.var 19,.var 3],.load (.var 7)]
example : maxVarExpHOL me_nested = 19 ∧
    everyVarExpHOL (fun x => decide (x ≤ maxVarExpHOL me_nested)) me_nested = true ∧
    everyVarExpHOL (fun x => decide (x < maxVarExpHOL me_nested)) me_nested = false := by
  exact ⟨by decide +kernel, maxVarExpMax _, by decide +kernel⟩
-- Original me_duplicate
private def me_duplicate : WordLangExpHOL (BitVec 80) := .op .add [.var 9,.var 9,.var 2]
example : maxVarExpHOL me_duplicate = 9 ∧
    everyVarExpHOL (fun x => decide (x ≤ maxVarExpHOL me_duplicate)) me_duplicate = true ∧
    everyVarExpHOL (fun x => decide (x < maxVarExpHOL me_duplicate)) me_duplicate = false := by
  exact ⟨by decide +kernel, maxVarExpMax _, by decide +kernel⟩
-- Original me_shiftleft
private def me_shiftleft : WordLangExpHOL (BitVec 64) := .shift .lsl (.var 23) (.var 4)
example : maxVarExpHOL me_shiftleft = 23 ∧
    everyVarExpHOL (fun x => decide (x ≤ maxVarExpHOL me_shiftleft)) me_shiftleft = true ∧
    everyVarExpHOL (fun x => decide (x < maxVarExpHOL me_shiftleft)) me_shiftleft = false := by
  exact ⟨by decide +kernel, maxVarExpMax _, by decide +kernel⟩
-- Original me_shiftright
private def me_shiftright : WordLangExpHOL (BitVec 1) := .shift .lsr (.const 1) (.var 43)
example : maxVarExpHOL me_shiftright = 43 ∧
    everyVarExpHOL (fun x => decide (x ≤ maxVarExpHOL me_shiftright)) me_shiftright = true ∧
    everyVarExpHOL (fun x => decide (x < maxVarExpHOL me_shiftright)) me_shiftright = false := by
  exact ⟨by decide +kernel, maxVarExpMax _, by decide +kernel⟩
-- Original me_zero
private def me_zero : WordLangExpHOL (BitVec 64) := .op .add [.const 99,.lookup .currHeap,.op .sub []]
example : maxVarExpHOL me_zero = 0 ∧
    everyVarExpHOL (fun x => decide (x ≤ maxVarExpHOL me_zero)) me_zero = true ∧
    everyVarExpHOL (fun x => decide (x < maxVarExpHOL me_zero)) me_zero = true := by
  exact ⟨by decide +kernel, maxVarExpMax _, by decide +kernel⟩
end Flapjack.Test.WordAllocMaxVarExpParity
