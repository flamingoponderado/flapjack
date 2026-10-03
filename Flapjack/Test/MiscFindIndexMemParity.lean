import Flapjack.Misc.FindIndex.Membership
import Flapjack.Compiler.Backend.Semantics.TargetSem.State
namespace Flapjack.Test.MiscFindIndexMemParity
open Flapjack Flapjack.Misc
example {α : Type} [DecidableEq α] [Nonempty α] (values : List α)
    (target : α) (offset : Nat) : target ∈ values → ∃ index,
    findIndex target values offset = some (offset+index) ∧
      index < values.length ∧ holEl index values = target := findIndex_mem values target offset
example {width : Nat} [NeZero width] {state projection : Type}
    (mc : MachineConfig width state projection) (target : BitVec width) (offset : Nat)
    (hm : target ∈ mc.ffiEntryPcs) : ∃ index,
    findIndex target mc.ffiEntryPcs offset = some (offset+index) ∧
      index < mc.ffiEntryPcs.length ∧ holEl index mc.ffiEntryPcs = target := by
  letI : Nonempty (BitVec width) := ⟨0⟩
  exact findIndex_mem _ _ _ hm
example : findIndex 7 [7,13] 0 = some 0 := by decide
example : findIndex 13 [7,13] 0 = some 1 := by decide
example : findIndex 13 [7,13] 10 = some 11 := by decide
example : findIndex 7 [7,7] 10 = some 10 := by decide
example : findIndex 13 [7,13] (2^80) = some (2^80+1) := by decide
example : findIndex "b" ["a","b","b"] 10 = some 11 := by decide
example : findIndex (13 : BitVec 80) [7,13] 10 = some 11 := by decide
example : (8 : Nat) ∉ [7,13] := by decide
example : (7 : Nat) ∉ [] := by decide
end Flapjack.Test.MiscFindIndexMemParity
