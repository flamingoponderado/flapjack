import Flapjack.Misc.FindIndex.SuccessfulMembership
import Flapjack.Compiler.Backend.Semantics.TargetSem.State

namespace Flapjack.Test.MiscFindIndexSuccessfulMemParity
open Flapjack Flapjack.Misc

example {α : Type} [DecidableEq α] (target : α) (values : List α)
    (offset index : Nat) : findIndex target values offset = some index →
      target ∈ values := findIndex_isMem target values offset index

example {width : Nat} [NeZero width] {state projection : Type}
    (mc : MachineConfig width state projection) (target : BitVec width)
    (offset index : Nat) (hs : findIndex target mc.ffiEntryPcs offset = some index) :
    target ∈ mc.ffiEntryPcs := findIndex_isMem _ _ _ _ hs

example : (7 : Nat) ∈ [7,13] := findIndex_isMem _ _ 0 0 (by decide)
example : (13 : Nat) ∈ [7,13] := findIndex_isMem _ _ 10 11 (by decide)
example : (7 : Nat) ∈ [7,7] := findIndex_isMem _ _ 10 10 (by decide)
example : (13 : Nat) ∈ [7,13] := findIndex_isMem _ _ (2^80) (2^80+1) (by decide)
example : "b" ∈ ["a","b","b"] := findIndex_isMem _ _ 10 11 (by decide)
example : (13 : BitVec 80) ∈ [7,13] := findIndex_isMem _ _ 10 11 (by decide)
example : findIndex (8 : Nat) [7,13] 10 = none := by decide
example : findIndex (7 : Nat) [] 10 = none := by decide

end Flapjack.Test.MiscFindIndexSuccessfulMemParity
