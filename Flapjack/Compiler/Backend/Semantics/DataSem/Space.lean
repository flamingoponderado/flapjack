module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Heap
public import Flapjack.Compiler.Backend.DataSpace.Requirements
public import Flapjack.Misc.Integer

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Data-language operation space requirements and accounting. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack
open Classical

private def bignumLimit (limits : Limits) (a b : Int) : Nat :=
  2 * bignumSize limits.arch64Bit a + 2 * bignumSize limits.arch64Bit b

/-- The source's operation-specific upper bound on heap allocation. HOL's
integer division and remainder remain unspecified at a zero divisor. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "space_consumed_def"]
noncomputable def spaceConsumed {C F : Type} (state : State C F) : ClosLang.Op → List Value → Nat
  | .blockOp (.consExtend _), .block _ _ xs' :: .number lower :: .number len :: .number _ :: xs =>
      (xs ++ (xs'.drop lower.toNat).take len.toNat).length + 1
  | .memOp .refArray, [.number len, _] => len.toNat + 1
  | .memOp (.refByte _), [.number len, _] => len.toNat / (archSize state.limits / 8) + 2
  | .blockOp (.fromList _), [.number len, _] => len.toNat + 1
  | .intOp .add, [.number a, .number b] =>
      if smallNum state.limits.arch64Bit a ∧ smallNum state.limits.arch64Bit b ∧
         smallNum state.limits.arch64Bit (a + b) then 0 else bignumLimit state.limits a b
  | .intOp .sub, [.number a, .number b] =>
      if smallNum state.limits.arch64Bit a ∧ smallNum state.limits.arch64Bit b ∧
         smallNum state.limits.arch64Bit (a - b) then 0 else bignumLimit state.limits a b
  | .intOp .mult, [.number a, .number b] =>
      if smallNum state.limits.arch64Bit a ∧ 0 ≤ a ∧ smallNum state.limits.arch64Bit b ∧ 0 ≤ b ∧
         smallNum state.limits.arch64Bit (a * b) then 0 else bignumLimit state.limits a b
  | .intOp .div, [.number a, .number b] =>
      if smallNum state.limits.arch64Bit a ∧ 0 ≤ a ∧ smallNum state.limits.arch64Bit b ∧ 0 ≤ b ∧
         smallNum state.limits.arch64Bit (holIntDiv a b) then 0 else bignumLimit state.limits a b
  | .intOp .mod, [.number a, .number b] =>
      if smallNum state.limits.arch64Bit a ∧ 0 ≤ a ∧ smallNum state.limits.arch64Bit b ∧ 0 ≤ b ∧
         smallNum state.limits.arch64Bit (holIntMod a b) then 0 else bignumLimit state.limits a b
  | .blockOp .listAppend, [value, _] =>
      match valueToList value with
      | none => 0
      | some values => (values.length + 1) * 3
  | _, _ => 0

/-- Reset or consume reserved space, accounting for explicit operation roots. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "do_space_def"]
noncomputable def doSpace {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state : State C F) : Option (State C F) :=
  if DataLang.opSpaceReset op then
    let used := sizeOfHeapArgs values state + spaceConsumed state op values
    let safe := state.safeForSpace && decide (noThunksInRefs state.refs ∧ used ≤ state.limits.heapLimit)
    some { state with space := 0, safeForSpace := safe, peakHeapLength := max state.peakHeapLength used }
  else
    let required := DataSpace.opSpaceReq op values.length
    if required = 0 then some state else consumeSpace required state

end Flapjack.Compiler.Backend.DataSem
