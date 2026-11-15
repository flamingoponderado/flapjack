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

/-- The source's post-reset heap-space safety test. HOL renders it as the
`Overload do_space_safe` (`dataSemScript.sml:405`), which is not a database
declaration, so this definition carries no `@[hol]` tag. -/
noncomputable def doSpaceSafe {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state : State C F) : Bool :=
  if DataLang.opSpaceReset op then
    state.safeForSpace && decide (noThunksInRefs state.refs ∧
      sizeOfHeapArgs values state + spaceConsumed state op values ≤ state.limits.heapLimit)
  else state.safeForSpace

/-- The source's post-reset peak-heap estimate. HOL renders it as the
`Overload do_space_peak` (`dataSemScript.sml:414`), so this definition carries
no `@[hol]` tag. -/
noncomputable def doSpacePeak {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state : State C F) : Nat :=
  if DataLang.opSpaceReset op then
    max state.peakHeapLength (sizeOfHeapArgs values state + spaceConsumed state op values)
  else state.peakHeapLength

/-- A zero space requirement is always satisfied, so consuming it is inert. -/
theorem consumeSpace_zero {C F : Type} (state : State C F) :
    consumeSpace 0 state = some state := by
  simp [consumeSpace]

/-- Exact HOL `do_space_alt` (`dataPropsScript.sml:443`): the reset branch is the
`do_space_safe`/`do_space_peak` pair, and the other branch consumes the
requirement, which includes the zero requirement (`consume_space 0 s = SOME s`). -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_space_alt"]
theorem doSpaceAlt {C F : Type} (op : ClosLang.Op) (values : List Value) (state : State C F) :
    doSpace op values state =
      if DataLang.opSpaceReset op then
        some { state with
          space := 0
          safeForSpace := doSpaceSafe op values state
          peakHeapLength := doSpacePeak op values state }
      else consumeSpace (DataSpace.opSpaceReq op values.length) state := by
  simp only [doSpace, doSpaceSafe, doSpacePeak]
  split
  · rfl
  · split
    · rename_i hreq
      rw [hreq, consumeSpace_zero]
    · rfl

end Flapjack.Compiler.Backend.DataSem
