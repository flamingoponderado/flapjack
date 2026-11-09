module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Control
public import Flapjack.Compiler.Backend.DataToWord.CallTree
public import Flapjack.Compiler.Backend.DataToWord.Locations
public import Flapjack.Misc.Integer

@[expose] public section

/-! Data-language stack-space accounting. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.Compiler.Backend.DataToWord
open Classical

/-- Count the structural size of a value's block tree. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "vb_size_def"]
def valueBlockSize : Value → Nat
  | .block _ tag values => 1 + tag + (values.map valueBlockSize).sum + values.length
  | _ => 1
termination_by value => sizeOf value

mutual
/-- Maximum nested block depth in a value. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "vs_depth_def"]
def valueDepth : Value → Nat
  | .block _ _ values => valuesDepth values
  | _ => 0
termination_by value => sizeOf value

/-- Maximum nested block depth in a list of values. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "vs_depth_def"]
def valuesDepth : List Value → Nat
  | [] => 0
  | x :: xs => max (1 + valueDepth x) (valuesDepth xs)
termination_by values => sizeOf values
end

/-- Stack bound for equality and comparison runtime helpers. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "eq_code_stack_max_def"]
def eqCodeStackMax (depth : Nat) (sizes : Spt Nat) : Option Nat :=
  (Option.map₂ max (sptLookup equalLocation sizes)
    (Option.map₂ max (sptLookup equal1Location sizes) (sptLookup compare1Location sizes))).map (depth * ·)

/-- Original stack bound for each data-language operation. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "stack_consumed_def"]
noncomputable def stackConsumed (sizes : Spt Nat) (limits : Limits) : ClosLang.Op → List Value → Option Nat
  | .memOp (.copyByte _), _ =>
      Option.map₂ max (sptLookup byteCopyLocation sizes)
        (Option.map₂ max (sptLookup byteCopyAddLocation sizes) (sptLookup byteCopySubLocation sizes))
  | .memOp (.refByte _), _ => Option.map₂ max (sptLookup refByteLocation sizes) (sptLookup replicateLocation sizes)
  | .memOp .refArray, _ => Option.map₂ max (sptLookup refArrayLocation sizes) (sptLookup replicateLocation sizes)
  | .memOp .xorByte, _ => sptLookup xorLoopLocation sizes
  | .memOp (.stringCmp _ _), _ => sptLookup stringCmpLoopLocation sizes
  | .blockOp (.consExtend _), _ => sptLookup memCopyLocation sizes
  | .blockOp (.fromList _), _ => Option.map₂ max (sptLookup fromListLocation sizes) (sptLookup fromList1Location sizes)
  | .blockOp .listAppend, _ =>
      Option.map₂ max (sptLookup appendLocation sizes)
        (Option.map₂ max (sptLookup appendLenLoopLocation sizes) (sptLookup appendMainLoopLocation sizes))
  | .intOp .div, [.number a, .number b] =>
      if smallNum limits.arch64Bit a ∧ 0 ≤ a ∧ smallNum limits.arch64Bit b ∧ 0 ≤ b ∧
         smallNum limits.arch64Bit (holIntDiv a b) then
        Option.map₂ max (sptLookup longDivLocation sizes) (sptLookup longDiv1Location sizes)
      else Option.map₂ max (sptLookup divLocation sizes) (WordDepth.maxDepth sizes anyArithCallTree)
  | .intOp .mod, [.number a, .number b] =>
      if smallNum limits.arch64Bit a ∧ 0 ≤ a ∧ smallNum limits.arch64Bit b ∧ 0 ≤ b ∧
         smallNum limits.arch64Bit (holIntMod a b) then
        Option.map₂ max (sptLookup longDivLocation sizes) (sptLookup longDiv1Location sizes)
      else Option.map₂ max (sptLookup modLocation sizes) (WordDepth.maxDepth sizes anyArithCallTree)
  | .intOp .mult, [.number a, .number b] =>
      if smallNum limits.arch64Bit a ∧ 0 ≤ a ∧ smallNum limits.arch64Bit b ∧ 0 ≤ b ∧
         smallNum limits.arch64Bit (a * b) then some 0
      else Option.map₂ max (sptLookup mulLocation sizes) (WordDepth.maxDepth sizes anyArithCallTree)
  | .blockOp .equal, [a, b] => eqCodeStackMax (min (valueDepth a + 1) (valueDepth b + 1)) sizes
  | .intOp .sub, [.number a, .number b] =>
      if smallNum limits.arch64Bit a ∧ smallNum limits.arch64Bit b ∧ smallNum limits.arch64Bit (a - b) then some 0
      else Option.map₂ max (sptLookup subLocation sizes) (WordDepth.maxDepth sizes anyArithCallTree)
  | .intOp .add, [.number a, .number b] =>
      if smallNum limits.arch64Bit a ∧ smallNum limits.arch64Bit b ∧ smallNum limits.arch64Bit (a + b) then some 0
      else Option.map₂ max (sptLookup addLocation sizes) (WordDepth.maxDepth sizes anyArithCallTree)
  | .intOp .lessEq, _ | .intOp .less, _ =>
      Option.map₂ max (sptLookup compareLocation sizes) (sptLookup compare1Location sizes)
  | op, values => if allowedOp op values.length then some 0 else none

/-- Account for the operation's extra stack space and update peak usage. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "do_stack_def"]
noncomputable def doStack {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state : State C F) : State C F :=
  let newStack := Option.map₂ (· + ·) (stackConsumed state.stackFrameSizes state.limits op values)
    (Option.map₂ (· + ·) (sizeOfStack state.stack) state.localsSize)
  let safe := (newStack.map (fun n => decide (state.limits.stackLimit > n))).getD false
  { state with safeForSpace := state.safeForSpace && safe, stackMax := Option.map₂ max state.stackMax newStack }

/-- Stack accounting preserves the evaluation clock. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "do_stack_clock"]
theorem doStack_clock {C F : Type} (op : ClosLang.Op) (values : List Value) (state : State C F) :
    (doStack op values state).clock = state.clock := rfl

end Flapjack.Compiler.Backend.DataSem
