import Flapjack.Word

/-!
# StackLang

The StackLang layer is the first stack-based intermediate representation in
CakeML's backend. It is deliberately kept separate from the RISC-V model:
StackLang still has structured control flow and an explicit handler stack, while
the later stack-to-lab pass is responsible for flattening these operations.

This file ports the call, exception, and FFI carriers from
`cakeml/compiler/backend/stackLangScript.sml` and the corresponding boundary
equations from `word_to_stackScript.sml`. Register allocation and the complete
word-to-stack compiler remain subsequent stages.
-/

namespace Flapjack

/-! Register relabeling is kept at the StackLang boundary so a source-shaped
    Cake program can be converted to the port's hardware-numbered Lab input
    without changing stores, offsets, labels, or constants. -/
def stackMapWordRegImm (map : Nat → Nat) : WordRegImm α → WordRegImm α
  | .imm value => .imm value
  | .reg register => .reg (map register)

/- Cake's wReg1/wReg2 keep equal allocator colors in distinct operand
   carriers for a store.  Preserve that distinction only at final register
   mapping; StackLang evaluation still sees the shared value. -/
def stackMapStoreAddress (map : Nat → Nat) (source address : Nat) : Nat :=
  map (if source = address then address + 1 else address)

def stackMapMemoryAddress (map : Nat → Nat) (operator : WordMemOp)
    (source address : Nat) : Nat :=
  match operator with
  | .store | .store8 | .store16 | .store32 =>
      stackMapStoreAddress map source address
  | .load | .load8 | .load16 | .load32 => map address

/-! The callee-return part of CakeML's Word-to-Stack calling convention.

    `num_stack_ret` counts values that were returned in the caller's stack
    frame rather than in the first `k` ABI result registers.  `copy_ret_aux`
    copies the stack-resident suffix from the old frame into the current one,
    starting at its highest slot just as CakeML's recursive definition does.
    Keeping these as StackLang carriers makes the convention available before
    the complete allocator supplies concrete frame sizes. -/
def stackNumReturnSlots (k : Nat) (values : List Nat) : Nat :=
  values.length + 1 - k

/-! The Word-to-Stack call carriers pass the already-sliced stack-resident
    return suffix rather than Cake's full `vs` list. Its length is therefore
    exactly `num_stack_ret`; keep the same descending copy and handler-frame
    offset without manufacturing an artificial ABI prefix. -/

/- The HOL development reserves the final stub location for the raise entry.
   The concrete target table will fill this in when stack-to-lab is ported. -/

/- The first three section labels are reserved by the executable Flapjack
   runtime-linked entry point: raise, StoreConsts, and the collector. -/
def stackStoreConstsStubLocation : Nat := 1

def stackGcStubLocation : Nat := 2

def stackFunctionFirstLabel : Nat := 3

end Flapjack
