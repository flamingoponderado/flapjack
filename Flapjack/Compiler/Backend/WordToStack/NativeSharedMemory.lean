import Flapjack.Compiler.Backend.WordToStack.NativeInstructions

/-! Native shared-memory instruction lowering for the literal compiler.
This implements the source compiler helper, not memory evaluation or a production
alias adjustment. Actual native compiler assembly and execution remain open.
-/
namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackLang
open WordToStackRegFormat (wReg1 wReg2)

/-- Literal eight source shared-memory cases on the native same-width carrier.
Loads stage the address then spill the destination; stores stage address and
source in that order. Offsets and all four memory sizes are preserved. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def wShareInstNative {width : Nat} [NeZero width] (op : HolMemop) (v : Nat)
    (address : HolAddr width) (kf : Nat × Nat × Nat) : HolProg width :=
  match op, address with
  | .load, .addr ad offset =>
      let l := wReg1 ad kf
      wStackLoadNative l.1
        (wRegWrite1Native (fun r => .shMemOp .load r (.addr l.2 offset)) v kf)
  | .load8, .addr ad offset =>
      let l := wReg1 ad kf
      wStackLoadNative l.1
        (wRegWrite1Native (fun r => .shMemOp .load8 r (.addr l.2 offset)) v kf)
  | .load16, .addr ad offset =>
      let l := wReg1 ad kf
      wStackLoadNative l.1
        (wRegWrite1Native (fun r => .shMemOp .load16 r (.addr l.2 offset)) v kf)
  | .load32, .addr ad offset =>
      let l := wReg1 ad kf
      wStackLoadNative l.1
        (wRegWrite1Native (fun r => .shMemOp .load32 r (.addr l.2 offset)) v kf)
  | .store, .addr ad offset =>
      let l1 := wReg1 ad kf
      let l2 := wReg2 v kf
      wStackLoadNative (l1.1 ++ l2.1)
        (.shMemOp .store l2.2 (.addr l1.2 offset))
  | .store8, .addr ad offset =>
      let l1 := wReg1 ad kf
      let l2 := wReg2 v kf
      wStackLoadNative (l1.1 ++ l2.1)
        (.shMemOp .store8 l2.2 (.addr l1.2 offset))
  | .store16, .addr ad offset =>
      let l1 := wReg1 ad kf
      let l2 := wReg2 v kf
      wStackLoadNative (l1.1 ++ l2.1)
        (.shMemOp .store16 l2.2 (.addr l1.2 offset))
  | .store32, .addr ad offset =>
      let l1 := wReg1 ad kf
      let l2 := wReg2 v kf
      wStackLoadNative (l1.1 ++ l2.1)
        (.shMemOp .store32 l2.2 (.addr l1.2 offset))

/-- Flapjack-only universal payload representation relation. No source or target
memory-evaluation result is assumed; no HOL original exists for this codec theorem. -/
theorem toGeneric_wShareInstNative {width : Nat} [NeZero width]
    (op : HolMemop) (v : Nat) (address : HolAddr width) (kf : Nat × Nat × Nat) :
    toGeneric (wShareInstNative op v address kf) =
      WordToStackRegFormat.wShareInst op v address.toWordLangAddr kf := by
  cases address
  cases op <;> simp only [wShareInstNative, WordToStackRegFormat.wShareInst,
    HolAddr.toWordLangAddr, toGeneric_wStackLoad]
  all_goals
    try rw [toGeneric_wRegWrite1]
    simp [toGeneric, Prog.map, HolAddr.toWordLangAddr]

end Flapjack.Compiler.Backend.WordToStack.Native
