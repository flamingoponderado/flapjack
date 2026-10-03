import Flapjack.Compiler.Backend.StackLang.ProductionCodec
import Flapjack.Compiler.Backend.WordToStack.NativeMoves

/-! Kernel tests of the production StackLang carrier codec. No evaluated
compiler or HOL semantic parity is claimed by these structural examples. -/
namespace Flapjack.Test.StackProductionCodecParity
open Flapjack Compiler.Backend.StackLang Compiler.Backend.StackCarrier

example : storeFromProduction (.temp 31) = some (.temp (BitVec.ofNat 5 31)) := rfl
example : storeFromProduction (.temp 32) = none := rfl

example : progToProduction (.stackStore 17 9 : ProgW (BitVec 64)) =
    some (.stackStore 17 9) := rfl
example : progFromProduction (.stackLoad 9 17 : StackProg (BitVec 64)) =
    some (.stackLoad 9 17) := rfl

/- HOL stackSemScript.sml:973/988 uses the first operand as the register
and the second as the stack-space-relative offset. Unequal operands are
intentional: symmetric roundtrip alone did not detect the previous swap. -/
example : holProgToProduction (.stackLoad 23 2 : HolProg 64) =
    some (.stackLoad 23 2) := by
  simp [holProgToProduction, Compiler.Backend.holProgToProgW, Prog.map, progToProduction]
example : holProgToProduction (.stackStore 22 1 : HolProg 64) =
    some (.stackStore 22 1) := by
  simp [holProgToProduction, Compiler.Backend.holProgToProgW, Prog.map, progToProduction]
example : productionToHolProg (.stackLoad 23 2 : StackProg (BitVec 64)) =
    some (.stackLoad 23 2) := by
  simp [productionToHolProg, Compiler.Backend.progWToHolProg, Prog.map, progFromProduction]
example : productionToHolProg (.stackStore 22 1 : StackProg (BitVec 64)) =
    some (.stackStore 22 1) := by
  simp [productionToHolProg, Compiler.Backend.progWToHolProg, Prog.map, progFromProduction]

/- Original HOL capture sr_spill_cycle in
scripts/hol-probes/word_to_stack_scheduler_route_probe.out. This independently
checks the native compiler image through the production codec, rather than
roundtripping a possibly incorrect codec image. -/
example : holProgToProduction
    (Compiler.Backend.WordToStack.Native.wMoveNative (width := 64)
      [(44, 46), (46, 44)] (22, 3, 2)) =
    some (.seq (.stackLoad 23 1)
      (.seq (.seq (.stackLoad 22 2) (.stackStore 22 1))
        (.stackStore 23 2))) := by cbv

example : progFromProduction (.const 9 255 : StackProg (BitVec 64)) = none := rfl
example : progFromProduction (.arith .add 9 10 11 : StackProg (BitVec 64)) = none := rfl
example : progFromProduction (.shift .lsl 9 10 11 : StackProg (BitVec 64)) = none := rfl
example : progFromProduction
    (.inst (.arith (.addCarry 1 2 3 4 5)) : StackProg (BitVec 64)) = none := rfl

example : progToProduction
    (.inst (.mem .store 9 (.addr 10 0)) : ProgW (BitVec 64)) =
    some (.inst (.mem .store 9 10)) := rfl
example : progToProduction
    (.inst (.mem .load 9 (.addr 10 7)) : ProgW (BitVec 64)) =
    some (.inst (.memOffset .load 9 10 7)) := rfl
example : progToProduction
    (.shMemOp .store 9 (.addr 10 0) : ProgW (BitVec 64)) =
    some (.shMemOffset .store 9 10 0) := rfl

example : progToProduction
    (.ffi "λ" 1 2 3 4 5 : ProgW (BitVec 64)) =
    some (.ffi "λ" 1 2 3 4 5) := rfl

example : progToProduction
    (.call (some (.seq .skip (.inst (.const 9 255)), 7, 8, 9)) (.inr 10)
      (some (.loop (.stackLoad 17 11), 12, 13)) : ProgW (BitVec 64)) =
    some (.call (some (.seq .skip (.inst (.const 9 255)), 7, 8, 9)) (.register 10)
      (some (.loop (.stackLoad 17 11), 12, 13))) := rfl

example {width : Nat} [NeZero width] (p : HolProg width)
    (s : StackProg (BitVec width)) (h : holProgToProduction p = some s) :
    productionToHolProg s = some p :=
  productionToHolProg_of_holProgToProduction p s h

def runChecks : IO Bool := do
  IO.println "PASS production StackLang structural codec (accepted canonical image; route remains open)"
  return true
end Flapjack.Test.StackProductionCodecParity
