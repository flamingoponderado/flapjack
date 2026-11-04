import Flapjack.Compiler.Backend.StackLang.WordPayloads
import Flapjack.RiscV.Lab

/-! Flapjack-only correspondence to the instruction conversions already used
by the executed Word-to-Stack and Lab routes. These declarations have no HOL
original and do not assert full program/transition correspondence. -/
namespace Flapjack.Compiler.Backend.StackLang.WordPayloads
open Flapjack Flapjack.RiscV

theorem mapRegImm_ofNat {width : Nat} [NeZero width] (operand : WordRegImm Nat) :
    mapRegImm (BitVec.ofNat width) operand = labWordRegImmToWord (width := width) operand := by
  cases operand <;> rfl

end Flapjack.Compiler.Backend.StackLang.WordPayloads
