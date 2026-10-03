import Flapjack.RiscV.L3.Defs.Decode

/-! Complete original step raw-instruction selector, over both fixed-width
constructors. No successful-decode or accepted-opcode premise is added. -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "DecodeAny_def"]
def DecodeAny (f : rawInstType) : instruction :=
  match f with
  | .Half h => DecodeRVC h
  | .Word w => Decode w

/-- Flapjack generic check of the Half equation; no distinct named HOL theorem. -/
theorem DecodeAny_half (h : BitVec 16) :
    DecodeAny (.Half h) = DecodeRVC h := rfl

/-- Flapjack generic check of the Word equation; no distinct named HOL theorem. -/
theorem DecodeAny_word (w : BitVec 32) :
    DecodeAny (.Word w) = Decode w := rfl

end Flapjack.RiscV.L3.Step
