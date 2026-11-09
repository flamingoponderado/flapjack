module

public import Flapjack.RiscV.WordToStack

@[expose] public section

/-!
# CakeML software LongDiv code-table shape

This is the source-shaped WordLang helper selected by CakeML's
`LongDiv_code_def` when `has_longdiv = false`.  It is deliberately kept as a
code-table value: the RISC-V instruction selector must continue to reject a
direct Word `LongDiv`, as the original `riscv_targetScript.sml` does.

Reference: `cakeml/compiler/backend/data_to_wordScript.sml:829-867`.
-/

namespace Flapjack.RiscV

def cakeLongDiv1Location : Nat := 22

def cakeLongDivLocation : Nat := 23

/- These helpers retain the static guards emitted by CakeML's HOL code table.
   They are evaluated at the target word width, so the resulting WordExp is
   the same guarded expression after specialization rather than an
   unconditional shift that is invalid at width zero or one. -/

def cakeLongDiv1Mask (width : Nat) : Nat :=
  let dimword := 2 ^ width
  if 1 % dimword = 0 then 0 else (dimword - 1) % dimword

/-! The code-table entries are functions.  CakeML's word-to-stack pass first
    reseats their even-numbered ABI arguments in the locations assigned to
    the helper's formal variables. -/
def cakeWordStackHelperRegister : Nat → Nat
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | 4 => 7
  | 6 => 9
  | 8 => 11
  | 10 => 13
  | 11 => 15
  | 12 => 17
  | 14 => 19
  | 16 => 21
  | _ => 23

/-! Adapt the source helper's Loc convention to the normalized StackLang
    LongDiv convention: the caller supplies high and low in x3 and x0, the
    divisor in x6, and observes quotient x0 and remainder x3.  Cake's
    `LongDiv_code` leaves the quotient in adjusted word register 10 and the
    remainder in `Temp 28`; copy those helper carriers into the normalized
    result registers in the return continuation. -/

example : cakeLongDiv1Mask 0 = 0 := by
  decide

example : cakeLongDiv1Mask 8 = 255 := by
  decide

end Flapjack.RiscV
