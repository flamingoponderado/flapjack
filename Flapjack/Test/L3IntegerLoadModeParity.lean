import Flapjack.RiscV.L3.Defs.IntegerLoadMode
namespace Flapjack.Test.L3IntegerLoadModeParity
open Flapjack.RiscV.L3

private def fixture (base : riscv_state) (n : Nat) : riscv_state :=
  { base with procID := BitVec.ofNat 8 255, totalCore := 1, exception := .NoException, c_MCSR := (fun id => { base.c_MCSR id with mcpuid := { (base.c_MCSR id).mcpuid with ArchBase := BitVec.ofNat 2 n } }) }

/-- Flapjack regression infrastructure, without a standalone HOL original.
All original selectors and arbitrary unrelated state are retained. The invalid
selector's architecture/Boolean remains canonical unspecified, not a default. -/
private def unknownMessage : List (BitVec 8) :=
  [85,110,107,110,111,119,110,32,97,114,99,104,105,116,101,99,116,117,114,101,58,32,49].map (BitVec.ofNat 8)

-- Original l3_integer_load_mode_probe.out: selector_0.
example (base : riscv_state) :
    (curArch () (fixture base 0), in32BitMode () (fixture base 0)) =
      ((Architecture.RV32I, fixture base 0), ((Architecture.RV32I == Architecture.RV32I), fixture base 0)) := by
  simp [fixture, curArch, in32BitMode, architecture, MCSR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]

-- Original l3_integer_load_mode_probe.out: selector_1.
example (base : riscv_state) :
    (curArch () (fixture base 1), in32BitMode () (fixture base 1)) =
      ((Flapjack.holArb Architecture, { fixture base 1 with exception := .UNDEFINED unknownMessage }), ((Flapjack.holArb Architecture == Architecture.RV32I), { fixture base 1 with exception := .UNDEFINED unknownMessage })) := by
  simp [fixture, curArch, in32BitMode, architecture, MCSR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]

-- Original l3_integer_load_mode_probe.out: selector_2.
example (base : riscv_state) :
    (curArch () (fixture base 2), in32BitMode () (fixture base 2)) =
      ((Architecture.RV64I, fixture base 2), ((Architecture.RV64I == Architecture.RV32I), fixture base 2)) := by
  simp [fixture, curArch, in32BitMode, architecture, MCSR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]

-- Original l3_integer_load_mode_probe.out: selector_3.
example (base : riscv_state) :
    (curArch () (fixture base 3), in32BitMode () (fixture base 3)) =
      ((Architecture.RV128I, fixture base 3), ((Architecture.RV128I == Architecture.RV32I), fixture base 3)) := by
  simp [fixture, curArch, in32BitMode, architecture, MCSR, raiseException_eq, unknownMessage, Flapjack.holNumToDecString, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]


/-- Full arbitrary-state invalid route: retains a prior exception and leaves the
unspecified architecture symbolic. Flapjack regression, no separate HOL port. -/
theorem invalidSelector (s : riscv_state) :
    architecture (BitVec.ofNat 2 1) s =
      (Flapjack.holArb Architecture,
        if s.exception == exception.NoException then
          { s with exception := exception.UNDEFINED unknownMessage } else s) := by
  simp [architecture, raiseException_eq, unknownMessage, Flapjack.holNumToDecString,
    Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]

end Flapjack.Test.L3IntegerLoadModeParity
