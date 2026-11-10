module

public import Flapjack.RiscV.PipelineDiagnostics

-- Checks below run compiled code from these modules.
public meta import Flapjack.Compiler.Backend.Semantics.WordSem
public meta import Flapjack.RiscV.PipelineDiagnostics
@[expose] public section

/-!
# Cake register-renaming oracle for the source-facing ABI adapter

`scripts/hol-probes/riscv_names_probeScript.sml` evaluates the original
CakeML `riscv_names` map (`cakeml/compiler/backend/riscv/riscv_configScript.sml`)
directly in HOL.  The recorded answers are:

  0 -> 1, 1 -> 10, 2 -> 11, 3 -> 12, 4 -> 13,
  10 -> 27, 11 -> 28, 12 -> 29, 13 -> 30,
  27 -> 0, 28 -> 2, 29 -> 3, 30 -> 4,
  everything else unset (identity).

`Flapjack.RiscV.riscvRegisterName` is the port of that map, so the guards below
are checked against the original oracle rather than a transcription.
-/

open Flapjack Flapjack.RiscV

namespace Flapjack.Test.RiscVAbiAdapterParity

/-- Oracle answers from the HOL probe for `riscv_names`. -/
def oracleAnswers : List (Nat × Nat) :=
  [(0, 1), (1, 10), (2, 11), (3, 12), (4, 13), (10, 27), (11, 28), (12, 29),
    (13, 30), (27, 0), (28, 2), (29, 3), (30, 4)]

/-- The ported map agrees with every recorded HOL oracle value. -/
def mapMatchesOracle : Bool :=
  oracleAnswers.all (fun entry => riscvRegisterName entry.1 == entry.2)

#guard mapMatchesOracle

/-- Cake leaves the registers outside the recorded map unchanged. -/
def mapIdentityOutsideOracle : Bool :=
  ([5, 6, 7, 8, 9, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
      31]).all (fun register => riscvRegisterName register == register)

#guard mapIdentityOutsideOracle

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [("the ported register map matches the riscv_names HOL oracle",
        mapMatchesOracle),
      ("registers outside the oracle stay identity like Cake",
        mapIdentityOutsideOracle)]
  let mut ok := true
  for check in checks do
    if check.2 then
      IO.println s!"PASS {check.1}"
    else
      ok := false
      IO.println s!"FAIL {check.1}"
  return ok

end Flapjack.Test.RiscVAbiAdapterParity
