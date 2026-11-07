import Flapjack.RiscV.PipelineDiagnostics

/-!
# CakeML RISC-V calling-convention parity

Regression coverage for the multi-function argument/return ABI (GitHub issue
#1024, bead `flapjack-pxn.8.5.10.1.1`).

Oracle evidence: the original compiler emits

```
fun 1 g(1 a, 1 b) { return a + b; }        -> add a0, a1, a0; ret
fun 1 h(1 a,1 b,1 c,1 d) { ... }           -> add a1,a1,a0; add a0,a3,a2; ...
```

so value argument `j` arrives in hardware register `riscv_names (j+1)`
(`a0..a3` = `10,11,12,13`) and the incoming link register is hardware `1`
(`riscv_names 0`).  The original allocator's `arg_count` therefore counts the
link slot as well, and its ABI word names are `[0, 2, 4, ..., 2n]` for `n`
value parameters.  Both facts are pinned here against the ported
`riscvRegisterName` map (`scripts/hol-probes/riscv_names_probe.out`).

The `callee_abi` fixture now reaches the same Cake ABI registers and exact
return bytes through the production pipeline.  The guards below retain the
source-level calling-convention facts that made that parity repair observable.
-/

namespace Flapjack.Test.RiscVAbiParity

open Flapjack Flapjack.RiscV

/-- Hardware argument registers of the original compiler for `j = 0..3`,
read from the emitted bodies of `fun 1 g(1 a, 1 b)` and
`fun 1 h(1 a, 1 b, 1 c, 1 d)`. -/
def cakeAbiArgumentRegisters : List Nat := [10, 11, 12, 13]

/-- The ported `riscv_names` map puts value argument `j` in the same hardware
register the original compiler uses. -/
def abiArgumentRegistersMatch : Bool :=
  (List.range 4).all (fun j => riscvRegisterName (j + 1) == cakeAbiArgumentRegisters[j]!)

/-- The incoming link register is hardware `1` (`riscv_names 0`). -/
def abiLinkRegisterMatches : Bool :=
  riscvRegisterName 0 == 1

/-! The same dependency order for the `WordLocation` scheduler, which drives
    the call argument/return and FFI moves.  For `{r3 <- r1, r1 <- r2}` the
    ready move `r1 <- r2` is emitted first and the postponed `r3 <- r1` last, so
    `r3` keeps the original `r1` instead of the new `r2`. -/
#guard abiArgumentRegistersMatch
#guard abiLinkRegisterMatches
/-! ### Cake ABI argument overflow

    The original `format_var`/`wMoveSingle` materializes arguments past the
    register window at the top of the frame, and sizes the frame with
    `stack_var_count = MAX ((max_var DIV 2 + 1) - k) stack_arg_count`
    (`word_to_stackScript.sml:586-592`), so the frame always has room for the
    stack-passed arguments.  Without that room Flapjack's physical argument
    destinations collide and the parallel move refuses to lower: the guest
    `generic_create` calls a 17-argument function and reported
    `wordToStackFailure 544 []` with `abiRegisterCount = 12`, i.e. five
    stack-passed arguments needing `17 - 12 - 1 = 4` frame slots. -/

def overflowArguments : List Nat :=
  [2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34]

def runChecks : IO Bool := do
  let checks := [
    ("the Cake ABI argument registers match riscv_names", abiArgumentRegistersMatch),
    ("the Cake ABI link register is hardware one", abiLinkRegisterMatches)]
  let mut ok := true
  for (label, passed) in checks do
    if passed then
      IO.println s!"PASS {label}"
    else
      IO.println s!"FAIL {label}"
      ok := false
  return ok

end Flapjack.Test.RiscVAbiParity
