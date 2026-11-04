import Flapjack.RiscV.PipelineDiagnostics

namespace Flapjack

open RiscV

/-! Direct Cake oracle guard for the six-instruction RISC-V carry expansion.
    This count is consumed by the Lab linker when computing later labels. -/
def diagnosticCompiledMain : CompiledFunction Nat :=
  { name := "main", params := [], body := .skip, returnShape := .one }

private def routedSkipFunction : CompiledFunction (BitVec 64) :=
  { name := "main", params := [], body := .skip, returnShape := .one }

private def nonByteRoutedFunction : CompiledFunction (BitVec 64) :=
  { name := "λ", params := [],
    body := .extCall "λ" 0 0 0 0,
    returnShape := .one }

private def routedCallCaller : CompiledFunction (BitVec 64) :=
  { name := "caller", params := [], body := .call none "callee" [],
    returnShape := .one }

private def routedCallCallee : CompiledFunction (BitVec 64) :=
  { name := "callee", params := [], body := .skip, returnShape := .one }

/-! Pin the complete width-8 helper shape from
    `scripts/hol-probes/longdiv_code_probe.out`, not only its calls and
    AddCarry leaves.  This is the Cake `LongDiv1_code` software path selected
    when `has_longdiv = F`; the direct RISC-V LongDiv selector remains
    intentionally rejecting the hardware instruction above. -/

def checkedPipelineDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "main", inline := false, exported := true, params := [],
      body := .return (.const (BitVec.ofNat 64 7)), returnShape := .one }]

/-! Original Pancake also accepts a computed address for an ordinary local
    store.  Keep this source-facing regression separate from the structured
    address case above: the address is a nested expression and the value is a
    scalar local. -/
def nestedLocalStoreSource : String :=
  "fun 1 main() { var 1 x = 7; st 1000 + 12, x; return x; }"

/-! GH #1157 (`Normalize or explain mode-specific section IDs in lowering
    errors`): the section id recorded in a lowering error is a crepe-local
    label, not a stable function identity.  `--hex` numbers crepe sections
    from 1 while the default runtime-image mode numbers them from
    `stackFunctionFirstLabel`, so the equal failing function shows up as
    different section ids.  These guards pin the presentation-layer regression
    without changing the internal Cake-compatible labels. -/
def diagnosticCompiledFunctions : List (CompiledFunction Nat) :=
  [ { name := "helper", params := [], body := .skip, returnShape := .one },
    diagnosticCompiledMain ]

#guard stackFunctionFirstLabel = 3

end Flapjack
