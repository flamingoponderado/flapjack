import Flapjack.Pancake.WordConvs.NotCreated
import Flapjack.Test.Runtime

/-!
# wordConvs `not_created_subprogs` / `no_*_subprogs` Lean regression

Kernel-checked cases matching the 15 rows of
`scripts/hol-probes/word_convs_not_created_probe.out`.
-/

namespace Flapjack.Test.WordLangNotCreatedParity

open Flapjack

private abbrev W := BitVec 8

private def cuts : WordLangCutsetsHOL := (.ln, .ln)

private def skipP : WordLangProgHOL W := .skip

private def allocEmpty : WordLangProgHOL W := .alloc 0 cuts

private def allocOther : WordLangProgHOL W := .alloc 1 cuts

private def seqAlloc : WordLangProgHOL W := .seq .skip (.alloc 0 cuts)

private def mtSkip : WordLangProgHOL W := .mustTerminate .skip

private def installEmpty : WordLangProgHOL W := .install 0 0 0 0 cuts

private def shareArb : WordLangProgHOL W := .shareInst wordLangArbMemOp 0 (.var 0)

private def shareLoad : WordLangProgHOL W := .shareInst .load 0 (.var 0)

private def seqShare : WordLangProgHOL W := .seq .skip shareArb

private def callNone : WordLangProgHOL W := .call none none [] none

private def callHandlerMt : WordLangProgHOL W :=
  .call none none [] (some (0, .mustTerminate .skip, 0, 0))

-- nac_skip=T
example : noAllocSubprogsHOL skipP = true := by decide
-- nac_alloc_empty=F
example : noAllocSubprogsHOL allocEmpty = false := by decide
-- nac_alloc_other=F
example : noAllocSubprogsHOL allocOther = false := by decide
-- nac_seq_alloc=F
example : noAllocSubprogsHOL seqAlloc = false := by decide
-- nac_mt_skip=T
example : noAllocSubprogsHOL mtSkip = true := by decide
-- nins_install_empty=F
example : noInstallSubprogsHOL installEmpty = false := by decide
-- nmt_mt_skip=F
example : noMtSubprogsHOL mtSkip = false := by decide
-- nsi_skip=T
example : noShareInstSubprogsHOL skipP = true := by decide
-- nsi_share_arb=F
example : noShareInstSubprogsHOL shareArb = false := by decide
-- nsi_share_load=F
example : noShareInstSubprogsHOL shareLoad = false := by decide
-- nsi_seq_share=F
example : noShareInstSubprogsHOL seqShare = false := by decide
-- nsi_call_none=T
example : noShareInstSubprogsHOL callNone = true := by decide
-- nsi_call_handler_mt=T
example : noShareInstSubprogsHOL callHandlerMt = true := by decide
-- nmt_call_handler_mt=F
example : noMtSubprogsHOL callHandlerMt = false := by decide
-- nac_install_empty=T
example : noAllocSubprogsHOL installEmpty = true := by decide

-- The exact general checker at HOL's predicates and `ARB` gives the same rows.
-- nac_alloc_empty=F
example : notCreatedSubprogsHOL
    (fun q => by classical exact decide (q ≠ .alloc 0 (.ln, .ln))) allocEmpty = false := by
  rw [← noAllocSubprogsHOL_eq_notCreated]; decide
-- nins_install_empty=F
example : notCreatedSubprogsHOL
    (fun q => by classical exact decide (q ≠ .install 0 0 0 0 (.ln, .ln))) installEmpty = false := by
  rw [← noInstallSubprogsHOL_eq_notCreated]; decide
-- nmt_call_handler_mt=F
example : notCreatedSubprogsHOL
    (fun q => by classical exact decide (q ≠ .mustTerminate .skip)) callHandlerMt = false := by
  rw [← noMtSubprogsHOL_eq_notCreated]; decide
-- nsi_call_handler_mt=T
example : notCreatedSubprogsHOL
    (fun q => by classical exact decide (q ≠ .shareInst holArbMemOp 0 (.var 0))) callHandlerMt =
      true := by
  rw [← noShareInstSubprogsHOL_eq_notCreated]; decide

private def oracleChecks : Bool :=
  [
    noAllocSubprogsHOL skipP == true,
    noAllocSubprogsHOL allocEmpty == false,
    noAllocSubprogsHOL allocOther == false,
    noAllocSubprogsHOL seqAlloc == false,
    noAllocSubprogsHOL mtSkip == true,
    noInstallSubprogsHOL installEmpty == false,
    noMtSubprogsHOL mtSkip == false,
    noShareInstSubprogsHOL skipP == true,
    noShareInstSubprogsHOL shareArb == false,
    noShareInstSubprogsHOL shareLoad == false,
    noShareInstSubprogsHOL seqShare == false,
    noShareInstSubprogsHOL callNone == true,
    noShareInstSubprogsHOL callHandlerMt == true,
    noMtSubprogsHOL callHandlerMt == false,
    noAllocSubprogsHOL installEmpty == true
  ].all id

#guard oracleChecks

def runChecks : IO Bool := do
  if oracleChecks then
    IO.println "PASS exact Boolean wordConvs specializations match all 15 original HOL rows"
    pure true
  else
    IO.println "FAIL exact Boolean wordConvs specializations disagree with original HOL"
    pure false

end Flapjack.Test.WordLangNotCreatedParity
