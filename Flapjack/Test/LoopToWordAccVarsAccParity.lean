import Flapjack.Pancake.Proofs.LoopToWord.AccVarsAcc

/-!
# Regression for the exact Loop-to-Word `acc_vars_acc'` port

Replays the direct original-HOL EVAL rows from
`scripts/hol-probes/loop_to_word_acc_vars_acc_prime_probe.out` over the exact
`HolLoopProg`/`NumSet` carriers: for programs exercising Assign, Seq, If, Loop
and Call, membership in `domain (acc_vars p (acc_vars q LN))` agrees with
membership in `domain (acc_vars p LN) ∪ domain (acc_vars q LN)`.
-/

namespace Flapjack.Test.LoopToWordAccVarsAccParity

open Flapjack
open Flapjack.LoopToWord

private def pAssign : HolLoopProg 64 := .assign 10 (.const 0)
private def qAssign : HolLoopProg 64 := .assign 1 (.const 0)
private def pSeq : HolLoopProg 64 :=
  .seq (.assign 10 (.const 0)) (.assign 11 (.const 0))
private def pIf : HolLoopProg 64 :=
  .ite .equal 3 (.reg 4) (.assign 10 (.const 0)) (.assign 11 (.const 0)) .ln
private def pLoop : HolLoopProg 64 := .loop .ln (.assign 10 (.const 0)) .ln
private def qLoop : HolLoopProg 64 := .loop .ln (.assign 2 (.const 0)) .ln
private def pCall : HolLoopProg 64 := .call (some ([10, 11], .ln)) (some 3) [4, 5] none

/-- Left-hand-side membership as a boolean, matching the probe's first entry. -/
private def mem (p q : HolLoopProg 64) (k : Nat) : Bool :=
  (sptLookup k (accVarsHOL p (accVarsHOL q .ln))).isSome

/-- Right-hand-side membership as a boolean, matching the probe's second entry. -/
private def memR (p q : HolLoopProg 64) (k : Nat) : Bool :=
  (sptLookup k (accVarsHOL p .ln)).isSome ||
    (sptLookup k (accVarsHOL q .ln)).isSome

/-- The ported `acc_vars_acc'` instantiated at the concrete Assign programs. -/
example : sptMem 10 (accVarsHOL pAssign (accVarsHOL qAssign .ln)) ↔
    (sptMem 10 (accVarsHOL pAssign .ln) ∨ sptMem 10 (accVarsHOL qAssign .ln)) := by
  simpa [sptMem] using congrFun (accVarsAccPrimeHOL qAssign pAssign) 10

/-- The ported `acc_vars_acc'` instantiated at the concrete Seq programs. -/
example : sptMem 11 (accVarsHOL pSeq (accVarsHOL qAssign .ln)) ↔
    (sptMem 11 (accVarsHOL pSeq .ln) ∨ sptMem 11 (accVarsHOL qAssign .ln)) := by
  simpa [sptMem] using congrFun (accVarsAccPrimeHOL qAssign pSeq) 11

/-- The ported `acc_vars_acc'` instantiated at the concrete If programs. -/
example : sptMem 12 (accVarsHOL pIf (accVarsHOL qAssign .ln)) ↔
    (sptMem 12 (accVarsHOL pIf .ln) ∨ sptMem 12 (accVarsHOL qAssign .ln)) := by
  simpa [sptMem] using congrFun (accVarsAccPrimeHOL qAssign pIf) 12

/-- The ported `acc_vars_acc'` instantiated at the concrete Loop programs. -/
example : sptMem 2 (accVarsHOL pLoop (accVarsHOL qLoop .ln)) ↔
    (sptMem 2 (accVarsHOL pLoop .ln) ∨ sptMem 2 (accVarsHOL qLoop .ln)) := by
  simpa [sptMem] using congrFun (accVarsAccPrimeHOL qLoop pLoop) 2

/-- The ported `acc_vars_acc'` instantiated at the concrete Call program. -/
example : sptMem 10 (accVarsHOL pCall (accVarsHOL qAssign .ln)) ↔
    (sptMem 10 (accVarsHOL pCall .ln) ∨ sptMem 10 (accVarsHOL qAssign .ln)) := by
  simpa [sptMem] using congrFun (accVarsAccPrimeHOL qAssign pCall) 10

/-- Boolean replay of every probe row: the two memberships agree. -/
def accVarsAccProbeChecks : List Bool :=
  [ mem pAssign qAssign 10 == memR pAssign qAssign 10,
    mem pAssign qAssign 1 == memR pAssign qAssign 1,
    mem pAssign qAssign 99 == memR pAssign qAssign 99,
    mem pSeq qAssign 10 == memR pSeq qAssign 10,
    mem pSeq qAssign 11 == memR pSeq qAssign 11,
    mem pSeq qAssign 1 == memR pSeq qAssign 1,
    mem pIf qAssign 10 == memR pIf qAssign 10,
    mem pIf qAssign 11 == memR pIf qAssign 11,
    mem pIf qAssign 12 == memR pIf qAssign 12,
    mem pLoop qLoop 10 == memR pLoop qLoop 10,
    mem pLoop qLoop 2 == memR pLoop qLoop 2,
    mem pCall qAssign 10 == memR pCall qAssign 10,
    mem pCall qAssign 11 == memR pCall qAssign 11,
    mem pCall qAssign 1 == memR pCall qAssign 1,
    mem pAssign qAssign 10 == true,
    mem pAssign qAssign 99 == false,
    mem pIf qAssign 10 == true,
    mem pIf qAssign 12 == false ]

#guard accVarsAccProbeChecks.all id

def runChecks : IO Bool := do
  let passed := accVarsAccProbeChecks.all id
  if passed then
    IO.println "PASS Loop-to-Word acc_vars_acc' exact HOL EVAL rows"
  else
    IO.println "FAIL Loop-to-Word acc_vars_acc' exact HOL EVAL rows"
  pure passed

end Flapjack.Test.LoopToWordAccVarsAccParity
