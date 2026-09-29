import Flapjack.Pancake.CrepArith
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Basis.Pure.MlString

/-!
# Exact-carrier parity for the `If` case of `simp_prog_correct`

Kernel-checked replay of the direct HOL rows in
`scripts/hol-probes/crep_arith_if_probe.out` against the exact `CrepSemHOLState`
carriers.  This module is deliberately independent of the tagged exact
`simpProgCorrectIfCase`: it exercises only the rows the direct HOL probe
produces, so it pins `simp_prog`, the condition-word branch selection, and the
absent-condition error branch without restating the case theorem.

The probe fixes an 8-bit state whose `locals` bind `1` and `2`; the Lean rows
below are stated over an arbitrary exact state (the width-8 fixture is a
specialization) so they also witness the same-module finite-support carrier.
The `simp_prog_if` row is replayed on `crepSimpProgHOL`; the `evaluate_if_*`
rows on `evalCrepSemHOLProgExact`.  The two code-only `mapc` rows
(`if_mapc_true`, `if_mapc_commute`) are recorded in the probe output and are
covered by the tagged exact `simpProgCorrectIfCase` proof; they are not
duplicated here to keep this replay free of that case theorem.
-/

namespace Flapjack.Test.CrepArithIfParity

open Flapjack
open Flapjack.Basis.Pure.MlString
open Classical

/-- Probe row `simp_prog_if` (`crep_arithScript.sml:90`): `simp_prog`
    simplifies the condition and both branches. -/
example {width : Nat} [NeZero width] (condition : CrepExpHOL width)
    (thenBranch elseBranch : CrepProgHOL width) :
    crepSimpProgHOL (.ite condition thenBranch elseBranch : CrepProgHOL width) =
      (.ite (crepSimpExpHOL condition) (crepSimpProgHOL thenBranch)
        (crepSimpProgHOL elseBranch) : CrepProgHOL width) := by
  simp only [crepSimpProgHOL]

/-- Probe rows `evaluate_if_true`/`evaluate_if_true_state` and
    `evaluate_if_false`/`evaluate_if_false_state`: a word condition selects
    `thenBranch` when nonzero and `elseBranch` when zero, at the input state. -/
example {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (condition : CrepExpHOL width)
    (thenBranch elseBranch : CrepProgHOL width) (w : BitVec width)
    (hcond : evalCrepSemHOLExp state condition = some (.word w)) (hw : w ≠ 0) :
    evalCrepSemHOLProgExact state (.ite condition thenBranch elseBranch) =
      evalCrepSemHOLProgExact state thenBranch := by
  simp only [evalCrepSemHOLProgExact_ite_holShape, hcond, if_pos hw]

example {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (condition : CrepExpHOL width)
    (thenBranch elseBranch : CrepProgHOL width) (w : BitVec width)
    (hcond : evalCrepSemHOLExp state condition = some (.word w)) (hw : w = 0) :
    evalCrepSemHOLProgExact state (.ite condition thenBranch elseBranch) =
      evalCrepSemHOLProgExact state elseBranch := by
  subst hw
  simp only [evalCrepSemHOLProgExact_ite_holShape, hcond]
  simp only [if_neg (show ¬((0 : BitVec width) ≠ 0) by simp)]

/-- Probe row `evaluate_if_error` (`crepSemScript.sml:307-311`): a condition
    that does not evaluate to a word errors with the input state. -/
example {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (condition : CrepExpHOL width)
    (thenBranch elseBranch : CrepProgHOL width)
    (hcond : evalCrepSemHOLExp state condition = none) :
    evalCrepSemHOLProgExact state (.ite condition thenBranch elseBranch) =
      (some .error, state) := by
  simp only [evalCrepSemHOLProgExact_ite_holShape, hcond]

/-- Build-time checks for the `If` parity rows. -/
def runChecks : IO Bool := do
  IO.println "PASS crep_arith simp_prog_correct If case replays the direct crep_arith_if HOL rows"
  return true

end Flapjack.Test.CrepArithIfParity
