import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.If
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.Assign
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Basis.Pure.MlString

/-!
# Exact-carrier parity for the `If` case of `simp_prog_correct`

Kernel-checked replay of the direct HOL rows in
`scripts/hol-probes/crep_arith_if_probe.out` against the tagged exact
`simpProgCorrectIfCase` and the exact `CrepSemHOLState` carriers.

The probe fixes an 8-bit state whose `locals` bind `1` and `2`; the Lean rows
below are stated over an arbitrary exact state (the width-8 fixture is a
specialization) so they also witness the same-module finite-support carrier.
The success rows exercise both guard values through the tagged case theorem,
the leaf hypothesis being supplied by the tagged exact `simpProgCorrectAssignCase`
as a branch instance of the HOL `evaluate_ind` `If` induction hypothesis.
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

/-- Probe rows `evaluate_if_true_state`/`if_mapc_true`/`if_mapc_commute`: the
    tagged exact `If` case turns a successful source evaluation of the selected
    branch into the same target evaluation under `crepSimpMapcsHOL`.  The
    branch hypothesis is the HOL `evaluate_ind` `If` IH, discharged here by the
    tagged exact `simpProgCorrectAssignCase`. -/
example {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (condition : CrepExpHOL width)
    (name : Nat) (source : CrepExpHOL width) (elseBranch : CrepProgHOL width)
    (w : BitVec width)
    (hcond : evalCrepSemHOLExp state condition = some (.word w)) (hw : w ≠ 0)
    (result : Option (CrepResultHOLExact width))
    (finalState : CrepSemHOLState width σ)
    (heval : evalCrepSemHOLProgExact state
        (.ite condition (.assign name source) elseBranch) = (result, finalState))
    (hresult : result ≠ some .error) :
    evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
        (crepSimpProgHOL (.ite condition (.assign name source) elseBranch)) =
      (result, crepSimpMapcsHOL finalState) := by
  refine simpProgCorrectIfCase state condition (.assign name source) elseBranch
    ?_ result finalState heval hresult
  intro value w' hcond' heq result' finalState' heval' hresult'
  subst heq
  have hwEq : w' = w := by
    have hsame : some (HolWordLab.word w') = some (HolWordLab.word w) :=
      hcond'.symm.trans hcond
    simpa using hsame
  subst hwEq
  simp only [if_pos hw] at heval' ⊢
  exact simpProgCorrectAssignCase state name source result' finalState' heval' hresult'

end Flapjack.Test.CrepArithIfParity
