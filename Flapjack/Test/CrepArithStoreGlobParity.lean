import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrectStoreGlob
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Basis.Pure.MlString

/-!
# Exact-carrier parity for the `StoreGlob` case of `simp_prog_correct`

Kernel-checked replay of the direct HOL rows in
`scripts/hol-probes/crep_arith_store_glob_probe.out` against the tagged exact
`simpProgCorrectStoreGlobCase` and the exact `CrepSemHOLState.setGlobals`.

The probe fixes an 8-bit state whose `globals` maps key `3w`; the Lean rows
below are stated over an arbitrary exact state (the width-8 fixture is a
specialization) so they also witness the same-module finite-support carrier.
-/

namespace Flapjack.Test.CrepArithStoreGlobParity

open Flapjack
open Flapjack.Basis.Pure.MlString

/-- Probe row `simp_prog_storeglob` (`crep_arithScript.sml:89`): `simp_prog`
    rewrites the stored expression and leaves the destination key. -/
example :
    crepSimpProgHOL (.storeGlob (3 : BitVec 5) (.const (7 : BitVec 8)) :
        CrepProgHOL 8) =
      (.storeGlob (3 : BitVec 5) (.const (7 : BitVec 8)) : CrepProgHOL 8) := by
  simp only [crepSimpProgHOL, crepSimpExpHOL]

/-- Probe rows `evaluate_storeglob_const`, `evaluate_storeglob_mapc` and
    `storeglob_mapc_commute`: the tagged exact `StoreGlob` case turns the
    successful source equation into the same globals update under
    `crepSimpMapcsHOL`. -/
example {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (dst : BitVec 5) (value : BitVec width) :
    evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
        (crepSimpProgHOL (.storeGlob dst (.const value) : CrepProgHOL width)) =
      (none, crepSimpMapcsHOL
        (CrepSemHOLState.setGlobals dst (.word value) state)) := by
  apply simpProgCorrectStoreGlobCase
  · rw [evalCrepSemHOLProgExact_storeGlob_holShape]
    simp only [evalCrepSemHOLExp]
  · simp

/-- Probe row `evaluate_storeglob_missing_var`: the source evaluation of an
    unbound variable errors, which the non-`Error` premise excludes. -/
example {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (dst : BitVec 5)
    (missing : state.locals.lookup 99 = none) :
    evalCrepSemHOLProgExact state (.storeGlob dst (.var 99) : CrepProgHOL width) =
      (some .error, state) := by
  rw [evalCrepSemHOLProgExact_storeGlob_holShape]
  simp only [evalCrepSemHOLExp, missing]

end Flapjack.Test.CrepArithStoreGlobParity
