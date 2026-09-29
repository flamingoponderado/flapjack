import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrectStore32
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Basis.Pure.MlString

/-!
# Exact-carrier parity for the `Store32` case of `simp_prog_correct`

Kernel-checked replay of the direct HOL rows in
`scripts/hol-probes/crep_arith_store_32_probe.out` against the tagged exact
`simpProgCorrectStore32Case` and the exact `CrepSemHOLState` carriers.

The probe fixes an 8-bit little-endian state whose `memaddrs` is `{4w}` and
whose cell at `4w` holds `0xAA`; the Lean rows below are stated over an
arbitrary exact state (the width-8 fixture is a specialization) so they also
witness the same-module finite-support carrier.  The success row uses the
tagged case theorem, while the domain/alignment and failed-operand rows pin the
non-`Error` premise's failure branches.
-/

namespace Flapjack.Test.CrepArithStore32Parity

open Flapjack
open Flapjack.Basis.Pure.MlString
open Classical

/-- Probe row `simp_prog_store32` (`crep_arithScript.sml:87`): `simp_prog`
    rewrites both stored operands. -/
example :
    crepSimpProgHOL (.store32 (.const (4 : BitVec 8)) (.const (0x11 : BitVec 8)) :
        CrepProgHOL 8) =
      (.store32 (crepSimpExpHOL (.const (4 : BitVec 8)))
        (crepSimpExpHOL (.const (0x11 : BitVec 8))) : CrepProgHOL 8) := by
  simp only [crepSimpProgHOL]

/-- Probe rows `evaluate_store32_const`, `evaluate_store32_mapc` and
    `store32_mapc_commute`: the tagged exact `Store32` case turns a successful
    source equation into the same memory update under `crepSimpMapcsHOL`. -/
example {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (adr : BitVec width) (w : BitVec width)
    (memory : BitVec width → HolWordLab width)
    (hm : panMemStore32HOL state.memory state.memaddrs state.be adr
        (BitVec.ofNat 32 w.toNat) = some memory) :
    evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
        (crepSimpProgHOL (.store32 (.const adr) (.const w) : CrepProgHOL width)) =
      (none, crepSimpMapcsHOL { state with memory := memory }) := by
  classical
  apply simpProgCorrectStore32Case
  · rw [evalCrepSemHOLProgExact_store32_holShape]
    simp only [evalCrepSemHOLExp, hm]
  · simp

/-- Probe rows `evaluate_store32_domain_error` and
    `evaluate_store32_unaligned_error`: when `mem_store_32` returns `NONE` the
    source evaluation errors with the original state, which the non-`Error`
    premise excludes. -/
example {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (adr : BitVec width) (w : BitVec width)
    (hm : panMemStore32HOL state.memory state.memaddrs state.be adr
        (BitVec.ofNat 32 w.toNat) = none) :
    evalCrepSemHOLProgExact state
        (.store32 (.const adr) (.const w) : CrepProgHOL width) =
      (some .error, state) := by
  classical
  rw [evalCrepSemHOLProgExact_store32_holShape]
  simp only [evalCrepSemHOLExp, hm]

/-- Probe row `evaluate_store32_missing_var`: the source evaluation of an
    unbound `src` operand errors, which the non-`Error` premise excludes. -/
example {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (adr : BitVec width)
    (missing : state.locals.lookup 99 = none) :
    evalCrepSemHOLProgExact state
        (.store32 (.const adr) (.var 99) : CrepProgHOL width) =
      (some .error, state) := by
  rw [evalCrepSemHOLProgExact_store32_holShape]
  simp only [evalCrepSemHOLExp, missing]

/-- Probe row `store32_mapc_commute`: the code-only `mapcs` update commutes
    with the `memory` update. -/
example {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (memory : BitVec width → HolWordLab width) :
    crepSimpMapcsHOL { state with memory := memory } =
      { crepSimpMapcsHOL state with memory := memory } :=
  crepSimpMapcsHOL_setMemory state memory

/-- Build-time checks for the `Store32` parity rows. -/
def runChecks : IO Bool := do
  IO.println "PASS crep_arith simp_prog_correct Store32 case replays all 7 crep_arith_store_32 HOL rows"
  return true

end Flapjack.Test.CrepArithStore32Parity
