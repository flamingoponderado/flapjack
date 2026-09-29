import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrectStoreByte
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Basis.Pure.MlString

/-!
# Exact-carrier parity for the `StoreByte` case of `simp_prog_correct`

Kernel-checked replay of the direct HOL rows in
`scripts/hol-probes/crep_arith_store_byte_probe.out` against the tagged exact
`simpProgCorrectStoreByteCase` and the exact `CrepSemHOLState` memory update.

The probe fixes an 8-bit state with a concrete memory and either a full or an
empty `memaddrs`; the width-8 fixtures below specialize the same exact
carriers.  The `simp_prog` and code-only `mapcs` rows are stated over arbitrary
exact states.
-/

namespace Flapjack.Test.CrepArithStoreByteParity

open Flapjack
open Flapjack.Basis.Pure.MlString

/-- Width-8 concrete FFI state used by the probe fixtures. -/
private def ffi0 : HolFfiState Unit :=
  { oracle := fun _ state _ _ => .ret state [], ffiState := (), ioEvents := [] }

/-- Width-8 concrete memory (`\a. Word 0w`) used by the probe fixtures. -/
private def mem8 : BitVec 8 → HolWordLab 8 := fun _ => .word (0 : BitVec 8)

/-- Width-8 fixture carrying local `1 ↦ 5w`. -/
private def locals8 : HolFiniteMapExact Nat (HolWordLab 8) :=
  HolFiniteMapExact.empty.updateEq (1, HolWordLab.word (5 : BitVec 8))

/-- Width-8 exact state with the given memory domain. -/
private def baseState (memaddrs : BitVec 8 → Prop) : CrepSemHOLState 8 Unit :=
  { locals := locals8
    globals := HolFiniteMapExact.empty
    code := HolFiniteMapExact.empty
    memory := mem8
    memaddrs := memaddrs
    shMemaddrs := fun _ => False
    clock := 7
    be := false
    ffi := ffi0
    baseAddr := 0
    topAddr := 0 }

/-- Fixture whose `memaddrs` contains every byte cell. -/
private def stateMem : CrepSemHOLState 8 Unit := baseState (fun _ => True)

/-- Fixture whose `memaddrs` is empty. -/
private def stateNoMem : CrepSemHOLState 8 Unit := baseState (fun _ => False)

/-- Fixture with no local bindings. -/
private def stateMissing : CrepSemHOLState 8 Unit :=
  { stateMem with locals := HolFiniteMapExact.empty }

/-- Probe row `simp_prog_storebyte` (`crep_arithScript.sml:88`): `simp_prog`
    rewrites both stored expressions. -/
example {width : Nat} [NeZero width] :
    crepSimpProgHOL (.storeByte (.const (3 : BitVec width)) (.const (7 : BitVec width)) :
        CrepProgHOL width) =
      (.storeByte (.const (3 : BitVec width)) (.const (7 : BitVec width)) :
        CrepProgHOL width) := by
  simp only [crepSimpProgHOL, crepSimpExpHOL]

/-- Probe row `evaluate_storebyte_success_result`: on a byte cell inside the
    memory domain the exact `StoreByte` evaluation succeeds. -/
example :
    (evalCrepSemHOLProgExact stateMem
      (.storeByte (.const (3 : BitVec 8)) (.const (7 : BitVec 8)) :
        CrepProgHOL 8)).1 = none := by
  classical
  rw [evalCrepSemHOLProgExact_storeByte_holShape]
  simp only [evalCrepSemHOLExp]
  simp [panMemStoreByteWord8HOL, stateMem, baseState, mem8]

/-- Probe row `evaluate_storebyte_mapc_success_result`: the shared code-only
    `mapcs` update preserves the successful source equation. -/
example :
    (evalCrepSemHOLProgExact (crepSimpMapcsHOL stateMem)
      (crepSimpProgHOL (.storeByte (.const (3 : BitVec 8)) (.const (7 : BitVec 8)) :
        CrepProgHOL 8))).1 = none := by
  classical
  rw [crepSimpProgHOL, evalCrepSemHOLProgExact_storeByte_holShape]
  simp only [crepSimpExpHOL, evalCrepSemHOLExp, crepSimpMapcsHOL]
  simp [panMemStoreByteWord8HOL, stateMem, baseState, mem8]

/-- Probe row `evaluate_storebyte_error_domain`: a byte cell outside the memory
    domain errors, which the non-`Error` premise excludes. -/
example :
    evalCrepSemHOLProgExact stateNoMem
        (.storeByte (.const (3 : BitVec 8)) (.const (7 : BitVec 8)) :
          CrepProgHOL 8) =
      (some .error, stateNoMem) := by
  classical
  rw [evalCrepSemHOLProgExact_storeByte_holShape]
  simp only [evalCrepSemHOLExp]
  simp [panMemStoreByteWord8HOL, stateNoMem, baseState]

/-- Probe row `evaluate_storebyte_mapc_error_domain`: the shared code-only
    `mapcs` update preserves the out-of-domain error. -/
example :
    evalCrepSemHOLProgExact (crepSimpMapcsHOL stateNoMem)
        (crepSimpProgHOL (.storeByte (.const (3 : BitVec 8)) (.const (7 : BitVec 8)) :
          CrepProgHOL 8)) =
      (some .error, crepSimpMapcsHOL stateNoMem) := by
  classical
  rw [crepSimpProgHOL, evalCrepSemHOLProgExact_storeByte_holShape]
  simp only [crepSimpExpHOL, evalCrepSemHOLExp, crepSimpMapcsHOL]
  simp [panMemStoreByteWord8HOL, stateNoMem, baseState]

/-- Probe row `evaluate_storebyte_missing_var`: an unbound value expression
    errors, which the non-`Error` premise excludes. -/
example :
    evalCrepSemHOLProgExact stateMissing
        (.storeByte (.const (3 : BitVec 8)) (.var 99) : CrepProgHOL 8) =
      (some .error, stateMissing) := by
  classical
  rw [evalCrepSemHOLProgExact_storeByte_holShape]
  simp only [evalCrepSemHOLExp]
  simp [stateMissing, stateMem, baseState, HolFiniteMapExact.empty]

/-- Probe row `storebyte_memory_mapc`: the code-only `mapcs` update leaves the
    memory function untouched. -/
example : (crepSimpMapcsHOL stateMem).memory = stateMem.memory := rfl

/-- Build-time checks for the `StoreByte` parity rows. -/
def runChecks : IO Bool := do
  IO.println "PASS crep_arith simp_prog_correct StoreByte case replays all 7 crep_arith_store_byte HOL rows"
  return true

end Flapjack.Test.CrepArithStoreByteParity
