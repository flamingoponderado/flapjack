import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrectExtCall
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Basis.Pure.MlString

/-!
# Exact-carrier parity for the `ExtCall` case of `simp_prog_correct`

Kernel-checked replay of the direct HOL rows in
`scripts/hol-probes/crep_arith_ext_call_probe.out` against the tagged exact
`simpProgCorrectExtCallCase` and the exact `CrepSemHOLState` carrier.

The probe fixes an 8-bit state with empty locals, so the `ExtCall` clause falls
into its missing-locals `(SOME Error, s)` branch; the width-8 fixtures below
specialize the same exact carriers.  The `simp_prog` and code-only `mapcs` rows
are stated over arbitrary exact states.
-/

namespace Flapjack.Test.CrepArithExtCallParity

open Flapjack
open Flapjack.Basis.Pure.MlString

/-- Width-8 concrete FFI state used by the probe fixtures. -/
private def ffi0 : HolFfiState Unit :=
  { oracle := fun _ state _ _ => .ret state [], ffiState := (), ioEvents := [] }

/-- Width-8 concrete memory (`\a. Word 0w`) used by the probe fixtures. -/
private def mem8 : BitVec 8 → HolWordLab 8 := fun _ => .word (0 : BitVec 8)

/-- Width-8 exact state with empty locals, mirroring the probe's
    `s with locals := FEMPTY`. -/
private def stateEmpty : CrepSemHOLState 8 Unit :=
  { locals := HolFiniteMapExact.empty
    globals := HolFiniteMapExact.empty
    code := HolFiniteMapExact.empty
    memory := mem8
    memaddrs := fun _ => False
    shMemaddrs := fun _ => False
    clock := 7
    be := false
    ffi := ffi0
    baseAddr := 0
    topAddr := 0 }

/-- Probe row `simp_prog_extcall` (`crep_arithScript.sml:113` catch-all):
    `simp_prog` leaves an `ExtCall` unchanged. -/
example {width : Nat} [NeZero width] :
    crepSimpProgHOL (.extCall (ofString "foo") 1 2 3 4 : CrepProgHOL width) =
      (.extCall (ofString "foo") 1 2 3 4 : CrepProgHOL width) := by
  simp only [crepSimpProgHOL]

/-- Probe row `extcall_mapcs_code`: the code-only `mapcs` rendering rewrites
    exactly the code map. -/
example :
    (crepSimpMapcsHOL stateEmpty).code =
      stateEmpty.code.map2 (fun (_, entry) => (entry.1, crepSimpProgHOL entry.2)) :=
  rfl

/-- Probe row `evaluate_extcall_missing_locals`: with an absent configuration
    local the exact clause returns `(some .error, s)`. -/
example :
    evalCrepSemHOLProgExact stateEmpty
        (.extCall (ofString "foo") 1 2 3 4 : CrepProgHOL 8) =
      (some .error, stateEmpty) := by
  rw [evalCrepSemHOLProgExact_extCall_holShape]
  simp [stateEmpty, HolFiniteMapExact.empty]

/-- Probe row `evaluate_extcall_mapc_missing_locals`: the same failure branch
    under the code-only `mapcs` update. -/
example :
    evalCrepSemHOLProgExact (crepSimpMapcsHOL stateEmpty)
        (.extCall (ofString "foo") 1 2 3 4 : CrepProgHOL 8) =
      (some .error, crepSimpMapcsHOL stateEmpty) := by
  rw [evalCrepSemHOLProgExact_extCall_holShape]
  simp [crepSimpMapcsHOL, stateEmpty, HolFiniteMapExact.empty]

/-- The tagged exact `ExtCall` case is inhabited at the HOL statement's type. -/
example : ∀ (state : CrepSemHOLState 8 Unit) (function : MlString)
      (configuration configurationLength array arrayLength : Nat)
      (result : Option (CrepResultHOLExact 8))
      (finalState : CrepSemHOLState 8 Unit),
      evalCrepSemHOLProgExact state
          (.extCall function configuration configurationLength array arrayLength : CrepProgHOL 8) =
        (result, finalState) →
      result ≠ some .error →
      evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
          (crepSimpProgHOL
            (.extCall function configuration configurationLength array arrayLength : CrepProgHOL 8)) =
        (result, crepSimpMapcsHOL finalState) :=
  simpProgCorrectExtCallCase

/-- The exact `ExtCall` case commutes with the code-only `mapcs` update. -/
example :
    evalCrepSemHOLProgExact (crepSimpMapcsHOL stateEmpty)
        (.extCall (ofString "foo") 1 2 3 4 : CrepProgHOL 8) =
      Prod.map id crepSimpMapcsHOL
        (evalCrepSemHOLProgExact stateEmpty
          (.extCall (ofString "foo") 1 2 3 4 : CrepProgHOL 8)) :=
  evalCrepSemHOLProgExact_extCall_mapcs stateEmpty (ofString "foo") 1 2 3 4

def runChecks : IO Bool := do
  IO.println "PASS crep_arith simp_prog_correct ExtCall case replays all 4 crep_arith_ext_call HOL rows"
  pure true

end Flapjack.Test.CrepArithExtCallParity
