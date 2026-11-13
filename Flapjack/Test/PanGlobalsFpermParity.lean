module

public import Flapjack.Pancake.PanGlobals

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.PanGlobals
@[expose] public section

namespace Flapjack.Test.PanGlobalsFpermParity

/-! Direct parity for `pan_globals$fperm_def`
    (`pan_globalsScript.sml:191`) over the tagged exact `fpermHOL` twin and its
    `ProgHOL`/`MlS` carriers.  The four direct-HOL rows of
    `scripts/hol-probes/pan_globals_fperm_probe.out` are replayed with the same
    values. -/

open Flapjack
open Flapjack.Basis.Pure.MlString (ofString toStringOfBytes)
open Flapjack.Pancake.PanLang

def nameIs (name : MlS) (expected : String) : Bool :=
  toStringOfBytes name == expected

def parityGuard : Bool :=
  let renamedCall :=
    fpermHOL (width := 64) (ofString "foo") (ofString "bar")
      (.call none (ofString "foo") [] : ProgHOL 64)
  let renamedDecCall :=
    fpermHOL (width := 64) (ofString "foo") (ofString "bar")
      (.decCall (ofString "x") .one (ofString "bar") [] (.skip : ProgHOL 64))
  let renamedHandler :=
    fpermHOL (width := 64) (ofString "foo") (ofString "bar")
      (.call (some (none, some (ofString "E", ofString "exn",
        (.call none (ofString "foo") [] : ProgHOL 64)))) (ofString "worker") [])
  let renamedControl :=
    fpermHOL (width := 64) (ofString "foo") (ofString "bar")
      (.seq
        (.ite (.const 0) (.call none (ofString "foo") [])
          (.while (.const 1)
            (.dec (ofString "x") .one (.const 2) (.call none (ofString "foo") []))))
        (.assign .local (ofString "x") (.const 3)) : ProgHOL 64)
  let unchanged :=
    fpermHOL (width := 64) (ofString "foo") (ofString "bar")
      (.return (.const 9) : ProgHOL 64)
  (match renamedCall with
  | .call none name [] => nameIs name "bar"
  | _ => false) &&
  (match renamedDecCall with
  | .decCall name .one function [] .skip =>
      nameIs name "x" && nameIs function "foo"
  | _ => false) &&
  (match renamedHandler with
  | .call (some (none, some (exception, handlerVar, .call none name [])))
      function [] =>
      nameIs exception "E" && nameIs handlerVar "exn" &&
      nameIs name "bar" && nameIs function "worker"
  | _ => false) &&
  (match renamedControl with
  | .seq
      (.ite (.const first) (.call none callName [])
        (.while (.const second)
          (.dec decName .one (.const value) (.call none innerName []))))
      (.assign .local assignName (.const assigned)) =>
      first == (0 : BitVec 64) && second == (1 : BitVec 64) &&
      value == (2 : BitVec 64) && assigned == (3 : BitVec 64) &&
      nameIs callName "bar" && nameIs innerName "bar" &&
      nameIs decName "x" && nameIs assignName "x"
  | _ => false) &&
  (match unchanged with
  | .return (.const value) => value == (9 : BitVec 64)
  | _ => false)

#eval parityGuard
#guard parityGuard

/-- Replays the direct original-HOL rows of
    `scripts/hol-probes/pan_globals_fperm_probe.out` and reports a PASS line
    (`flapjack-6nn.1.2`). -/
def runChecks : IO Bool := do
  IO.println (if parityGuard then
    "PASS pan_globals fperm_def parity (4 HOL rows)"
    else "FAIL pan_globals fperm_def parity (4 HOL rows)")
  pure parityGuard

end Flapjack.Test.PanGlobalsFpermParity
