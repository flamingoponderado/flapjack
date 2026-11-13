module

public import Flapjack.Pancake.PanGlobals

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.PanGlobals
@[expose] public section

namespace Flapjack.Test.PanGlobalsFpermDecsParity

/-! Direct parity for `pan_globals$fperm_decs_def`
    (`pan_globalsScript.sml:216`) over the tagged exact `fpermDecsHOL` twin and
    its `DeclHOL`/`MlS` carriers.  The three direct-HOL rows of
    `scripts/hol-probes/pan_globals_fperm_decs_probe.out` are replayed with the
    same values. -/

open Flapjack
open Flapjack.Basis.Pure.MlString (ofString toStringOfBytes)
open Flapjack.Pancake.PanLang

def nameIs (name : MlS) (expected : String) : Bool :=
  toStringOfBytes name == expected

def sourceFunction : FunDeclHOL 64 :=
  { name := ofString "foo"
    inline := false
    exported := true
    params := []
    body := .call none (ofString "foo") []
    returnShape := .one }

def targetFunction : FunDeclHOL 64 :=
  { name := ofString "bar"
    inline := true
    exported := false
    params := []
    body := .decCall (ofString "x") .one (ofString "foo") [] .skip
    returnShape := .one }

def singletonNonFunctionDecls : List (DeclHOL 64) :=
  [.decl .one (ofString "g") (.const 7)]

def parityGuard : Bool :=
  let renamed :=
    fpermDecsHOL (width := 64) (ofString "foo") (ofString "bar")
      ([.decl .one (ofString "g") (.const 7), .function sourceFunction,
        .function targetFunction] : List (DeclHOL 64))
  match renamed with
  | [.decl .one globalName (.const globalValue), .function first, .function second] =>
      nameIs globalName "g" && globalValue == (7 : BitVec 64) &&
      nameIs first.name "bar" &&
      (match first.body with
      | .call none name [] => nameIs name "bar"
      | _ => false) &&
      nameIs second.name "foo" &&
      (match second.body with
      | .decCall name .one function [] .skip =>
          nameIs name "x" && nameIs function "bar"
      | _ => false) &&
      first.inline == false && first.exported == true &&
      second.inline == true && second.exported == false
  | _ => false

#eval parityGuard
#guard parityGuard

def emptyGuard : Bool :=
  (fpermDecsHOL (width := 64) (ofString "foo") (ofString "bar")
    ([] : List (DeclHOL 64))).isEmpty

#guard emptyGuard

def singletonGuard : Bool :=
  match fpermDecsHOL (width := 64) (ofString "foo") (ofString "bar")
      singletonNonFunctionDecls with
  | [.decl .one name (.const value)] => nameIs name "g" && value == (7 : BitVec 64)
  | _ => false

#guard singletonGuard

def runChecks : IO Bool := do
  IO.println (if parityGuard && emptyGuard && singletonGuard then
    "PASS pan_globals fperm_decs_def / fperm_decs_decls parity (3 HOL rows)"
    else "FAIL pan_globals fperm_decs_def / fperm_decs_decls parity (3 HOL rows)")
  pure (parityGuard && emptyGuard && singletonGuard)

end Flapjack.Test.PanGlobalsFpermDecsParity
