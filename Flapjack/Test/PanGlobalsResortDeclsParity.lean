module

public import Flapjack.Pancake.PanGlobals

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.PanGlobals
@[expose] public section

namespace Flapjack.Test.PanGlobalsResortDeclsParity

/-! Direct parity for `pan_globals$resort_decls_def`
    (`pan_globalsScript.sml:179`) over the tagged exact `resortDeclsHOL` twin
    and its `DeclHOL`/`MlS` carriers.  The three direct-HOL rows of
    `scripts/hol-probes/pan_globals_resort_decls_probe.out` are replayed with
    the same values. -/

open Flapjack
open Flapjack.Basis.Pure.MlString (ofString toStringOfBytes)
open Flapjack.Pancake.PanLang

def nameIs (name : MlS) (expected : String) : Bool :=
  toStringOfBytes name == expected

def parityGuard : Bool :=
  (match resortDeclsHOL (width := 64)
      ([.decl .one (ofString "g") (.const 7), .name (ofString "S") [],
        .exnDecl (ofString "E") .one] : List (DeclHOL 64)) with
  | [.name structName [], .exnDecl exception .one,
      .decl .one globalName (.const value)] =>
      nameIs structName "S" && nameIs exception "E" &&
      nameIs globalName "g" && value == (7 : BitVec 64)
  | _ => false) &&
  (match resortDeclsHOL (width := 64)
      ([.name (ofString "S1") [], .name (ofString "S2") [],
        .exnDecl (ofString "E1") .one, .exnDecl (ofString "E2") .one,
        .decl .one (ofString "g1") (.const 1),
        .decl .one (ofString "g2") (.const 2)] : List (DeclHOL 64)) with
  | [.name firstName [], .name secondName [], .exnDecl firstExn .one,
      .exnDecl secondExn .one, .decl .one firstGlobal (.const firstValue),
      .decl .one secondGlobal (.const secondValue)] =>
      nameIs firstName "S1" && nameIs secondName "S2" &&
      nameIs firstExn "E1" && nameIs secondExn "E2" &&
      nameIs firstGlobal "g1" && nameIs secondGlobal "g2" &&
      firstValue == (1 : BitVec 64) && secondValue == (2 : BitVec 64)
  | _ => false)

#eval parityGuard
#guard parityGuard

/-- Replays the `empty` direct-HOL row (`resort_decls [] = []`). -/
def emptyGuard : Bool :=
  (resortDeclsHOL (width := 64) ([] : List (DeclHOL 64))).isEmpty

#eval emptyGuard
#guard emptyGuard

def runChecks : IO Bool := do
  IO.println (if parityGuard && emptyGuard then
    "PASS pan_globals resort_decls_def parity (3 HOL rows)"
    else "FAIL pan_globals resort_decls_def parity (3 HOL rows)")
  pure (parityGuard && emptyGuard)

end Flapjack.Test.PanGlobalsResortDeclsParity
