import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.PanLang.Prog

namespace Flapjack.Test.PanGlobalsNewMainNameExactParity

/-! Direct parity for the exact `pan_globals$new_main_name_def` port
    (`pan_globalsScript.sml:224`) over the `mlstring`-keyed `DeclHOL` carrier.

    Replays the four direct HOL-EVAL rows of
    `scripts/hol-probes/pan_globals_new_main_name_probe.out`
    (`empty=«main»`, `two_collisions=«main''»`, `mixed=«main'»`,
    `absent=«main»`) through the tagged `newMainNameHOL`, decoding the exact
    `MlS` result with the byte codec for comparison. -/

open Flapjack
open Flapjack.Pancake.PanLang
  (MlS DeclHOL FunDeclHOL ShapeHOL ExpHOL ProgHOL)
open Flapjack.Basis.Pure.MlString (ofString toStringOfBytes)

/-- Exact-carrier analogue of the production `functionDecl`: a `DeclHOL`
    function declaration with no parameters, `Skip` body, `One` return shape. -/
def functionDecl {width : Nat} [NeZero width] (name : MlS) : DeclHOL width :=
  .function
    { name := name
      inline := false
      exported := false
      params := []
      body := .skip
      returnShape := .one }

/-- Rows from `pan_globals_new_main_name_probe.out` over the exact carrier. -/
def parityGuard {width : Nat} [NeZero width] : Bool :=
  toStringOfBytes (newMainNameHOL (width := width) ([] : List (DeclHOL width))) == "main" &&
  toStringOfBytes (newMainNameHOL (width := width)
    [functionDecl (width := width) (ofString "main"),
     functionDecl (width := width) (ofString "main'")]) == "main''" &&
  toStringOfBytes (newMainNameHOL (width := width)
    [.decl .one (ofString "g") (.const 7), .name (ofString "S") [],
     .exnDecl (ofString "E") .one,
     functionDecl (width := width) (ofString "main")]) == "main'" &&
  toStringOfBytes (newMainNameHOL (width := width)
    [functionDecl (width := width) (ofString "worker")]) == "main"

#eval parityGuard (width := 64)
#guard (parityGuard (width := 64))

def runChecks : IO Bool := do
  let result := parityGuard (width := 64)
  IO.println (if result then
    "PASS pan_globals new_main_name_def exact-carrier parity (4 HOL rows)"
    else "FAIL pan_globals new_main_name_def exact-carrier parity (4 HOL rows)")
  pure result

end Flapjack.Test.PanGlobalsNewMainNameExactParity
