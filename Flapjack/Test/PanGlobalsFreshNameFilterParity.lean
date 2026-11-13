module

public import Flapjack.Pancake.Proofs.PanGlobals

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.Proofs.PanGlobals
@[expose] public section

namespace Flapjack.Test.PanGlobalsFreshNameFilterParity

open Flapjack
open Flapjack.Basis.Pure.MlString (ofString)
open Flapjack.Pancake.PanLang

/-! Executable observations corresponding to the HOL lemmas `fresh_name_correct`
    (`pan_globalsProofScript.sml:993`), `fresh_name_correct'`
    (`pan_globalsProofScript.sml:1003`), and `FILTER_decs_fperm_decs`
    (`pan_globalsProofScript.sml:2832`).  The `FILTER_decs_fperm_decs`
    observation runs on the tagged exact `fpermDecsHOL`/`exceptionsHOL` twins. -/

def functionDeclaration : DeclHOL 64 :=
  .function
    { name := ofString "f", inline := false, exported := false, params := [],
      body := .skip, returnShape := .one }

def declarations : List (DeclHOL 64) :=
  [functionDeclaration,
   .decl (.comb [.one, .named (ofString "S")]) (ofString "g") (.const 7),
   .name (ofString "S") [], .exnDecl (ofString "E") (.named (ofString "T")),
   .decl .one (ofString "h") (.const 9)]

def freshNameFilterGuard : Bool :=
  (!(["x", "x'", "y"].contains (globalFreshName "x" ["x", "x'", "y"]))) &&
    ((exceptionsHOL (List.filter (fun declaration => !isFunctionHOL declaration)
        (fpermDecsHOL (width := 64) (ofString "f") (ofString "b") declarations))).length ==
      (exceptionsHOL (List.filter (fun declaration => !isFunctionHOL declaration)
        declarations)).length)

#guard freshNameFilterGuard

def runChecks : IO Bool := do
  let ok ←
    if freshNameFilterGuard then
      IO.println "PASS pan_globals fresh_name_correct and FILTER_decs_fperm_decs"
      pure true
    else
      pure false
  pure ok

end Flapjack.Test.PanGlobalsFreshNameFilterParity
