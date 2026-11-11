module

public import Flapjack.Pancake.Proofs.PanGlobals

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.Proofs.PanGlobals
@[expose] public section

namespace Flapjack.Test.PanGlobalsFunctionPreservationParity

open Flapjack
open Flapjack.Basis.Pure.MlString (ofString toStringOfBytes)
open Flapjack.Pancake.PanLang

/-! Executable observations corresponding to the HOL lemmas `resort_decls_preserve_functions`
    (`pan_globalsProofScript.sml:2055`) and `fperm_decs_FILTER_is_function`
    (`pan_globalsProofScript.sml:2032`), replayed on the tagged exact
    `resortDeclsHOL`/`fpermDecsHOL` twins. -/

def functionDeclaration : DeclHOL 64 :=
  .function
    { name := ofString "f", inline := false, exported := false, params := [],
      body := .skip, returnShape := .one }

def declarations : List (DeclHOL 64) :=
  [functionDeclaration,
   .decl (.comb [.one, .named (ofString "S")]) (ofString "g") (.const 7),
   .name (ofString "S") [], .exnDecl (ofString "E") (.named (ofString "T")),
   .decl .one (ofString "h") (.const 9)]

def functionPreservationGuard : Bool :=
  (((functionsHOL (resortDeclsHOL (width := 64) declarations)).map
      (fun entry => toStringOfBytes entry.1)) == ["f"]) &&
    (((functionsHOL (fpermDecsHOL (width := 64) (ofString "f") (ofString "b")
        (List.filter isFunctionHOL declarations))).map
      (fun entry => toStringOfBytes entry.1)) == ["b"])

#guard functionPreservationGuard

def runChecks : IO Bool := do
  let ok ←
    if functionPreservationGuard then
      IO.println "PASS pan_globals function preservation lemmas"
      pure true
    else
      pure false
  pure ok

end Flapjack.Test.PanGlobalsFunctionPreservationParity
