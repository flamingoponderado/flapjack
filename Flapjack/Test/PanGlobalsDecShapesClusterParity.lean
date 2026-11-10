module

public import Flapjack.Pancake.Proofs.PanGlobals

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.Proofs.PanGlobals
@[expose] public section

namespace Flapjack.Test.PanGlobalsDecShapesClusterParity

open Flapjack

/-! Executable observations corresponding to the HOL `dec_shapes` cluster
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2328-2365`), exercised
    on a mixed fixture. `dec_shapes` is the production `globalDeclShapes`. -/
def functionDeclaration : Decl Nat :=
  .function
    { name := "f", inline := false, exported := false, params := [],
      body := .skip, returnShape := .one }

def declarations : List (Decl Nat) :=
  [functionDeclaration,
   .decl (.comb [.one, .named "S"]) "g" (.const 7),
   .name "S" [], .exnDecl "E" (.named "T"),
   .decl .one "h" (.const 9)]

def rest : List (Decl Nat) := [.decl .one "k" (.const 11)]

def functionOnly : List (Decl Nat) :=
  [functionDeclaration,
   .function
     { name := "g", inline := false, exported := false, params := [],
       body := .skip, returnShape := .one }]

def decShapesClusterGuard : Bool :=
  (match globalDeclShapes (declarations ++ rest) with
   | [.comb [.one, .named "S"], .one, .one] => true
   | _ => false) &&
  (globalDeclShapes functionOnly).isEmpty &&
  (match globalDeclShapes
      (globalDeclsFilter
        (fun declaration => !globalDeclIsFunction declaration) declarations) with
   | [.comb [.one, .named "S"], .one] => true
   | _ => false) &&
  (match globalDeclShapes
      (globalDeclsFilter globalDeclIsException declarations) with
   | [] => true
   | _ => false) &&
  (match globalDeclShapes (globalRenameDecls "foo" "bar" declarations) with
   | [.comb [.one, .named "S"], .one] => true
   | _ => false) &&
  (match globalDeclShapes (globalResortDecls declarations) with
   | [.comb [.one, .named "S"], .one] => true
   | _ => false)

#guard decShapesClusterGuard

def runChecks : IO Bool := do
  if decShapesClusterGuard then
    IO.println "PASS pan_globals dec_shapes cluster"
    pure true
  else
    IO.println "FAIL pan_globals dec_shapes cluster"
    pure false

end Flapjack.Test.PanGlobalsDecShapesClusterParity