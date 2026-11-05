import Flapjack.Pancake.Proofs.PanGlobals

namespace Flapjack.Test.PanGlobalsCompileDecsStructuralParity

open Flapjack

def compileContext : GlobalPassContext Nat :=
  { globals := []
    globalsSize := 1
    maxGlobalsSize := 16
    bytesInWord := 1
    fromNat := id }

def functionDeclaration : Decl Nat :=
  .function
    { name := "f", inline := false, exported := false, params := [],
      body := .skip, returnShape := .one }

def declarations : List (Decl Nat) :=
  [functionDeclaration, .decl .one "g" (.const 7), .name "S" [],
   .exnDecl "E" .one]

def nonFunctionDeclarations : List (Decl Nat) :=
  [.decl .one "g" (.const 7), .name "S" [], .exnDecl "E" .one]

def compileResult : GlobalCompileDecsResult Nat :=
  globalCompileDecs compileContext declarations

def compileDecsStructuralGuard : Bool :=
  let result := globalCompileDecs compileContext declarations
  result.functions.all globalDeclIsFunction &&
  (globalCompileDecs compileContext nonFunctionDeclarations).functions.isEmpty &&
  result.exceptions.length ==
    (globalDeclsFilter globalDeclIsException declarations).length &&
  ((functions result.functions).map (fun entry => entry.1) ==
    (functions declarations).map (fun entry => entry.1))

/-- Predicate that recognizes the function declaration renamed from `f` to
    `b`; true on every other declaration, matching the HOL hypothesis shape of
    `EVERY_fperm_decs`. -/
def renamedPredicate : Decl Nat → Bool
  | .function function => function.name == "b"
  | _ => true

def everyFpermDecsGuard : Bool :=
  (globalRenameDecls "f" "b" declarations).all renamedPredicate

def compileDecsFilterDeclsGuard : Bool :=
  let result := globalCompileDecs compileContext
    (globalDeclsFilter isDecl declarations)
  result.functions.isEmpty && result.exceptions.isEmpty &&
  (result.initializers.length == compileResult.initializers.length)

#eval everyFpermDecsGuard
#guard everyFpermDecsGuard
#eval compileDecsFilterDeclsGuard
#guard compileDecsFilterDeclsGuard

def runChecks : IO Bool := do
  let structuralOk ←
    if compileDecsStructuralGuard then
      IO.println "PASS pan_globals compile_decs structural lemmas"
      pure true
    else
      IO.println "FAIL pan_globals compile_decs structural lemmas"
      pure false
  let fpermFilterOk ←
    if everyFpermDecsGuard && compileDecsFilterDeclsGuard then
      IO.println "PASS pan_globals EVERY_fperm_decs and compile_decs_FILTER_decs"
      pure true
    else
      IO.println "FAIL pan_globals EVERY_fperm_decs and compile_decs_FILTER_decs"
      pure false
  pure (structuralOk && fpermFilterOk)

end Flapjack.Test.PanGlobalsCompileDecsStructuralParity