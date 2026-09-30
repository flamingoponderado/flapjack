import Flapjack.Pancake.PanGlobals.CompileExpExact

/-! Direct replay of the captured original HOL rows in
`scripts/hol-probes/pan_globals_compile_decs_probe.out` against the exact
`DeclHOL`/`ProgHOL`/`PanGlobalsContextExact` definition.  The six checked rows
cover the empty case, each declaration constructor, and functions on both
sides of a global declaration so the context-at-source-position rule is
observable. -/

namespace Flapjack.Test.PanGlobalsCompileDecsExactParity

open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang

def initialContext : PanGlobalsContextExact 8 :=
  { globals := HolFiniteMapExact.empty
    globalsSize := 1
    maxGlobalsSize := 16 }

def nameIs (name : MlS) (expected : String) : Bool :=
  toStringOfBytes name == expected

def contextAtInitialSize (context : PanGlobalsContextExact 8) : Bool :=
  context.globalsSize == 1 && context.maxGlobalsSize == 16 &&
    (match context.globals.lookup (ofString "g") with
     | none => true
     | _ => false)

def contextWithGAtTwo (context : PanGlobalsContextExact 8) : Bool :=
  context.globalsSize == 2 && context.maxGlobalsSize == 16 &&
    match context.globals.lookup (ofString "g") with
    | some (.one, address) => address == 2
    | _ => false

def isGlobalInitializer (program : ProgHOL 8) (address value : BitVec 8) : Bool :=
  match program with
  | .store (.op .sub [.topAddr, .const actualAddress]) (.const actualValue) =>
      actualAddress == address && actualValue == value
  | _ => false

/-- Classifies the global read in the sole compiled function row: `0` is the
unresolved `Const 0w` branch, `1` is the resolved `Load One` branch. -/
def functionGlobalReadKind (declaration : DeclHOL 8) : Nat :=
  match declaration with
  | .function function =>
      if !nameIs function.name "f" then 3 else
      match function.body with
      | .assign .local name (.const value) =>
          if nameIs name "x" && value == 0 then 0 else 3
      | .assign .local name (.load .one (.op .sub [.topAddr, .const address])) =>
          if nameIs name "x" && address == 2 then 1 else 3
      | _ => 3
  | _ => 3

def emptyRowGuard : Bool :=
  let result := compileDecsExactHOL initialContext []
  result.1.isEmpty && result.2.1.isEmpty && result.2.2.1.isEmpty &&
    contextAtInitialSize result.2.2.2

def declRowGuard : Bool :=
  let result := compileDecsExactHOL initialContext
    [.decl .one (ofString "g") (.const 7)]
  match result.1, result.2.1, result.2.2.1 with
  | [initializer], [], [] =>
      isGlobalInitializer initializer 2 7 && contextWithGAtTwo result.2.2.2
  | _, _, _ => false

def exceptionRowGuard : Bool :=
  let result := compileDecsExactHOL initialContext
    [.exnDecl (ofString "E") .one]
  result.1.isEmpty && result.2.1.isEmpty &&
    (match result.2.2.1 with
     | [.exnDecl exception .one] => nameIs exception "E"
     | _ => false) && contextAtInitialSize result.2.2.2

def nameRowGuard : Bool :=
  let result := compileDecsExactHOL initialContext
    [.name (ofString "S") []]
  result.1.isEmpty && result.2.1.isEmpty && result.2.2.1.isEmpty &&
    contextAtInitialSize result.2.2.2

def functionDeclaration : DeclHOL 8 :=
  .function
    { name := ofString "f", inline := false, exported := false, params := [],
      body := .assign .local (ofString "x") (.var .global (ofString "g")),
      returnShape := .one }

def functionBeforeDeclRowGuard : Bool :=
  let result := compileDecsExactHOL initialContext
    [functionDeclaration, .decl .one (ofString "g") (.const 7)]
  match result.1, result.2.1, result.2.2.1 with
  | [initializer], [.function function], [] =>
      isGlobalInitializer initializer 2 7 &&
      functionGlobalReadKind (.function function) == 0 &&
      contextWithGAtTwo result.2.2.2
  | _, _, _ => false

def functionAfterDeclRowGuard : Bool :=
  let result := compileDecsExactHOL initialContext
    [.decl .one (ofString "g") (.const 7), functionDeclaration]
  match result.1, result.2.1, result.2.2.1 with
  | [initializer], [.function function], [] =>
      isGlobalInitializer initializer 2 7 &&
      functionGlobalReadKind (.function function) == 1 &&
      contextWithGAtTwo result.2.2.2
  | _, _, _ => false

def exactCompileDecsOracleGuard : Bool :=
  emptyRowGuard && declRowGuard && exceptionRowGuard && nameRowGuard &&
    functionBeforeDeclRowGuard && functionAfterDeclRowGuard

#eval exactCompileDecsOracleGuard
#guard exactCompileDecsOracleGuard

def runChecks : IO Bool := do
  if exactCompileDecsOracleGuard then
    IO.println "PASS exact pan_globals compile_decs_def matches all six direct HOL rows"
    pure true
  else
    IO.println "FAIL exact pan_globals compile_decs_def direct HOL rows"
    pure false

end Flapjack.Test.PanGlobalsCompileDecsExactParity
