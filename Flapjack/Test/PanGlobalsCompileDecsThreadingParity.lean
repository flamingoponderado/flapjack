module

public import Flapjack.Pancake.Proofs.PanGlobals

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.Proofs.PanGlobals
@[expose] public section

namespace Flapjack.Test.PanGlobalsCompileDecsThreadingParity

open Flapjack

/-- The pass context used by the direct-HOL fixture
    (`scripts/hol-probes/pan_globals_compile_decs_probeScript.sml`). -/
def compileContext : GlobalPassContext Nat :=
  { globals := []
    globalsSize := 0
    maxGlobalsSize := 16
    bytesInWord := 1
    fromNat := id }

/-- A function whose body reads the global `g`, which is declared *after* it in
    `functionBeforeDecl`. -/
def globalFunction : Decl Nat :=
  .function
    { name := "f", inline := false, exported := false, params := [],
      body := .assign .local "x" (.var .global "g"), returnShape := .one }

def functionBeforeDecl : List (Decl Nat) :=
  [globalFunction, .decl .one "g" (.const 7)]

def functionAfterDecl : List (Decl Nat) :=
  [.decl .one "g" (.const 7), globalFunction]

def nonFunctionDeclarations : List (Decl Nat) :=
  [.decl .one "g" (.const 7), .name "S" [], .exnDecl "E" .one]

def threadedBefore : GlobalCompileDecsResult Nat :=
  globalCompileDecsThreaded compileContext functionBeforeDecl

def threadedAfter : GlobalCompileDecsResult Nat :=
  globalCompileDecsThreaded compileContext functionAfterDecl

def productionBefore : GlobalCompileDecsResult Nat :=
  globalCompileDecs compileContext functionBeforeDecl

def threadedNonFunction : GlobalCompileDecsResult Nat :=
  globalCompileDecsThreaded compileContext nonFunctionDeclarations

/-- Classifies a compiled function body: `0` is an unresolved global read
    (`Const`), `1` a resolved one (`Load`), `2` anything else. -/
def bodyKind : Prog Nat → Nat
  | .assign _ _ (.const _) => 0
  | .assign _ _ (.load _ _) => 1
  | _ => 2

def firstFunctionBodyKind (result : GlobalCompileDecsResult Nat) : Nat :=
  match result.functions with
  | [.function function] => bodyKind function.body
  | _ => 3

/-- The HOL `function_before_decl` row: the later `g` declaration is not yet in
    scope, so the threaded pass leaves the body's global read unresolved. -/
theorem threadedBeforeBodyUnresolved : firstFunctionBodyKind threadedBefore = 0 := by
  simp [firstFunctionBodyKind, threadedBefore, globalCompileDecsThreaded, bodyKind,
    globalFunction, functionBeforeDecl, globalCompileProg, globalCompileExp,
    compileContext, lookupInfo]

/-- The HOL `function_after_decl` row: with `g` declared first, the threaded
    pass resolves the global read. -/
theorem threadedAfterBodyResolved : firstFunctionBodyKind threadedAfter = 1 := by
  simp [firstFunctionBodyKind, threadedAfter, globalCompileDecsThreaded, bodyKind,
    globalFunction, functionAfterDecl, globalCompileProg, globalCompileExp,
    compileContext, globalAddress, lookupInfo]

/-- The production pass now uses the threaded definition, so it also leaves the
    forward reference unresolved. -/
theorem productionBeforeBodyUnresolved : firstFunctionBodyKind productionBefore = 0 := by
  simp [firstFunctionBodyKind, productionBefore, bodyKind, globalFunction,
    functionBeforeDecl, globalCompileDecs, globalCompileDecsThreaded,
    globalCompileProg, globalCompileExp, compileContext, globalAddress,
    lookupInfo]

/-- Direct rows for the exact `fresh_name` port, mirroring the
    `fresh_name_clear` / `fresh_name_missing_empty` / `fresh_name_hit` /
    `fresh_name_seed` rows of `scripts/hol-probes/pan_globals_compile_decs_probe.out`
    (HOL: `«x»`, `«»`, `«'''»`, `«vn''»`). -/
def freshNameChecks : List Bool :=
  [ freshNameHOL "x" ["y"] == "x"
  , freshNameHOL "" [] == ""
  , freshNameHOL "" ["", "'", "''"] == "'''"
  , freshNameHOL "vn'" ["vn'"] == "vn''" ]

#eval freshNameChecks
#guard freshNameChecks.all id

def threadingGuard : Bool :=
  firstFunctionBodyKind threadedBefore == 0 &&
  firstFunctionBodyKind threadedAfter == 1 &&
  firstFunctionBodyKind productionBefore == 0 &&
  threadedBefore.functions.all globalDeclIsFunction &&
  threadedNonFunction.functions.isEmpty

#eval threadingGuard
#guard threadingGuard

def runChecks : IO Bool := do
  let threadingOk ← if threadingGuard then
      IO.println "PASS pan_globals compile_decs context threading (Function before Decl)"
      pure true
    else
      IO.println "FAIL pan_globals compile_decs context threading (Function before Decl)"
      pure false
  pure threadingOk

end Flapjack.Test.PanGlobalsCompileDecsThreadingParity
