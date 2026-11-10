module

public import Flapjack.Pancake.Proofs.PanGlobals
public import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
public import Flapjack.Test.Fixtures.PanGlobals

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.Proofs.PanGlobals
public meta import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
public meta import Flapjack.Test.Fixtures.PanGlobals
@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Flapjack.Test.PanGlobalsResortDeclsEvaluateParity

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Test.Fixtures.PanGlobals



abbrev functionDecl : FunDeclHOL 8 :=
  { name := ml "f"
    inline := false
    exported := false
    params := [(ml "x", ShapeHOL.one)]
    body := ProgHOL.skip
    returnShape := ShapeHOL.one }

/-- A mixed declaration list: a function, a global declaration, and an
    exception declaration. -/
abbrev decsTest : List (DeclHOL 8) :=
  [ .function functionDecl
  , .decl ShapeHOL.one (ml "g") (ExpHOL.const 7)
  , .exnDecl (ml "E") ShapeHOL.one ]

/-- `resort_decls` moves the `ExnDecl` first, then the `Decl`, then the
    `Function`. -/
def resortOrderGuard : Bool :=
  match resortDeclsHOL decsTest with
  | [.exnDecl _ _, .decl _ _ _, .function _] => true
  | _ => false

def wordOfGlobal (state : PanSemStateFiniteExact 8 Unit) (name : String) : Option Nat :=
  match state.globals.lookup (ml name) with
  | some (.val (.word value)) => some value.toNat
  | _ => none

def eshapeIsOne (state : PanSemStateFiniteExact 8 Unit) (name : String) : Bool :=
  match state.eshapes.lookup (ml name) with
  | some ShapeHOL.one => true
  | _ => false

def codeHasFunction (state : PanSemStateFiniteExact 8 Unit) (name : String) : Bool :=
  (state.code.lookup (ml name)).isSome

/-- The concrete `evaluate_decls` result is the same for the original and the
    resorted ordering: the global `g`, the exception shape `E`, and the function
    code `f` are all recorded. -/
def evaluateAgreesGuard : Bool :=
  match evaluateDeclsHOLFinite state0 decsTest,
      evaluateDeclsHOLFinite state0 (resortDeclsHOL decsTest) with
  | some original, some resorted =>
      wordOfGlobal original "g" == some 7 &&
        wordOfGlobal resorted "g" == some 7 &&
        eshapeIsOne original "E" && eshapeIsOne resorted "E" &&
        codeHasFunction original "f" && codeHasFunction resorted "f"
  | _, _ => false

example :
    PanSemStateFiniteExact.evaluateDeclsHOLFinite state0 (resortDeclsHOL decsTest) =
      PanSemStateFiniteExact.evaluateDeclsHOLFinite state0 decsTest :=
  resortDeclsEvaluate state0 decsTest (by decide)

example (state' : PanSemStateFiniteExact 8 Unit)
    (h : PanSemStateFiniteExact.evaluateDeclsHOLFinite state0 decsTest = some state') :
    PanSemStateFiniteExact.evaluateDeclsHOLFinite state0 (resortDeclsHOL decsTest) = some state' :=
  resortDeclsEvaluateImp state0 decsTest state' h (by decide)

example :
    PanSemStateFiniteExact.evaluateDeclsHOLFinite state0
        ([.decl ShapeHOL.one (ml "g") (ExpHOL.const 7)] ++ [.function functionDecl])
      = PanSemStateFiniteExact.evaluateDeclsHOLFinite state0
          (.function functionDecl :: [.decl ShapeHOL.one (ml "g") (ExpHOL.const 7)]) :=
  evaluateDeclsOneFunLast (y := .function functionDecl)
    (xs := [.decl ShapeHOL.one (ml "g") (ExpHOL.const 7)]) state0 (by rfl) (by decide)

private def parityGuard : Bool :=
  resortOrderGuard && evaluateAgreesGuard

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS pan_globals resort_decls_evaluate (exact carriers) reordering and evaluator agreement"
    pure true
  else
    IO.println "FAIL pan_globals resort_decls_evaluate (exact carriers)"
    pure false

end Flapjack.Test.PanGlobalsResortDeclsEvaluateParity
