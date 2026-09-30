/-
Parity for the exact HOL `pan_globalsProof$resort_decls_evaluate` cluster
(`cakeml/pancake/proofs/pan_globalsProofScript.sml:1854-1950`): the ports
`evaluateDeclsOneFunLast`, `resortDeclsEvaluate`, and
`resortDeclsEvaluateImp` over the reviewed finite-support carrier.

There is no direct original-HOL `EVAL` oracle row for these *theorems*: the HOL
statements quantify over an arbitrary state and declaration list, and the
`scripts/hol-probes` harness records concrete evaluator values, not proof-engine
theorem instances.  This module therefore replays each HOL statement
kernel-checked against a concrete declaration list (`resortOrderGuard` shows
`resort_decls` moving the `ExnDecl` before the `Decl` before the `Function`,
and the `example`s apply the ported theorems to concrete lists), plus `#guard`
rows that the concrete `evaluate_decls` results agree on both orderings.  No
oracle row is fabricated.
-/
import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

namespace Flapjack.Test.PanGlobalsResortDeclsEvaluateParity

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

private abbrev Word8 := RiscV.Word 8

abbrev ml (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

private abbrev emptyValues : HolFiniteMapExact MlS (ValueHOL 8) :=
  HolFiniteMapExact.empty

private abbrev emptyShapes : HolFiniteMapExact MlS ShapeHOL :=
  HolFiniteMapExact.empty

private abbrev emptyCode :
    HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 8 × ShapeHOL) :=
  HolFiniteMapExact.empty

abbrev state0 : PanSemStateFiniteExact 8 Unit :=
  { locals := emptyValues
    globals := emptyValues
    structs := []
    code := emptyCode
    eshapes := emptyShapes
    memory := fun _ => .word 0
    memaddrs := fun _ => False
    shMemaddrs := fun _ => False
    clock := 5
    be := false
    ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
    baseAddr := 0
    topAddr := 100 }

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
