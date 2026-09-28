import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.PanLang.Prog

namespace Flapjack.Test.PanGlobalsTransformsExactParity

/-! Direct exact-carrier replay of HOL `resort_decls_def` and `dec_shapes_def`
(`pan_globalsScript.sml:179` and `:228-234`) against the fixtures captured in
`scripts/hol-probes/pan_globals_resort_decls_probe.out` and
`scripts/hol-probes/pan_globals_dec_shapes_probe.out`. -/

open Flapjack
open Flapjack.Pancake.PanLang
  (DeclHOL FunDeclHOL ShapeHOL MlS)
open Flapjack.Basis.Pure.MlString (ofString)

def functionDecl {width : Nat} [NeZero width] (name : MlS) : DeclHOL width :=
  .function
    { name := name
      inline := false
      exported := false
      params := []
      body := .skip
      returnShape := .one }

def resortMixed {width : Nat} [NeZero width] : Bool :=
  match resortDeclsHOL
    ([.decl .one (ofString "g") (.const 7),
      .name (ofString "S") [],
      .exnDecl (ofString "E") .one] : List (DeclHOL width)) with
  | [.name structName [], .exnDecl exception .one, .decl .one globalName (.const value)] =>
      structName == ofString "S" && exception == ofString "E" &&
        globalName == ofString "g" && value == 7
  | _ => false

def resortStableGroups {width : Nat} [NeZero width] : Bool :=
  match resortDeclsHOL
    ([.decl .one (ofString "g1") (.const 1),
      .name (ofString "S1") [], .exnDecl (ofString "E1") .one,
      .name (ofString "S2") [], .exnDecl (ofString "E2") .one,
      .decl .one (ofString "g2") (.const 2)] : List (DeclHOL width)) with
  | [.name firstName [], .name secondName [], .exnDecl firstExn .one,
      .exnDecl secondExn .one, .decl .one firstGlobal (.const firstValue),
      .decl .one secondGlobal (.const secondValue)] =>
      firstName == ofString "S1" && secondName == ofString "S2" &&
        firstExn == ofString "E1" && secondExn == ofString "E2" &&
        firstGlobal == ofString "g1" && secondGlobal == ofString "g2" &&
        firstValue == 1 && secondValue == 2
  | _ => false

def shapesMixed {width : Nat} [NeZero width] : Bool :=
  match decShapesHOL
    ([functionDecl (width := width) (ofString "f"),
      .decl (.comb [.one, .named (ofString "S")]) (ofString "g") (.const 7),
      .name (ofString "S") [], .exnDecl (ofString "E") (.named (ofString "T")),
      .decl .one (ofString "h") (.const 9)] : List (DeclHOL width)) with
  | [.comb [.one, .named name], .one] => name == ofString "S"
  | _ => false

def shapesFunctionsOnly {width : Nat} [NeZero width] : Bool :=
  (decShapesHOL
    ([functionDecl (width := width) (ofString "f")] : List (DeclHOL width))).isEmpty

def parityGuard {width : Nat} [NeZero width] : Bool :=
  resortMixed (width := width) && resortStableGroups (width := width) &&
    (resortDeclsHOL ([] : List (DeclHOL width))).isEmpty &&
    shapesMixed (width := width) && shapesFunctionsOnly (width := width) &&
    (decShapesHOL ([] : List (DeclHOL width))).isEmpty

#eval parityGuard (width := 64)
#guard parityGuard (width := 64)

def runChecks : IO Bool := do
  let result := parityGuard (width := 64)
  IO.println (if result then
    "PASS pan_globals resort_decls_def/dec_shapes_def exact-carrier HOL rows"
    else "FAIL pan_globals resort_decls_def/dec_shapes_def exact-carrier HOL rows")
  pure result

end Flapjack.Test.PanGlobalsTransformsExactParity
