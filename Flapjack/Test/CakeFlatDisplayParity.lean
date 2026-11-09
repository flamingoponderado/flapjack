import Flapjack.Compiler.Backend.PresLang.Flat
import Flapjack.Compiler.Backend.SourceLet
import Flapjack.Compiler.Backend.SourceToFlat.CompileProg
import Flapjack.Compiler.Backend.Backend.PrimSrcConfig.Executable
import Flapjack.CakeParser.Frontend

/-! The expected output is the `after source_to_flat` stage from the pinned
CakeML compiler with `--explore --exclude_prelude=true`. -/
namespace Flapjack.Test.CakeFlatDisplayParity

open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend

private def source : String :=
  "datatype t = A | B int; fun f x = case x of A => ~1 | B n => n; val x = f (B 7);"

private def expected : String :=
  "(let none (app (GlobalVarAlloc 3)) (con ConIdNone))\n\n" ++
  "(app (GlobalVarInit 0) (app Opref (con ConIdNone)))\n\n" ++
  "(letrec<>\n   ((f x\n         (mat (var_local x) ((Pcon) (lit)) ((Pcon (Pvar n)) (var_local n)))))\n" ++
  "   (app (GlobalVarInit 1) (var_local f)))\n\n" ++
  "(mat\n   (app Opapp (app (GlobalVarLookup 1)) (con (ConIdTyped 0 2) (lit)))\n" ++
  "   ((Pvar x) (app (GlobalVarInit 2) (var_local x))))\n\n"

private def flatStage : Option String :=
  match Flapjack.CakeParser.Frontend.parseSourceFuel 20000 20000 (ofString source).explode with
  | .success ds =>
      let ds := SourceLet.compileDecs ds
      let (_, flat) := SourceToFlat.compileProg Backend.primSrcConfigExecutable ds
      some (String.join (PresLang.Flat.expressions flat))
  | _ => none

#guard flatStage == some expected

private def byteName : MlString := .implode [BitVec.ofNat 8 255]

#guard PresLang.Flat.expressionBytes [.varLocal .none byteName] ==
  (ofString "(var_local ").explode ++ [BitVec.ofNat 8 255] ++ (ofString ")\n\n").explode

#guard match PresLang.Flat.expression (.varLocal (.cons .none 3) (ofString "x")) with
  | .item (some (.cons .none 3)) "var_local" _ => true
  | _ => false

end Flapjack.Test.CakeFlatDisplayParity
