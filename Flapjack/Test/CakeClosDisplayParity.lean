module

public import Flapjack.Compiler.Backend.PresLang.Clos
public import Flapjack.Compiler.Backend.SourceLet
public import Flapjack.Compiler.Backend.SourceToFlat.Eliminate
public import Flapjack.Compiler.Backend.FlatToClos.Compile
public import Flapjack.Compiler.Backend.Backend.PrimSrcConfig.Executable
public import Flapjack.CakeParser.Frontend

-- Checks below run compiled code from these modules.
public meta import Flapjack.CakeParser.Frontend
public meta import Flapjack.Compiler.Backend.Backend.PrimSrcConfig.Executable
public meta import Flapjack.Compiler.Backend.FlatToClos.Compile
public meta import Flapjack.Compiler.Backend.PresLang.Clos
public meta import Flapjack.Compiler.Backend.SourceLet
public meta import Flapjack.Compiler.Backend.SourceToFlat.Eliminate
@[expose] public section

/-! `after flat_to_clos` from pinned CakeML's explorer for a source program
with a datatype and a recursive function. -/
namespace Flapjack.Test.CakeClosDisplayParity

open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend

private def source : String :=
  "datatype t = A | B int; fun f x = case x of A => ~1 | B n => n; val x = f (B 7);"

private def expected : String :=
  "(dec\n   (let\n      ((b <- (op AllocGlobal (op (Const 1)))) (a <- (op (Cons 0))))\n" ++
  "      (op (SetGlobal 0) (var a))))\n\n" ++
  "(dec\n   (let\n      ((a <-\n            (let\n               ()\n" ++
  "               (op AllocGlobal (op (Const 3))))))\n      (op (Cons 0))))\n\n" ++
  "(dec (op (SetGlobal 1) (op Ref (op (Cons 0)))))\n\n" ++
  "(dec\n   (letrec<f> none none\n      ((a (b)\n            (let\n               ((c <- (var b)))\n" ++
  "               (if (op (TagLenEq 0 0) (var c))\n                  (op (Const ~1))\n" ++
  "                  (let\n                     ((d <- (op El (op (Const 0)) (var c))))\n" ++
  "                     (let\n                        ((e <- (var d)))\n                        (var e)))))))\n" ++
  "      (op (SetGlobal 2) (var a))))\n\n" ++
  "(dec\n   (let\n      ((a <-\n            (app none (op (Global 2))\n" ++
  "               (op (Constant (ConstCons 0 ((ConstInt 7))))))))\n" ++
  "      (let\n         ((b <- (var a)))\n         (op (SetGlobal 3) (var b)))))\n\n"

private def closureStage : Option String :=
  match Flapjack.CakeParser.Frontend.parseSourceFuel 20000 20000 (ofString source).explode with
  | .success ds =>
      let (_, flat) := SourceToFlat.compileTotal Backend.primSrcConfigExecutable (SourceLet.compileDecs ds)
      some (String.join (PresLang.Clos.sourcePrograms (FlatToClos.compileProg flat) []))
  | _ => none

#guard closureStage == some expected

#guard [0, 25, 26, 27, 51, 52, 701, 702].map PresLang.Clos.varName ==
  ["a", "z", "aa", "ab", "az", "ba", "zz", "aaa"]

end Flapjack.Test.CakeClosDisplayParity
