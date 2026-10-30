import Flapjack.Compiler.Backend.BackendPasses.Frontend
import Flapjack.Compiler.Backend.Backend.PrimSrcConfig.Executable
import Flapjack.CakeParser.Frontend

/-! Complete six-stage prefix from the pinned CakeML explorer, with the
standard basis excluded. The reference digest is recorded in
`scripts/hol-probes/cake_explore_frontend.json`. -/
namespace Flapjack.Test.CakeFrontendStagesParity
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend

private def source : String := "datatype t = A | B int; fun f x = case x of A => ~1 | B n => n; val x = f (B 7);"

private def expected : List HolChar := (ofString "# original source code\n\n(Dtype (() t ((A ()) (B ((Attup () (Short int)))))))\n\n(Dletrec\n   (f x\n      (Lannot\n         (Mat (Lannot (Var (Short x)))\n            (((Pcon (some (Short A)) ()) (Lannot (Lit (IntLit ~1))))\n               ((Pcon (some (Short B)) ((Pvar n))) (Lannot (Var (Short n)))))))))\n\n(Dlet (Pvar x)\n   (Lannot\n      (App Opapp (Lannot (Var (Short f)))\n         (Lannot (Con (some (Short B)) ((Lit (IntLit 7))))))))\n\n# after source_let\n\n(Dtype (() t ((A ()) (B ((Attup () (Short int)))))))\n\n(Dletrec\n   (f x\n      (Lannot\n         (Mat (Lannot (Var (Short x)))\n            (((Pcon (some (Short A)) ()) (Lannot (Lit (IntLit ~1))))\n               ((Pcon (some (Short B)) ((Pvar n))) (Lannot (Var (Short n)))))))))\n\n(Dlet (Pvar x)\n   (Lannot\n      (App Opapp (Lannot (Var (Short f)))\n         (Lannot (Con (some (Short B)) ((Lit (IntLit 7))))))))\n\n# after source_to_flat\n\n(let none (app (GlobalVarAlloc 3)) (con ConIdNone))\n\n(app (GlobalVarInit 0) (app Opref (con ConIdNone)))\n\n(letrec<>\n   ((f x\n         (mat (var_local x) ((Pcon) (lit)) ((Pcon (Pvar n)) (var_local n)))))\n   (app (GlobalVarInit 1) (var_local f)))\n\n(mat\n   (app Opapp (app (GlobalVarLookup 1)) (con (ConIdTyped 0 2) (lit)))\n   ((Pvar x) (app (GlobalVarInit 2) (var_local x))))\n\n# after remove_flat\n\n(let none (app (GlobalVarAlloc 3)) (con ConIdNone))\n\n(app (GlobalVarInit 0) (app Opref (con ConIdNone)))\n\n(letrec<>\n   ((f x\n         (mat (var_local x) ((Pcon) (lit)) ((Pcon (Pvar n)) (var_local n)))))\n   (app (GlobalVarInit 1) (var_local f)))\n\n(mat\n   (app Opapp (app (GlobalVarLookup 1)) (con (ConIdTyped 0 2) (lit)))\n   ((Pvar x) (app (GlobalVarInit 2) (var_local x))))\n\n# after flat_pattern\n\n(let none (app (GlobalVarAlloc 3)) (con ConIdNone))\n\n(app (GlobalVarInit 0) (app Opref (con ConIdNone)))\n\n(letrec<>\n   ((f x\n         (let (some ..%) (var_local x)\n            (if (app (TagLenEq 0 0) (var_local ..%)) (lit)\n               (let (some ..') (app (El 0) (var_local ..%))\n                  (let (some n) (var_local ..') (var_local n)))))))\n   (app (GlobalVarInit 1) (var_local f)))\n\n(let (some ..%)\n   (app Opapp (app (GlobalVarLookup 1)) (con (ConIdTyped 0 2) (lit)))\n   (let (some x) (var_local ..%) (app (GlobalVarInit 2) (var_local x))))\n\n# after flat_to_clos\n\n(dec\n   (let\n      ((b <- (op AllocGlobal (op (Const 1)))) (a <- (op (Cons 0))))\n      (op (SetGlobal 0) (var a))))\n\n(dec\n   (let\n      ((a <-\n            (let\n               ()\n               (op AllocGlobal (op (Const 3))))))\n      (op (Cons 0))))\n\n(dec (op (SetGlobal 1) (op Ref (op (Cons 0)))))\n\n(dec\n   (letrec<f> none none\n      ((a (b)\n            (let\n               ((c <- (var b)))\n               (if (op (TagLenEq 0 0) (var c))\n                  (op (Const ~1))\n                  (let\n                     ((d <- (op El (op (Const 0)) (var c))))\n                     (let\n                        ((e <- (var d)))\n                        (var e)))))))\n      (op (SetGlobal 2) (var a))))\n\n(dec\n   (let\n      ((a <-\n            (app none (op (Global 2))\n               (op (Constant (ConstCons 0 ((ConstInt 7))))))))\n      (let\n         ((b <- (var a)))\n         (op (SetGlobal 3) (var b)))))\n\n").explode

private def actual : Option (List HolChar) :=
  match Flapjack.CakeParser.Frontend.parseSourceFuel 20000 20000 (ofString source).explode with
  | .success ds => some (BackendPasses.frontendReportBytes
      (BackendPasses.captureFrontend Backend.primSrcConfigExecutable ds))
  | _ => none

#guard actual == some expected

end Flapjack.Test.CakeFrontendStagesParity
