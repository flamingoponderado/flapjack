import Flapjack.Compiler.Inference.Infer.Core
import Flapjack.CakeParser.Frontend

/-! Replay original HOL expression/pattern inference with state. -/
namespace Flapjack.Test.CakeInferCoreParity
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Inference
open Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.Infer.Core
open Flapjack.Basis.Pure.MlString

private def initial : State := ⟨0, .ln, 15⟩
private def idFn : Exp := .fn (ofString "x") (.var (.short (ofString "x")))

#guard match inferExprFuel 100 100 emptyEnv idFn initial with
  | .ok (t, s) => t == .app [.uvar 0, .uvar 0] 4 && s.nextUvar == 1 &&
      s.nextId == 15 && sptIsEmpty s.subst
  | _ => false

#guard match inferPatternFuel 100 100 emptyEnv
    (.pcon none [.pvar (ofString "x"), .pref (.pvar (ofString "y"))]) initial with
  | .ok ((t, [(y, ty), (x, tx)]), s) =>
      t == .app [.uvar 0, .app [.uvar 1] 7] 9 &&
      x == ofString "x" && y == ofString "y" && tx == .uvar 0 && ty == .uvar 1 &&
      s.nextUvar == 2 && s.nextId == 15 && sptIsEmpty s.subst
  | _ => false

#guard match inferExprFuel 100 100 emptyEnv (.app .opapp [idFn, .lit (.intLit 1)]) initial with
  | .ok (t, s) => t == .uvar 1 && s.nextUvar == 2 && s.nextId == 15 &&
      sptLookup 0 s.subst == some (.app [] 5) && sptLookup 1 s.subst == some (.app [] 5)
  | _ => false

#guard match Flapjack.CakeParser.Frontend.parseSourceFuel 500 500 (ofString "fn x => x;").explode with
  | .success [.dlet _ _ expr] => match inferExprFuel 100 100 emptyEnv expr initial with
    | .ok (t, s) => t == .app [.uvar 0, .uvar 0] 4 && s.nextUvar == 1
    | _ => false
  | _ => false


#guard match inferExprFuel 100 100 emptyEnv
    (.letrec [(ofString "f", ofString "x", .var (.short (ofString "x")))]
      (.var (.short (ofString "f")))) initial with
  | .ok (t, s) => t == .uvar 0 && s.nextUvar == 2 &&
      sptLookup 0 s.subst == some (.app [.uvar 1, .uvar 1] 4)
  | _ => false

private def intEnv : Env :=
  { emptyEnv with infT := .bind [(ofString "int", ([], .app [] 5))] [] }

#guard match inferExprFuel 100 100 intEnv
    (.tannot (.lit (.intLit 3)) (.atapp [] (.short (ofString "int")))) initial with
  | .ok (t, s) => t == .app [] 5 && s.nextUvar == 0 && sptIsEmpty s.subst
  | _ => false

end Flapjack.Test.CakeInferCoreParity
