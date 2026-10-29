import Flapjack.Compiler.Backend.Semantics.ClosSem.Call

/-! Replay representative original closure applications from the pinned HOL
probe; finite cases do not establish general evaluator correspondence. -/
namespace Flapjack.Test.ClosSemCallParity
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.Compiler.Backend.ClosLang

private def body : Flapjack.Compiler.Backend.ClosLang.Exp := .var .none 0
private def body2 : Flapjack.Compiler.Backend.ClosLang.Exp := .var .none 1
private def funs : List (Nat × Flapjack.Compiler.Backend.ClosLang.Exp) := [(1, body), (1, body2)]

example : destClosure 3 none (.closure none [] [.number 9] 2 body) [.number 1] =
    some (.partialApp (.closure none [.number 1] [.number 9] 2 body)) := rfl
example : destClosure 3 none (.closure none [] [.number 9] 2 body) [.number 1, .number 2, .number 3] =
    some (.fullApp body [.number 2, .number 3, .number 9] [.number 1]) := rfl
example : destClosure 3 (some 4) (.closure (some 3) [] [] 1 body) [.number 1] = none := rfl
example : destClosure 3 (some 12) (.recclosure (some 10) [] [] funs 1) [.number 7] =
    some (.fullApp body2 [.number 7, .recclosure (some 10) [] [] funs 0,
      .recclosure (some 10) [] [] funs 1] []) := rfl
example : destClosure 3 none (.recclosure none [] [] [(1, body)] 1) [.number 7] = none := rfl

end Flapjack.Test.ClosSemCallParity
