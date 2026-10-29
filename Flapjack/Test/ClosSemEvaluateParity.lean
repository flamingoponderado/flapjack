import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel

/-! Selected bounded evaluations replay the pinned HOL observations. The
extra fuel is not part of HOL evaluation and this is not an equivalence proof. -/
namespace Flapjack.Test.ClosSemEvaluateParity
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.Basis.Pure.MlString

example {C F : Type} (s : State C F) :
    (evaluateFuel 20 [.var .none 0] [.number 7] s).map Prod.fst = some (.val [.number 7]) := rfl
example {C F : Type} (s : State C F) :
    (evaluateFuel 20 [.var .none 1] [.number 7] s).map Prod.fst = some (.err (.abort .typeError)) := rfl
example {C F : Type} (s : State C F) :
    (evaluateFuel 20 [.ifThenElse .none (.op .none (.blockOp (.cons 1)) [])
      (.op .none (.intOp (.const 7)) []) (.op .none (.intOp (.const 9)) [])] [] s).map Prod.fst =
      some (.val [.number 7]) := rfl
example {C F : Type} (s : State C F) :
    (evaluateFuel 20 [.handle .none (.raise .none (.op .none (.intOp (.const 7)) []))
      (.var .none 0)] [] s).map Prod.fst = some (.val [.number 7]) := rfl
example {C F : Type} (s : State C F) :
    (evaluateFuel 20 [.tick .none (.var .none 0)] [.number 7] { s with clock := 0 }).map Prod.fst =
      some (.err (.abort .timeoutError)) := rfl
example {C F : Type} (s : State C F) :
    (evaluateFuel 20 [.app .none none (.fn (ofString "f") none none 1 (.var .none 0))
      [.op .none (.intOp (.const 9)) []]] [] { s with clock := 2, maxApp := 2 }).map Prod.fst =
      some (.val [.number 9]) := rfl

end Flapjack.Test.ClosSemEvaluateParity
