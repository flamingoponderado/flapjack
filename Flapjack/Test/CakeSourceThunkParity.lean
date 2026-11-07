import Flapjack.SemanticPrimitivesHOL.Thunk

/-! Source thunk observations captured from pinned HOL. -/
namespace Flapjack.Test.CakeSourceThunkParity
open Flapjack.SemanticPrimitivesHOL

private def intV (n : Int) : Value := .litv (.intLit n)
private def initial : Store Value := [.thunk .notEvaluated (intV 1)]
private def ffi : Flapjack.HolFfiState Nat :=
  { oracle := fun _ state _ bytes => .ret state bytes, ffiState := 7, ioEvents := [] }

#guard match destThunk [.loc false 0] initial with
  | .isThunk .notEvaluated (.litv (.intLit 1)) => true
  | _ => false
#guard match destThunk [.loc true 0] initial with
  | .badRef => true
  | _ => false
#guard match destThunk [.loc true 0] [.refv (intV 1)] with
  | .notThunk => true
  | _ => false
#guard match updateThunk [.loc false 0] initial [intV 2] with
  | some [.thunk .evaluated (.litv (.intLit 2))] => true
  | _ => false
#guard (updateThunk [.loc false 0] (initial ++ [.thunk .evaluated (intV 2)]) [.loc false 1]).isNone
#guard match (thunkOp (initial, ffi) (.updateThunk .evaluated) [.loc false 0, intV 2] :
    Option (StoreFfi Value Nat × Result Value Bool)) with
  | some (([.thunk .evaluated (.litv (.intLit 2))], outFfi), .val (.conv none [])) => outFfi.ffiState == 7
  | _ => false
#guard xorBytes [3] [5, 7] = some [6, 7]
#guard (xorBytes [3, 7] [5]).isNone

-- The HOL result error payload and FFI carrier are independent type variables.
example (state : StoreFfi Value Nat) : Option (StoreFfi Value Nat × Result Value Bool) :=
  thunkOp state (.allocThunk .notEvaluated) [intV 1]

end Flapjack.Test.CakeSourceThunkParity
