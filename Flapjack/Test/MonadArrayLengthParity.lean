import Flapjack.Translator.Monadic.MonadBase.ArrayLength

namespace Flapjack.Test.MonadArrayLengthParity
open Flapjack.Translator.Monadic.MonadBase
/-! Same-input original HOL equations replayed in the kernel. These finite
observations do not prove cross-assistant equivalence or production routing. -/
-- al_empty=T
example : arrayLength (exception := Bool) (fun (_ : Nat) => ([] : List Nat)) 42 =
    (.success 0, 42) := by decide +kernel
-- al_duplicates=T
example : arrayLength (exception := Bool) (fun (s : Nat) => [s,s,s]) 7 =
    (.success 3, 7) := by decide +kernel
-- al_bool_state=T
example : arrayLength (exception := Nat)
    (fun (s : Bool) => if s then [2,3] else ([] : List Nat)) true =
    (.success 2, true) := by decide +kernel
-- al_list_state=T
example : arrayLength (exception := Bool) (fun (s : List Nat) => s) [2,3,5] =
    (.success 3, [2,3,5]) := by decide +kernel
-- al_bool_values=T
example : arrayLength (exception := List Nat) (fun (_ : Nat) => [true,false,true])
    18446744073709551616 = (.success 3, 18446744073709551616) := by decide +kernel

example {state value exception : Type} (getArr : state → List value) (s : state) :
    arrayLength (exception := exception) getArr s =
      (.success (getArr s).length, s) := rfl
end Flapjack.Test.MonadArrayLengthParity
