import Flapjack.Translator.Monadic.MonadBase

namespace Flapjack.Translator.Monadic.MonadBase

/-- The getter returns HOL's list carrier; length succeeds and preserves the
entire input state. State, element, and exception types remain independent. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Marray_length_def"]
def arrayLength {state value exception : Type} (getArr : state → List value) :
    M state Nat exception :=
  fun s => (.success (getArr s).length, s)

/-- Flapjack infrastructure exposing the definition for arbitrary carriers;
there is no separate HOL theorem for this pointwise equation. -/
theorem arrayLength_apply {state value exception : Type}
    (getArr : state → List value) (s : state) :
    arrayLength (exception := exception) getArr s =
      (.success (getArr s).length, s) := rfl

end Flapjack.Translator.Monadic.MonadBase
