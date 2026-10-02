import Flapjack.Pancake.WordLang
import Flapjack.Basis.Pure.MlString
namespace Flapjack.Compiler.Backend.WordToStack
open Flapjack.Basis.Pure.MlString
/-- Original ordered WordToStack runtime symbols at the reviewed WordLang labels.
Native mlstring characters retain the original bytes; production formatting is
tracked separately. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "stub_names_def"]
def stubNames (_ : Unit) : List (Nat × MlString) :=
  [(Flapjack.raiseStubLocation, .implode [95,82,97,105,115,101]),
   (Flapjack.storeConstsStubLocation, .implode [95,83,116,111,114,101,67,111,110,115,116,115])]
end Flapjack.Compiler.Backend.WordToStack
