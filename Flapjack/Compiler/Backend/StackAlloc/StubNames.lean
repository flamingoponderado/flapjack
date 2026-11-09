module

public import Flapjack.Compiler.Backend.StackLang.Overloads
public import Flapjack.Basis.Pure.MlString

@[expose] public section
namespace Flapjack.Compiler.Backend.StackAlloc
open Flapjack.Basis.Pure.MlString
/-- Original GC runtime symbol at the reviewed StackLang stub location.
Native mlstring characters retain the original bytes; production formatting is
tracked separately. -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "stub_names_def"]
def stubNames (_ : Unit) : List (Nat × MlString) :=
  [(Flapjack.Compiler.Backend.StackLang.gcStubLocation, .implode [95,71,67])]
end Flapjack.Compiler.Backend.StackAlloc
