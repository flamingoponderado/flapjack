module

public import Flapjack.Compiler.Backend.Arm8Config.Names
public import Flapjack.Compiler.Backend.StackNames.OperandNames

@[expose] public section

/-!
# `findNameSpt` at `arm8Names`

`StackNames.findNameSpt arm8Names` is the explicit register map `arm8NameMap`.
This lives beside `Arm8Config.Names` rather than inside it because `Names.lean`
is a `module` file and `StackNames.OperandNames` is not; the lemma is proof-side
infrastructure shared by the closed-model and L3 `backend_config_ok` proofs.
-/

namespace Flapjack.Compiler.Backend.Arm8Config

open Flapjack

/-- `findNameSpt` of `arm8Names` is the explicit map `arm8NameMap`. -/
theorem findNameSpt_arm8Names :
    StackNames.findNameSpt arm8Names = arm8NameMap :=
  funext arm8Names_lookup_eq

end Flapjack.Compiler.Backend.Arm8Config
