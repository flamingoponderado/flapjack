module

public import Flapjack.Compiler.Backend.BvlToBvi.Compile
public import Flapjack.Compiler.Backend.BvlToBvi.SourceSing
public import Flapjack.Compiler.Backend.BviLet.Proofs.SourceAgreement

@[expose] public section

/-! Agreement of auxiliary-code generation with the total let optimizer. -/
namespace Flapjack.Compiler.Backend.BvlToBvi

/-- The executed auxiliary list is precisely the flattening of the
source-shaped auxiliary tree, for every optimizer fuel. -/
theorem compileAuxFuel_eq_flattened (fuel k args : Nat) (body : Bvi.Exp) :
    compileAuxFuel fuel k args body =
      some (appListAppend (compileAuxSource (k, args, body))) := by
  simp [compileAuxFuel, BviLet.compileExp_eq, compileAuxSource, appListAppend, appendAux]

end Flapjack.Compiler.Backend.BvlToBvi
