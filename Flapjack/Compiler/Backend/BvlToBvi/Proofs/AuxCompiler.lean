module

public import Flapjack.Compiler.Backend.BvlToBvi.Compile
public import Flapjack.Compiler.Backend.BvlToBvi.SourceSing
public import Flapjack.Compiler.Backend.BviLet.Proofs.SourceAgreement

@[expose] public section

/-! Agreement of auxiliary-code generation with the total let optimizer. -/
namespace Flapjack.Compiler.Backend.BvlToBvi

/-- The executed auxiliary-code generator always emits the source-shaped
optimized body. This is Flapjack infrastructure: the HOL definition returns
a SmartAppend tree, while the executable returns its flattened list. -/
theorem compileAuxFuel_eq_source (fuel k args : Nat) (body : Bvi.Exp) :
    compileAuxFuel fuel k args body =
      some [(bvlNumStubs + bvlToBviNamespaces * k + 1, args,
        BviLet.compileSing [] 0 body)] := by
  simp [compileAuxFuel, BviLet.compileExp_eq]

/-- The executed auxiliary list is precisely the flattening of the
source-shaped auxiliary tree, for every optimizer fuel. -/
theorem compileAuxFuel_eq_flattened (fuel k args : Nat) (body : Bvi.Exp) :
    compileAuxFuel fuel k args body =
      some (appListAppend (compileAuxSource (k, args, body))) := by
  simp [compileAuxFuel_eq_source, compileAuxSource, appListAppend, appendAux]

end Flapjack.Compiler.Backend.BvlToBvi
