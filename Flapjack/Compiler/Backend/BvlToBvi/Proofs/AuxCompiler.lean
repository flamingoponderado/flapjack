import Flapjack.Compiler.Backend.BvlToBvi.Compile
import Flapjack.Compiler.Backend.BviLet.Proofs.SourceAgreement

/-! Agreement of auxiliary-code generation with the total let optimizer. -/
namespace Flapjack.Compiler.Backend.BvlToBvi

/-- The executed auxiliary-code generator always emits the source-shaped
optimized body. This is Flapjack infrastructure: the HOL definition returns
a SmartAppend tree, while the executable returns its flattened list. -/
theorem compileAuxFuel_eq_source (fuel k args : Nat) (body : Bvi.Exp) :
    compileAuxFuel fuel k args body =
      some [(bvlNumStubs + bvlToBviNamespaces * k + 1, args,
        BviLet.compileSing [] 0 body)] := by
  simp [compileAuxFuel, BviLet.compileBounded_eq_compileSing]

/-- Once expression conversion returns, the production function entry uses
the same total let optimizer, independently of its optimizer fuel. The
expression-conversion correspondence remains a separate obligation. -/
theorem compileSingleFuel_eq_source (fuel optFuel n name args : Nat) (body : Bvl.Exp)
    (converted : Bvi.Exp) (aux : List (Nat × Nat × Bvi.Exp)) (next : Nat)
    (run : compileBounded fuel optFuel n body = some (converted, aux, next)) :
    compileSingleFuel fuel optFuel n (name, args, body) =
      some ((bvlNumStubs + bvlToBviNamespaces * name, args,
        BviLet.compileSing [] 0 converted) :: aux, next) := by
  simp [compileSingleFuel, run, BviLet.compileBounded_eq_compileSing]

end Flapjack.Compiler.Backend.BvlToBvi
