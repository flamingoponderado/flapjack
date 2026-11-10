module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.FreeCorrect
public import Flapjack.Compiler.Backend.ClosCall.Proofs.Length

@[expose] public section

/-! Closedness of mutually recursive groups in the executed direct-call pass. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang ClosProps

/-- The fold used by direct-call conversion to decide whether every
transformed recursive body is closed with respect to its arguments. -/
def groupClosedFuel (fuel : Nat) (fns : List (Nat × Exp)) (bodies : List Exp) : Option Bool :=
  (fns.zip bodies).foldlM (fun all pair => do
    if !all then pure false else
      closedFuel fuel (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none pair.1.1 pair.2)) true

end Flapjack.Compiler.Backend.ClosCall
