module

public import Flapjack.Compiler.Backend.ClosInterp.Proofs.AttachSemantics
public import Flapjack.FiniteMap.EmptyExact

@[expose] public section


/-! Source-shaped interpreter attachment observation. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.Compiler.Backend.BackendProps

/-- Attaching the interpreter preserves closure behavior with the original
oracle and compiler transformation. `insertProgram` is insertion on the
first component paired with the identity on the auxiliary code. -/
@[hol "cakeml/compiler/backend/proofs/clos_interpProofScript.sml" "semantics_attach_interpreter"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem attachInterpreter_semantics_source {C F : Type} (expressions : List ClosLang.Exp)
    (ffi : HolFfiState F) (maxApp : Nat) (oracle : ClosSem.CompileOracle C)
    (compiler : ClosSem.Compiler C)
    (sourceNoFail : ClosSem.semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
      (pureCc insertProgram compiler) (attachInterpreter expressions) ≠ .fail)
    (assumptions : (∀ index, (oracle index).2.2 = []) ∧ 0 < maxApp) :
    ClosSem.semantics ffi maxApp HolFiniteMapExact.holEmpty (pureCo insertProgram ∘ oracle)
      compiler (attachInterpreter expressions) =
    ClosSem.semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
      (pureCc insertProgram compiler) (attachInterpreter expressions) :=
  attachInterpreter_semantics expressions ffi maxApp oracle compiler sourceNoFail assumptions

end Flapjack.Compiler.Backend.ClosInterp
