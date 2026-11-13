module

public import Flapjack.SemanticPrimitivesProps.ResultMap
public import Flapjack.Compiler.Backend.Semantics.BviSem.State

@[expose] public section

namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.BviSem

/-- Mapping a handler result cannot produce an escaping return. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "call_SOME_handler_result"]
theorem callSome_handlerResult {α β γ τ : Type} (f : α → β) (g : γ → Flapjack.Compiler.Backend.BvlSem.Value)
    (r : Result α γ) (t : τ) :
    (match mapResult f (fun v => ExnOrRet.exn (g v)) r with
      | .val v => (Result.val v, t)
      | .err (.raise (.exn v)) => (Result.err (.raise (.exn v)), t)
      | .err (.raise (.ret _)) => (Result.err (.abort .typeError), t)
      | .err (.abort e) => (Result.err (.abort e), t)) =
    (mapResult f (fun v => ExnOrRet.exn (g v)) r, t) := by
  cases r with
  | val value => rfl
  | err error => cases error <;> rfl
end Flapjack.Compiler.Backend.BvlToBvi.Proofs
