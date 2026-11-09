import Flapjack.Compiler.Backend.BvlHandle.Proofs.HandleOk
import Flapjack.Compiler.Backend.BvlToBvi.Config

/-! Code-name and oracle invariants for the BVL-to-BVI state relation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlHandle.Proofs (handleOk)

/-- Source-shaped code-name and oracle invariant. Both sparse-tree payloads
and the oracle's two program-label payload types are independent. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "names_ok_def"]
def namesOk {C α β δ ε : Type} (source : Spt α) (target : Spt β)
    (oracle : Nat → (Nat × C) × List (δ × ε × Bvl.Exp)) : Prop :=
  (∀ n config prog, oracle n = (config, prog) →
    ∀ name arity exp, (name, arity, exp) ∈ prog → handleOk [exp]) ∧
  let next := (oracle 0).1.1
  ∀ n, sptMem n target ∧ Flapjack.bvlNumStubs ≤ n →
    if n % Flapjack.bvlToBviNamespaces = 1 then
      n < Flapjack.bvlNumStubs + Flapjack.bvlToBviNamespaces * next
    else n % Flapjack.bvlToBviNamespaces = 0 ∧
      sptMem ((n - Flapjack.bvlNumStubs) / Flapjack.bvlToBviNamespaces) source

/-- Every program supplied by a related oracle satisfies the handler invariant. -/
theorem namesOk_oracle {C α β δ ε : Type} (source : Spt α) (target : Spt β)
    (oracle : Nat → (Nat × C) × List (δ × ε × Bvl.Exp))
    (ok : namesOk source target oracle) (n : Nat) (name : δ) (arity : ε)
    (exp : Bvl.Exp) (member : (name, arity, exp) ∈ (oracle n).2) : handleOk [exp] :=
  ok.1 n (oracle n).1 (oracle n).2 (Prod.eta (oracle n)).symm name arity exp member

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
