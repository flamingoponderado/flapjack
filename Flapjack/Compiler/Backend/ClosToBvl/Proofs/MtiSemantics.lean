module

public import Flapjack.Compiler.Backend.ClosMti.Proofs.Semantics
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.MtiInvariants
@[expose] public section

/-! Observable semantics for conditional closure preprocessing. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosLang ClosProps BackendProps ClosSem

/-- Conditional multi-argument introduction preserves the original observable semantics. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "semantics_cond_mti_compile_inc"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem semantics_condMtiCompileInc {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (co : CompileOracle C) (doMti : Bool) (cc : Compiler C) (xs : List ClosLang.Exp)
    (premises : semantics ffi maxApp HolFiniteMapExact.holEmpty co
      (pureCc (ClosMti.condCompileInc doMti maxApp) cc) xs ≠ .fail ∧
      (doMti → (∀ n, (co n).2.2 = [] ∧ ∀ e ∈ (co n).2.1, noMti e) ∧
        1 ≤ maxApp ∧ ∀ e ∈ xs, noMti e)) :
    semantics ffi maxApp HolFiniteMapExact.holEmpty
      (pureCo (ClosMti.condCompileInc doMti maxApp) ∘ co) cc
      (ClosMti.compile doMti maxApp xs) =
    semantics ffi maxApp HolFiniteMapExact.holEmpty co
      (pureCc (ClosMti.condCompileInc doMti maxApp) cc) xs := by
  apply ClosMti.semantics_compile ffi maxApp co _ xs doMti cc _
  refine ⟨premises.1, ?_, ?_, premises.2⟩
  · cases doMti <;> rfl
  · cases doMti <;> rfl
end Flapjack.Compiler.Backend.ClosToBvl
