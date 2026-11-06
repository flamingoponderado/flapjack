import Flapjack.Compiler.Backend.ClosKnown.Proofs.InlineTotal
import Flapjack.Compiler.Backend.ClosKnown.Proofs.InlineDecrease
import Flapjack.Compiler.Backend.ClosKnown.Proofs.MergeTotal
import Flapjack.Compiler.Backend.ClosOp.Proofs.SmartTotal
import Flapjack.Compiler.Backend.ClosFvs.Proofs.Total
import Flapjack.Compiler.Backend.ClosTicks.Proofs.Total
import Flapjack.Compiler.Backend.ClosLetop.Proofs.Total

/-! Structural totality of the executable known-closure traversal when
inlining is disabled. This is not a HOL correctness theorem. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang

/-- The total production traversal succeeds for every inline factor. This is
Flapjack infrastructure, not a separate HOL theorem. -/
theorem knownListBounded_succeeds (fuel : Nat) (c : Config) (xs : List Exp)
    (env : List ValApprox) (globals : Spt ValApprox) :
    ∃ result, knownListBounded fuel c xs env globals = some result :=
  ⟨knownListTotal c xs env globals, rfl⟩

/-- The complete checked known-closure pass succeeds at every inline factor.
This is Flapjack infrastructure, not the HOL pass-correctness theorem. -/
theorem compileFuel_succeeds (fuel : Nat) (c : Config) (es : List Exp) :
    ∃ result, compileFuel fuel (some c) es = some result := by
  obtain ⟨prepared, hp⟩ := mapM_succeeds es (ClosFvs.removeBounded fuel 0) (by
    intro e _; exact ClosFvs.removeBounded_succeeds fuel 0 e)
  obtain ⟨⟨known, globals⟩, hk⟩ := knownListBounded_succeeds fuel c prepared [] .ln
  obtain ⟨finished, hf⟩ := mapM_succeeds known (fun p => do
    let e ← ClosTicks.removeBounded fuel p.1
    ClosLetop.compileBounded fuel e) (by
      intro p _
      obtain ⟨e, a⟩ := p
      obtain ⟨unticked, hu⟩ := ClosTicks.removeBounded_succeeds fuel e
      obtain ⟨result, hr⟩ := ClosLetop.compileBounded_succeeds fuel unticked
      exact ⟨result, by simp [hu, hr]⟩)
  change known.mapM (fun p => (ClosTicks.removeBounded fuel p.1).bind
    (ClosLetop.compileBounded fuel)) = some finished at hf
  exact ⟨(some { c with valApproxSpt := globals }, finished), by
    simp [compileFuel, hp, hk, hf]⟩

end Flapjack.Compiler.Backend.ClosKnown
