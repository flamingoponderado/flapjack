module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.Wellformed
public import Flapjack.FiniteMap.AlistExact.Lookup

@[expose] public section

/-! Extension of direct-call compiler states and their auxiliary code. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack

/-- The new state extends the old sparse map and preserves each old lookup;
its auxiliary labels are distinct. Key, payload and sparse-map value types
remain independent as in HOL. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "subg_def"]
def stateExtends {A K V : Type} (g0 g1 : Spt A × List (K × V)) : Prop :=
  sptSubspt g0.1 g1.1 ∧
    (∀ key value, holALookup g0.2 key = some value →
      holALookup g1.2 key = some value) ∧
    (g1.2.map Prod.fst).Nodup

/-- A state with distinct labels extends itself. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "subg_refl"]
theorem stateExtends_refl {A K V : Type} (g : Spt A × List (K × V))
    (distinct : (g.2.map Prod.fst).Nodup) : stateExtends g g := by
  refine ⟨?_, ?_, distinct⟩
  · intro key member
    exact ⟨member, rfl⟩
  · intro _ _ h
    exact h

/-- Compiler-state extension is transitive. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "subg_trans"]
theorem stateExtends_trans {A K V : Type} (g1 g2 g3 : Spt A × List (K × V))
    (h12 : stateExtends g1 g2) (h23 : stateExtends g2 g3) : stateExtends g1 g3 := by
  refine ⟨?_, ?_, h23.2.2⟩
  · intro key member
    obtain ⟨middle, firstEq⟩ := h12.1 key member
    obtain ⟨last, secondEq⟩ := h23.1 key middle
    exact ⟨last, secondEq.trans firstEq⟩
  · intro key value lookup
    exact h23.2.1 key value (h12.2.1 key value lookup)

end Flapjack.Compiler.Backend.ClosCall
