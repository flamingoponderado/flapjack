module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.LabelDistinct
public import Flapjack.Compiler.Backend.ClosCall.Proofs.TotalCorrespondence
public import Flapjack.Compiler.Backend.ClosCall.Compile

@[expose] public section

/-! Original direct-call code-location invariants. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang ClosProps

/-- Every emitted auxiliary label is old or the successor of an input
closure location. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_add_SUC_code_locs"]
theorem calls_addSucc_codeLocations (xs : List Exp) (initial : State) (ys : List Exp)
    (final : State) (run : calls xs initial = (ys, final)) :
    {x | x ∈ final.2.map Prod.fst} ⊆
      {x | x ∈ initial.2.map Prod.fst} ∪ Nat.succ '' {x | x ∈ codeLocations xs} := by
  have bounded := callsListBounded_correct 0 xs initial
  change callsSingList xs initial = (ys, final) at run
  rw [run] at bounded
  have bound := callsListBounded_labelsBound 0 xs initial final ys bounded
  intro label member
  rcases bound label member with old | ⟨loc, inLocations, eq⟩
  · exact Or.inl old
  · exact Or.inr ⟨loc, inLocations, by simpa [Nat.succ_eq_add_one] using eq.symm⟩

/-- Direct-call conversion preserves distinctness of auxiliary labels under
the source location and disjointness conditions. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_ALL_DISTINCT"]
theorem calls_allDistinct (xs : List Exp) (initial : State) (ys : List Exp)
    (final : State) (h : calls xs initial = (ys, final) ∧
      (initial.2.map Prod.fst).Nodup ∧ (codeLocations xs).Nodup ∧
      (∀ label, ¬ (label ∈ Nat.succ '' {x | x ∈ codeLocations xs} ∧
        label ∈ initial.2.map Prod.fst))) :
    (final.2.map Prod.fst).Nodup := by
  have bounded := callsListBounded_correct 0 xs initial
  have run : callsSingList xs initial = (ys, final) := h.1
  rw [run] at bounded
  apply callsListBounded_labelsDistinct 0 xs initial final ys bounded h.2.2.1 ?_ h.2.1
  intro loc locMem labelMem
  apply h.2.2.2 (Nat.succ loc)
  exact ⟨⟨loc, locMem, rfl⟩, by simpa [Nat.succ_eq_add_one] using labelMem⟩

end Flapjack.Compiler.Backend.ClosCall
