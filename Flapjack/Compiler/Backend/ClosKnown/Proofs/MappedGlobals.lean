module

public import Flapjack.Compiler.Backend.Semantics.ClosSem
public import Mathlib.Data.Set.Basic

@[expose] public section

/-! Initialization and controlled extension of closure globals. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosSem

/-- Indices whose global slots contain initialized values. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "mapped_globals_def"]
def mappedGlobals {α : Type} (globals : List (Option α)) : Set Nat :=
  { i | ∃ value, getGlobal i globals = some (some value) }

/-- Initialized slots outside the permitted set retain their previous values. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "mglobals_extend_def"]
def mglobalsExtend {α : Type} (before : List (Option α)) (allowed : Set Nat)
    (after : List (Option α)) : Prop :=
  mappedGlobals after ⊆ mappedGlobals before ∪ allowed ∧
    ∀ k value, getGlobal k after = some (some value) ∧ k ∉ allowed →
      getGlobal k before = some (some value)

/-- Any global list extends itself for an arbitrary set of permitted writes. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "mglobals_extend_refl"]
theorem mglobalsExtendRefl {α : Type} (s : List (Option α)) (allowed : Set Nat) :
    mglobalsExtend s allowed s := by
  constructor
  · intro k hk; exact Or.inl hk
  · intro k value h; exact h.1

/-- Composing extensions permits the union of the two write sets. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "mglobals_extend_trans"]
theorem mglobalsExtendTrans {α : Type} (s0 s1 s2 : List (Option α)) (g1 g2 : Set Nat)
    (h : mglobalsExtend s0 g1 s1 ∧ mglobalsExtend s1 g2 s2) :
    mglobalsExtend s0 (g1 ∪ g2) s2 := by
  rcases h with ⟨⟨sub1, preserve1⟩, ⟨sub2, preserve2⟩⟩
  constructor
  · intro k hk
    rcases sub2 hk with old | added
    · rcases sub1 old with old | added
      · exact Or.inl old
      · exact Or.inr (Or.inl added)
    · exact Or.inr (Or.inr added)
  · intro k value ⟨lookup, outside⟩
    have out1 : k ∉ g1 := fun member => outside (Or.inl member)
    have out2 : k ∉ g2 := fun member => outside (Or.inr member)
    exact preserve1 k value ⟨preserve2 k value ⟨lookup, out2⟩, out1⟩

/-- Enlarging the permitted write set preserves an extension relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "mglobals_extend_SUBSET"]
theorem mglobalsExtendSubset {α : Type} (s0 s : List (Option α)) (g1 g2 : Set Nat)
    (h : mglobalsExtend s0 g1 s ∧ g1 ⊆ g2) : mglobalsExtend s0 g2 s := by
  rcases h with ⟨⟨subset, preserve⟩, inclusion⟩
  constructor
  · intro k member
    rcases subset member with old | allowed
    · exact Or.inl old
    · exact Or.inr (inclusion allowed)
  · intro k value ⟨lookup, outside⟩
    exact preserve k value ⟨lookup, fun allowed => outside (inclusion allowed)⟩

end Flapjack.Compiler.Backend.ClosKnown
