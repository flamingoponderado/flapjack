module

public import Flapjack.HOL.Unification.UnifDef
public import Flapjack.FiniteMap.MapKeys

@[expose] public section

namespace Flapjack.HOL.Unification

/-- The canonical tuple viewed through the finite-support-preserving map codec. -/
def uRTupleToBroad {α : Type}
    (p : HolFiniteMapExact Nat (Term α) × Term α × Term α) :
    FiniteMapBroad Nat (Term α) × Term α × Term α :=
  (FiniteMapBroad.toBroad p.1, p.2.1, p.2.2)

/-- Reconstruct the canonical tuple from its finite-support-preserving view. -/
def uRTupleOfBroad {α : Type}
    (p : FiniteMapBroad Nat (Term α) × Term α × Term α) :
    HolFiniteMapExact Nat (Term α) × Term α × Term α :=
  (FiniteMapBroad.ofBroad p.1, p.2.1, p.2.2)

/-- The tuple codec preserves the complete canonical map and both terms. -/
theorem holFmapAsFiniteSupportTupleWitness_uRWellFounded {α : Type}
    (p : HolFiniteMapExact Nat (Term α) × Term α × Term α) :
    uRTupleOfBroad (uRTupleToBroad p) = p := by
  rcases p with ⟨⟨lookup, support⟩, left, right⟩
  rfl

/-- The tuple codec also reconstructs every finite-support-preserving view. -/
theorem holFmapAsFiniteSupportTupleWitness_uRWellFounded_reverse {α : Type}
    (p : FiniteMapBroad Nat (Term α) × Term α × Term α) :
    uRTupleToBroad (uRTupleOfBroad p) = p := by
  rcases p with ⟨⟨lookup, support⟩, left, right⟩
  rfl

/-- The unification relation is well founded on its tuple model. This proof is
    untagged while the representation of finite maps inside tuple-valued
    relation arguments has no reviewed qualifier. -/
theorem uRWellFounded {α : Type} : WellFounded (@uR α) := by
  classical
  let rank : (HolFiniteMapExact Nat (Term α) × Term α × Term α) → Nat × Nat :=
    fun p => ((Set.diff (allVars p.1 p.2.1 p.2.2) p.1.domain).ncard,
      pairCount (walkstar p.1 p.2.1))
  apply Subrelation.wf _ (InvImage.wf rank (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf)
  intro child parent edge
  rcases child with ⟨sx, c1, c2⟩
  rcases parent with ⟨s, t1, t2⟩
  change wfs sx ∧ s.submap sx ∧
    Set.Subset (allVars sx c1 c2) (allVars s t1 t2) ∧
    pairCount (walkstar sx c1) < pairCount (walkstar sx t1) at edge
  have domainSub : Set.Subset s.domain sx.domain := by
      intro k present
      change s.lookup k ≠ none at present
      change sx.lookup k ≠ none
      cases found : s.lookup k with
      | none => exact (present found).elim
      | some value => rw [edge.2.1 k value found]; simp
  have contained : Set.Subset (Set.diff (allVars sx c1 c2) sx.domain)
      (Set.diff (allVars s t1 t2) s.domain) := by
    intro k hk
    exact ⟨edge.2.2.1 hk.1, fun old => hk.2 (domainSub old)⟩
  have finiteParent : (Set.diff (allVars s t1 t2) s.domain).Finite :=
    (finiteAllVars s t1 t2).subset (fun _ h => h.1)
  change Prod.Lex (· < ·) (· < ·) (rank (sx, c1, c2)) (rank (s, t1, t2))
  by_cases equal : sx = s
  · subst sx
    rcases lt_or_eq_of_le (Set.ncard_le_ncard contained finiteParent) with smaller | sizes
    · apply Prod.Lex.left
      exact smaller
    · change Prod.Lex (· < ·) (· < ·)
        ((Set.diff (allVars s c1 c2) s.domain).ncard, pairCount (walkstar s c1))
        ((Set.diff (allVars s t1 t2) s.domain).ncard, pairCount (walkstar s t1))
      rw [sizes]
      exact Prod.Lex.right _ edge.2.2.2
  · have newKey : ∃ k, k ∈ sx.domain ∧ k ∉ s.domain := by
      by_contra missing
      apply equal
      apply HolFiniteMapExact.ext_lookup
      intro k
      cases old : s.lookup k with
      | some value => exact edge.2.1 k value old
      | none =>
        cases new : sx.lookup k with
        | none => rfl
        | some value =>
          have memNew : k ∈ sx.domain := by change sx.lookup k ≠ none; rw [new]; simp
          have notOld : k ∉ s.domain := by change ¬ (s.lookup k ≠ none); simp [old]
          exact (missing ⟨k, memNew, notOld⟩).elim
    have decrease : Set.diff (allVars sx c1 c2) sx.domain ⊂
        Set.diff (allVars s t1 t2) s.domain := by
      refine ⟨contained, ?_⟩
      obtain ⟨k, memNew, notOld⟩ := newKey
      intro reverse
      have inChild : allVars sx c1 c2 k := Or.inr (Or.inl memNew)
      have inParent := edge.2.2.1 inChild
      exact (reverse ⟨inParent, notOld⟩).2 memNew
    apply Prod.Lex.left
    exact Set.ncard_lt_ncard decrease finiteParent

end Flapjack.HOL.Unification
