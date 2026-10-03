import Flapjack.Misc.Sptree.Mapi

namespace Flapjack

/-- Original smart branch normalization preserves well-formed children. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "wf_mk_BN" 1832]
theorem sptWfMkBN {α : Type} (left right : Spt α)
    (valid : sptWf left = true ∧ sptWf right = true) :
    sptWf (sptMkBN left right) = true := by
  cases left <;> cases right <;> simp_all [sptMkBN, sptWf, sptIsEmpty]

/-- Original smart value-bearing branch normalization preserves well-formed
children, including the collapse to a singleton when both are empty. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "wf_mk_BS" 1838]
theorem sptWfMkBS {α : Type} (left right : Spt α) (value : α)
    (valid : sptWf left = true ∧ sptWf right = true) :
    sptWf (sptMkBS left value right) = true := by
  cases left <;> cases right <;> simp_all [sptMkBS, sptWf, sptIsEmpty]

/-- Arbitrary-index normalization used inside the original wf_mapi proof.
This induction helper has no separately declared HOL theorem. -/
theorem sptWfMapi0 {α β : Type} (f : Nat → α → β) (tree : Spt α) (index : Nat) :
    sptWf (sptMapi0 f index tree) = true := by
  induction tree generalizing index with
  | ln => rfl
  | ls value => rfl
  | bn left right ihLeft ihRight =>
      exact sptWfMkBN _ _ ⟨ihLeft _, ihRight _⟩
  | bs left value right ihLeft ihRight =>
      exact sptWfMkBS _ _ _ ⟨ihLeft _, ihRight _⟩

/-- Original unconditional indexed-map normalization. No input
well-formedness premise is added: malformed raw nodes are normalized too. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "wf_mapi"]
theorem sptWfMapi {α β : Type} (f : Nat → α → β) (tree : Spt α) :
    sptWf (sptMapi f tree) = true := sptWfMapi0 f tree 0

end Flapjack
