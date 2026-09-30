import Flapjack.Misc.LprefixLub

/-!
# HOL `lprefix_lub` chain/equality lemma checks

Kernel-checked examples over small concrete prefix chains for the generic
`equiv_lprefix_chain` / `lprefix_rel` slice of `Flapjack/Misc/LprefixLub.lean`
(HOL `examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml`).
Bead `flapjack-pxn.18.5.2.22.3.2.1`.
-/

namespace Flapjack.Test.LprefixLubParity

open Flapjack Flapjack.HolLList

/-- `{[0], [0,1,2]}`, a two-element prefix chain. -/
private def chainA : HolLList Nat → Prop :=
  fun l => l = fromList [0] ∨ l = fromList [0, 1, 2]

/-- `{[0,1], [0,1,2]}`, a chain sharing its top with `chainA`. -/
private def chainB : HolLList Nat → Prop :=
  fun l => l = fromList [0, 1] ∨ l = fromList [0, 1, 2]

private theorem chainA_chain : lprefixChain chainA := by
  intro a b ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact Or.inl (lprefix_refl _)
  · exact Or.inl ((lprefix_fromList _ _).2 ⟨[1, 2], rfl⟩)
  · exact Or.inr ((lprefix_fromList _ _).2 ⟨[1, 2], rfl⟩)
  · exact Or.inl (lprefix_refl _)

private theorem chainB_chain : lprefixChain chainB := by
  intro a b ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact Or.inl (lprefix_refl _)
  · exact Or.inl ((lprefix_fromList _ _).2 ⟨[2], rfl⟩)
  · exact Or.inr ((lprefix_fromList _ _).2 ⟨[2], rfl⟩)
  · exact Or.inl (lprefix_refl _)

private theorem relAB : lprefixRel chainA chainB := by
  intro l hl
  rcases hl with rfl | rfl
  · exact ⟨fromList [0, 1], Or.inl rfl, (lprefix_fromList _ _).2 ⟨[1], rfl⟩⟩
  · exact ⟨fromList [0, 1, 2], Or.inr rfl, lprefix_refl _⟩

private theorem relBA : lprefixRel chainB chainA := by
  intro l hl
  rcases hl with rfl | rfl
  · exact ⟨fromList [0, 1, 2], Or.inr rfl, (lprefix_fromList _ _).2 ⟨[2], rfl⟩⟩
  · exact ⟨fromList [0, 1, 2], Or.inr rfl, lprefix_refl _⟩

-- `IMP_build_lprefix_lub_EQ`: the two chains have the same `build_lprefix_lub`.
example : buildLprefixLub chainA = buildLprefixLub chainB :=
  IMP_build_lprefix_lub_EQ chainA_chain chainB_chain relAB relBA

-- `lprefix_lub_is_chain`: any `lprefix_lub` witness forces a chain.
example : lprefixChain chainA :=
  lprefix_lub_is_chain (buildLprefixLub_thm chainA_chain)

-- `IMP_equiv_lprefix_chain`: mutual `lprefix_rel` gives `equiv_lprefix_chain`.
example : equivLprefixChain chainA chainB :=
  IMP_equiv_lprefix_chain chainA_chain chainB_chain relAB relBA

-- `lprefix_rel_lnth`: pointwise membership transport along `lprefix_rel`.
example : ∀ ll n x, chainA ll → lnth n ll = some x →
    ∃ ll', chainB ll' ∧ lnth n ll' = some x :=
  lprefix_rel_lnth relAB

def runChecks : IO Bool := do
  IO.println "PASS lprefix_lub chain/equality lemmas (equiv_lprefix_chain/lprefix_rel)"
  pure true

end Flapjack.Test.LprefixLubParity
