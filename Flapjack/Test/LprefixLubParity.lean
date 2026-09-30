import Flapjack.Misc.LprefixLub

/-!
# HOL `lprefix_lub` chain/equality lemma checks

Kernel-checked examples over small concrete prefix chains for the generic
`equiv_lprefix_chain` / `lprefix_rel` slice of `Flapjack/Misc/LprefixLub.lean`
(HOL `examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml`), together with
the `llist_shorter` relation from `Flapjack/Misc/LprefixLub.lean` and the tagged
`equiv_lprefix_chain_thm2`.
Bead `flapjack-pxn.18.5.2.22.3.2.1` / `flapjack-pxn.18.5.2.22.3.2.1.1`.
No direct HOL `EVAL` oracle is captured for the generic chain/LUB theorems
here (`equiv_lprefix_chain_thm2` and the `equiv_lprefix_chain`/`lprefix_rel`
family): they quantify over possibly infinite lazy lists, so there is no
finite closed input with a meaningful `EVAL` result; the examples below are
Lean-side kernel checks instead.  The `llist_shorter` relation itself does have
finite closed instances and is covered by a captured original-HOL probe
(`scripts/hol-probes/lprefix_lub_llist_shorter_probe.out`).
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

private theorem chainA_fin : ∀ ll, chainA ll → LFinite ll := by
  intro ll hl
  rcases hl with rfl | rfl
  · exact lfinite_fromList [0]
  · exact lfinite_fromList [0, 1, 2]

private theorem chainB_fin : ∀ ll, chainB ll → LFinite ll := by
  intro ll hl
  rcases hl with rfl | rfl
  · exact lfinite_fromList [0, 1]
  · exact lfinite_fromList [0, 1, 2]

-- `llist_shorter_fromList` on concrete finite lists.
example : llistShorter (fromList [0, 1]) (fromList [0, 1, 2]) :=
  (llistShorter_fromList _ _).2 (by decide)

-- `llist_shorter_lnth`: shorter means the longer list is defined wherever it is.
example : llistShorter (fromList [0]) (fromList [0, 1]) ↔
    ∀ n x, lnth n (fromList [0]) = some x →
      ∃ y, lnth n (fromList [0, 1]) = some y :=
  llistShorter_lnth

-- `lnth_some_down_closed`: a defined index transports downward.
example : ∃ y, lnth 1 (fromList [0, 1, 2]) = some y :=
  lnth_some_down_closed (ll := fromList [0, 1, 2]) (x := 2) (n1 := 2) (n2 := 1)
    (by rw [lnth_eq_rep]; simp [fromList, lcons]) (by decide)

-- `equiv_lprefix_chain_thm2` at the concrete chains: the equivalence is exactly
-- the `ls2`-covers-`ls1` conjunct together with the `llist_shorter` conjunct.
example : (equivLprefixChain chainA chainB ↔
    (∀ (ll1 : HolLList Nat) (n : Nat) (x : Nat), chainA ll1 → lnth n ll1 = some x →
      ∃ ll2, chainB ll2 ∧ lnth n ll2 = some x) ∧
    (∀ (ll2 : HolLList Nat) (_n : Nat) (_x : Nat), chainB ll2 → ll2 ≠ lnil →
      ∃ ll1, chainA ll1 ∧ llistShorter ll2 ll1)) :=
  equiv_lprefix_chain_thm2 chainA_chain chainB_chain chainB_fin

-- The `llist_shorter` conjunct extracted from a concrete `equiv_lprefix_chain`.
example : ∀ (ll2 : HolLList Nat) (_n : Nat) (_x : Nat), chainB ll2 → ll2 ≠ lnil →
    ∃ ll1, chainA ll1 ∧ llistShorter ll2 ll1 :=
  ((equiv_lprefix_chain_thm2 chainA_chain chainB_chain chainB_fin).mp
    (IMP_equiv_lprefix_chain chainA_chain chainB_chain relAB relBA)).2

-- Finite instances of `llist_shorter` from the captured original-HOL probe
-- `scripts/hol-probes/lprefix_lub_llist_shorter_probe.out` (rows
-- `llist_shorter_{shorter,equal_length,longer,two_empty,nil_nonempty,nonempty_nil}`).
example : llistShorter (fromList [1, 2]) (fromList [1, 2, 3]) := by
  rw [llistShorter_fromList]; decide
example : llistShorter (fromList [1, 2, 3]) (fromList [4, 5, 6]) := by
  rw [llistShorter_fromList]; decide
example : ¬ llistShorter (fromList [1, 2, 3]) (fromList [1, 2]) := by
  rw [llistShorter_fromList]; decide
example : llistShorter (fromList ([] : List Nat)) (fromList ([] : List Nat)) := by
  rw [llistShorter_fromList]; decide
example : llistShorter (fromList ([] : List Nat)) (fromList [1]) := by
  rw [llistShorter_fromList]; decide
example : ¬ llistShorter (fromList [1]) (fromList ([] : List Nat)) := by
  rw [llistShorter_fromList]; decide

def runChecks : IO Bool := do
  IO.println "PASS lprefix_lub chain/equality lemmas (equiv_lprefix_chain/lprefix_rel)"
  IO.println "PASS llist_shorter + equiv_lprefix_chain_thm2 (llistShorter/equiv_lprefix_chain_thm2)"
  IO.println "PASS llist_shorter finite instances replay lprefix_lub_llist_shorter_probe (6 rows)"
  pure true

end Flapjack.Test.LprefixLubParity
