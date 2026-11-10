module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.SourceChain
public import Flapjack.FiniteMap.AlistExact
@[expose] public section

/-! Installation of generated source expression chains. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosSem

/-- The generated expression chain is installed in its association-list code map. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "chain_installed_chain_exps"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.alistToFmap])]
theorem chainInstalled_chainExps (start : Nat) (es : List ClosLang.Exp) :
    chainInstalled start es (HolFiniteMapExact.alistToFmap (chainExps start es)) := by
  induction es generalizing start with
  | nil => simp [chainInstalled]
  | cons first rest ih =>
    cases rest with
    | nil =>
      apply (chainInstalled_cons start first [] _).2
      constructor
      · have lookup := HolFiniteMapExact.lookup_alistToFmap_head (start, 0, first) []
        simp [chainExps, findCode, lookup]
      · simp [chainInstalled]
    | cons second tail =>
      let head : Nat × Nat × ClosLang.Exp :=
        (start, 0, .let .none [first] (.call .none 0 (start + 1) []))
      let remaining := chainExps (start + 1) (second :: tail)
      have heq : chainExps start (first :: second :: tail) = head :: remaining := rfl
      rw [heq]
      apply (chainInstalled_cons start first (second :: tail) _).2
      constructor
      · have lookup := HolFiniteMapExact.lookup_alistToFmap_head head remaining
        simp [findCode, head, lookup]
      · intro i bound
        have previous := ih (start + 1) i bound
        have neq : start + 1 + i ≠ head.1 := by simp [head]; omega
        have same := HolFiniteMapExact.lookup_alistToFmap_tail head remaining (start + 1 + i) neq
        unfold findCode at previous ⊢
        rw [same]
        exact previous
end Flapjack.Compiler.Backend.ClosToBvl
