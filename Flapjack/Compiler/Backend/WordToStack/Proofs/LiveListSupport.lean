import Flapjack.HolRef
import Lean.Elab.Tactic.Omega

namespace Flapjack.Compiler.Backend.WordToStack

/-- Full original prefix preservation under arbitrary list dropping. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "isPREFIX_DROP"]
theorem prefixDrop {α : Type} (s t : List α) (i : Nat) (h : s.IsPrefix t) :
    (s.drop i).IsPrefix (t.drop i) := by
  rw [List.prefix_iff_eq_take.mp h, List.drop_take]
  apply List.take_prefix

/-- Full original optional lookup offset law. HOL LLOOKUP is oEL, represented
by native getElem? including none outside the list. No total EL is used. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LLOOKUP_cons_SUC"]
theorem lookupConsSuc {α : Type} (h : α) (xs : List α) (m n : Nat) (hlt : m < n) :
    (h :: xs)[n - m]? = xs[n - (m + 1)]? := by
  have heq : n - m = (n - (m + 1)) + 1 := by omega
  rw [heq]
  simp

/-- Full original injectivity of halving on even natural registers. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "EVEN_DIV2_INJ"]
theorem evenDiv2Inj (x y : Nat) (hx : x % 2 = 0) (hy : y % 2 = 0)
    (hdiv : x / 2 = y / 2) : x = y := by omega

end Flapjack.Compiler.Backend.WordToStack
