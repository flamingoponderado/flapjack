module

public import Flapjack.Compiler.Backend.Semantics.BviSem.State
public import Flapjack.Misc.ListEl
public import Flapjack.HolRef

@[expose] public section

/-!
# List lemmas of HOL `bviProps`

Counterpart of `cakeml/compiler/backend/semantics/bviPropsScript.sml:646-665`:
`take_drop_lem`, the BVI twin of the `bvlProps` list lemma.
-/

namespace Flapjack.Compiler.Backend.BviProps

/-- A dropped prefix splits into its head and the rest of the drop. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "take_drop_lem"
  (total_function_inhabitants := [α])]
theorem takeDropLem {α : Type} [Nonempty α] (skip : Nat) (env : List α) (n : Nat)
    (bounds : skip < env.length ∧ skip + (n + 1) ≤ env.length ∧ env.drop skip ≠ []) :
    Flapjack.holEl skip env :: (env.drop (1 + skip)).take n =
      (env.drop skip).take (n + 1) := by
  obtain ⟨short, _long, _nonempty⟩ := bounds
  rw [Flapjack.holEl_eq_getElem skip env short]
  rw [List.drop_eq_getElem_cons short, List.take_succ_cons]
  congr 1
  rw [Nat.add_comm]

end Flapjack.Compiler.Backend.BviProps
