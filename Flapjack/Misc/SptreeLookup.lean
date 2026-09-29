import Flapjack.Misc.Sptree
import Flapjack.Pancake.Semantics.LoopProps.UnassignedVarsExact

/-!
# sptree `delete` / `list_delete` lookup lemmas

Flapjack infrastructure (no CakeML declarations): the HOL `sptree` library facts
`lookup_delete` and the `list_delete` lookup characterisation, over the exact
`Spt` carrier.
-/

namespace Flapjack

/-- HOL `sptree$lookup_delete` (HOL/src sptree library; no CakeML tag). -/
theorem sptLookup_sptDelete {α : Type} :
    ∀ (t : Spt α) (n k : Nat), sptLookup k (sptDelete n t) = if k = n then none else sptLookup k t
  | .ln, n, k => by simp [sptDelete, sptLookup]
  | .ls v, n, k => by
      by_cases hn : n = 0 <;> by_cases hk : k = 0 <;> simp [sptDelete, sptLookup, hn, hk] <;> omega
  | .bn l r, n, k => by
      by_cases hn : n = 0
      · subst hn; by_cases hk : k = 0 <;> simp [sptDelete, sptLookup, hk]
      · simp only [sptDelete, hn, if_false]
        by_cases he : n % 2 = 0
        · simp only [he, if_true, sptLookup_sptMkBN]
          by_cases hk : k = 0
          · simp [sptLookup, hk] <;> omega
          · by_cases hke : k % 2 = 0
            · simp only [sptLookup, hk, hke, if_false, if_true, sptLookup_sptDelete l]
              by_cases h : k = n
              · subst h; simp
              · have : (k - 1) / 2 ≠ (n - 1) / 2 := by omega
                simp [h, this]
            · simp only [sptLookup, hk, hke, if_false]
              have : k ≠ n := by omega
              simp [this]
        · simp only [he, if_false, sptLookup_sptMkBN]
          by_cases hk : k = 0
          · simp [sptLookup, hk] <;> omega
          · by_cases hke : k % 2 = 0
            · simp only [sptLookup, hk, hke, if_false, if_true]
              have : k ≠ n := by omega
              simp [this]
            · simp only [sptLookup, hk, hke, if_false, sptLookup_sptDelete r]
              by_cases h : k = n
              · subst h; simp
              · have : (k - 1) / 2 ≠ (n - 1) / 2 := by omega
                simp [h, this]
  | .bs l v r, n, k => by
      by_cases hn : n = 0
      · subst hn; by_cases hk : k = 0 <;> simp [sptDelete, sptLookup, hk]
      · simp only [sptDelete, hn, if_false]
        by_cases he : n % 2 = 0
        · simp only [he, if_true, sptLookup_sptMkBS]
          by_cases hk : k = 0
          · simp [sptLookup, hk] <;> omega
          · by_cases hke : k % 2 = 0
            · simp only [sptLookup, hk, hke, if_false, if_true, sptLookup_sptDelete l]
              by_cases h : k = n
              · subst h; simp
              · have : (k - 1) / 2 ≠ (n - 1) / 2 := by omega
                simp [h, this]
            · simp only [sptLookup, hk, hke, if_false]
              have : k ≠ n := by omega
              simp [this]
        · simp only [he, if_false, sptLookup_sptMkBS]
          by_cases hk : k = 0
          · simp [sptLookup, hk] <;> omega
          · by_cases hke : k % 2 = 0
            · simp only [sptLookup, hk, hke, if_false, if_true]
              have : k ≠ n := by omega
              simp [this]
            · simp only [sptLookup, hk, hke, if_false, sptLookup_sptDelete r]
              by_cases h : k = n
              · subst h; simp
              · have : (k - 1) / 2 ≠ (n - 1) / 2 := by omega
                simp [h, this]

/-- `list_delete` lookup (HOL `backend_common`/sptree reasoning; no CakeML tag). -/
theorem sptLookup_sptListDelete {α : Type} :
    ∀ (ks : List Nat) (t : Spt α) (k : Nat),
      sptLookup k (sptListDelete ks t) = if k ∈ ks then none else sptLookup k t
  | [], t, k => by simp [sptListDelete]
  | x :: xs, t, k => by
      simp only [sptListDelete, sptLookup_sptListDelete xs, sptLookup_sptDelete, List.mem_cons]
      by_cases h1 : k = x <;> by_cases h2 : k ∈ xs <;> simp [h1, h2]

end Flapjack
