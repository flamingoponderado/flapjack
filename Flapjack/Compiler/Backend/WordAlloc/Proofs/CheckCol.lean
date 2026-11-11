module

public import Flapjack.Compiler.Backend.RegAlloc.ClashTree
public import Flapjack.Compiler.Backend.WordAlloc.Proofs.NumSets
public import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport
public import Mathlib.Data.List.Nodup

@[expose] public section

namespace Flapjack.WordAlloc

/-- Literal fixed-set checker soundness: successful checking retains the input
tree, proves injection on its entire domain, and identifies the entire output
domain with its image. No wf premise or global injection assumption is added. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "check_col_INJ"]
theorem checkColInj (f : Nat → Nat) (tree q r : NumSet)
    (h : RegAlloc.checkCol f tree = some (q, r)) :
    q = tree ∧
      (∀ x y, sptDomain q x → sptDomain q y → f x = f y → x = y) ∧
      sptDomain r = (fun y => ∃ x, sptDomain q x ∧ f x = y) := by
  let keys := (sptToAList tree).map Prod.fst
  have hkeys (key : Nat) : key ∈ keys ↔ sptDomain tree key := by
    constructor
    · intro hm
      obtain ⟨⟨name, value⟩, hentry, he⟩ := List.mem_map.mp hm
      have hkey : name = key := by simpa using he
      refine (sptDomain_iff_lookup tree key).mpr ⟨value, ?_⟩
      rw [← hkey]
      exact (sptMemToAList tree name value).mp hentry
    · intro hd
      obtain ⟨value, hv⟩ := (sptDomain_iff_lookup tree key).mp hd
      exact List.mem_map.mpr ⟨(key, value), (sptMemToAList tree key value).mpr hv, rfl⟩
  have hfrom (names : List Nat) :
      sptFromAList (names.map (fun name => (name, ()))) = numsetListInsert names .ln := by
    induction names with
    | nil => rfl
    | cons name names ih => simp only [List.map_cons, sptFromAList, numsetListInsert, ih]
  have hcol : RegAlloc.checkCol f tree =
      if (keys.map f).Pairwise (· ≠ ·) then
        some (tree, numsetListInsert (keys.map f) .ln) else none := by
    simp only [RegAlloc.checkCol, hfrom]
    simp only [keys, List.map_map, Function.comp_def]
  rw [hcol] at h
  split at h
  · rename_i hd
    have hp := Option.some.inj h
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    refine ⟨rfl, ?_, ?_⟩
    · intro x y hx hy he
      exact List.inj_on_of_nodup_map hd ((hkeys x).mpr hx) ((hkeys y).mpr hy) he
    · rw [domainNumsetListInsert]
      funext y
      simp only [sptDomain, sptLookup, Option.isSome_none, Bool.false_eq_true,
        false_or, List.mem_map, hkeys]
  · simp at h

end Flapjack.WordAlloc
