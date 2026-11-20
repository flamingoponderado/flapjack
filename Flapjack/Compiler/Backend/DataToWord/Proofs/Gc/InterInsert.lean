module

public import Flapjack.Misc.Sptree.Wf

@[expose] public section

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

open Flapjack
open Classical

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "inter_insert"]
theorem inter_insert {α β : Type} (n : Nat) (x : α) (t1 : Spt α) (t2 : Spt β) :
    sptInter (sptInsert n x t1) t2 =
      if sptDomain t2 n then sptInsert n x (sptInter t1 t2) else sptInter t1 t2 := by
  classical
  by_cases h : sptDomain t2 n
  · simp only [h, if_pos]
    apply (sptEqThm _ _ ⟨sptWfInter _ _, sptWfInsert _ _ _ (sptWfInter _ _)⟩).2
    intro k
    by_cases hk : k = n
    · subst k
      simp [sptLookup_sptInterCases, sptLookup_sptInsert_same, sptDomain] at h ⊢
      cases he : sptLookup n t2 <;> simp_all
    · rw [sptLookup_sptInterCases, sptLookup_sptInsert_ne _ _ _ _ hk,
        sptLookup_sptInsert_ne _ _ _ _ hk, sptLookup_sptInterCases]
  · simp only [h, if_false]
    apply (sptEqThm _ _ ⟨sptWfInter _ _, sptWfInter _ _⟩).2
    intro k
    by_cases hk : k = n
    · subst k
      simp [sptLookup_sptInterCases, sptLookup_sptInsert_same, sptDomain] at h ⊢
      cases he : sptLookup n t2 <;> simp_all
    · rw [sptLookup_sptInterCases, sptLookup_sptInsert_ne _ _ _ _ hk,
        sptLookup_sptInterCases]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
