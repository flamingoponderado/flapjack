module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AdjustedSet
public import Flapjack.Misc.Sptree.UnionAlgebra

@[expose] public section

/-! Sparse-tree intersection needed when restoring a saved environment. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Associations stored only at zero cannot affect an adjusted live set. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "inter_union_lemma"]
theorem interUnionLemma {α β : Type} (ws : List (Nat × α)) (t : Spt α) (s : Spt β)
    (zero : ∀ pair ∈ ws, pair.1 = 0) :
    sptInter (sptUnion t (sptFromAList ws)) (adjustSet s) = sptInter t (adjustSet s) := by
  apply (sptEqThm _ _ ⟨sptWfInter _ _, sptWfInter _ _⟩).2
  intro key
  rw [sptLookup_sptInterCases, sptLookup_sptInterCases, sptLookup_sptUnion,
    sptLookup_sptFromAList]
  cases present : sptLookup key (adjustSet s) with
  | none => simp
  | some entry =>
    have keyNe : key ≠ 0 := by
      have domain : sptDomain (adjustSet s) key := (sptMem_iff_lookup _ _).mpr ⟨entry, present⟩
      obtain ⟨n, eq, _⟩ := (adjustSet_domain s key).mp domain
      simp only [adjustVar] at eq
      omega
    have missing : sptAListLookup key ws = none := by
      cases found : sptAListLookup key ws with
      | none => rfl
      | some value =>
        have member := sptAListLookup_mem key ws value found
        have keyZero := zero (key, value) member
        exact False.elim (keyNe keyZero)
    cases sptLookup key t <;> simp [missing]

/-- Insertion into the left side of a union commutes with intersection. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "inter_insert_union"]
theorem interInsertUnion {α β : Type} (key : Nat) (value : α)
    (left right : Spt α) (domain : Spt β) :
    sptInter (sptInsert key value (sptUnion left right)) domain =
      sptInter (sptUnion (sptInsert key value left) right) domain := by
  rw [sptInsert_union key value (sptUnion left right),
    sptInsert_union key value left, sptUnion_assoc]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
