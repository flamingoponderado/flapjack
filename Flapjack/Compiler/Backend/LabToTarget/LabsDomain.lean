import Flapjack.Compiler.Backend.LabToTarget.LabelLookup
import Mathlib.Data.Set.Basic

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "labs_domain_def"]
def labsDomain {α : Type} (labs : Spt (Spt α)) : Set (Nat × Nat) :=
  {pair | labLookup pair.1 pair.2 labs ≠ none}

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "labs_domain_LN"]
theorem labsDomain_ln {α : Type} : labsDomain (.ln : Spt (Spt α)) = ∅ := by
  ext pair
  simp [labsDomain, labLookup, sptLookup]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "labs_domain_insert"]
theorem labsDomain_insert {α : Type} (key : Nat) (inner : Spt α)
    (labs : Spt (Spt α)) (fresh : ¬ sptDomain labs key) :
    labsDomain (sptInsert key inner labs) =
      (fun n => (key, n)) '' (sptDomain inner) ∪ labsDomain labs := by
  ext pair
  rcases pair with ⟨outer, index⟩
  have imageMem : ((outer, index) ∈ (fun n => (key, n)) '' (sptDomain inner)) ↔
      outer = key ∧ sptDomain inner index := by
    change (∃ n, sptDomain inner n ∧ (key, n) = (outer, index)) ↔ _
    constructor
    · rintro ⟨n, hn, hpair⟩
      have hkey := congrArg Prod.fst hpair
      have hindex := congrArg Prod.snd hpair
      change n = index at hindex
      exact ⟨hkey.symm, hindex ▸ hn⟩
    · rintro ⟨rfl, hn⟩
      exact ⟨index, hn, rfl⟩
  by_cases heq : outer = key
  · subst outer
    have hnone : sptLookup key labs = none := by
      simpa [sptDomain] using fresh
    simp only [labsDomain, Set.mem_ofPred_eq, labLookup, sptLookup_sptInsert_same,
      hnone, imageMem, eq_self, true_and, Set.mem_union]
    cases hlookup : sptLookup index inner <;> simp [sptDomain, hlookup]
  · simp [labsDomain, labLookup, sptLookup_sptInsert_ne _ _ _ _ heq,
      imageMem, heq]

end Flapjack.Compiler.Backend.LabToTarget
