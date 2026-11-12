module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.InstalledCode
import Mathlib.Data.List.Nodup

@[expose] public section

/-! Original code-installation properties for sparse-tree unions. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- A contiguous portion of distinct-key code is installed in its source tree. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "code_installed_fromAList_strong"]
theorem codeInstalled_fromAList_strong {A B : Type} : ∀ (ls ls' : List (Nat × A × B)),
    ((ls.map Prod.fst).Nodup ∧ ls' <:+: ls) →
      codeInstalled ls' (sptFromAList ls) := by
  intro ls ls' h entry member
  have inAll : entry ∈ ls := h.2.sublist.subset member
  rw [sptLookup_sptFromAList]
  apply sptAListLookup_eq_of_mem_unique entry.1 entry.2 ls
  · exact inAll
  · intro other otherMem
    have eq : (entry.1, other) = entry :=
      List.inj_on_of_nodup_map h.1 otherMem inAll rfl
    exact congrArg Prod.snd eq

/-- Left-biased tree union preserves installed code when the left tree is
disjoint from the installed labels. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "code_installed_union"]
theorem codeInstalled_union {A B : Type} (aux : List (Nat × A × B))
    (y x : Spt (A × B))
    (h : codeInstalled aux y ∧ ∀ k, ¬ (k ∈ aux.map Prod.fst ∧ sptDomain x k)) :
    codeInstalled aux (sptUnion x y) := by
  intro entry member
  have absent : sptLookup entry.1 x = none := by
    cases lookup : sptLookup entry.1 x with
    | none => rfl
    | some value =>
      have keyMem : entry.1 ∈ aux.map Prod.fst :=
        List.mem_map.mpr ⟨entry, member, rfl⟩
      have inDomain : sptDomain x entry.1 := (sptDomain_iff_lookup x entry.1).2 ⟨value, lookup⟩
      exact False.elim (h.2 entry.1 ⟨keyMem, inDomain⟩)
  simpa [sptLookup_sptUnion, absent] using h.1 entry member

/-- Left-biased tree union retains code already installed in its left tree. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "code_installed_union1"]
theorem codeInstalled_union1 {A B : Type} (aux : List (Nat × A × B))
    (t1 t2 : Spt (A × B)) (installed : codeInstalled aux t1) :
    codeInstalled aux (sptUnion t1 t2) := by
  intro entry member
  rw [sptLookup_sptUnion, installed entry member]

/-- Inserting a key absent from an installed list preserves its installation. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "code_installed_insert"]
theorem codeInstalled_insert {A B : Type} (aux : List (Nat × A × B))
    (tree : Spt (A × B)) (key : Nat) (value : A × B)
    (premises : codeInstalled aux tree ∧ key ∉ aux.map Prod.fst) :
    codeInstalled aux (sptInsert key value tree) := by
  obtain ⟨installed, fresh⟩ := premises
  intro entry member
  have different : entry.1 ≠ key := by
    intro equal
    apply fresh
    exact List.mem_map.mpr ⟨entry, member, equal⟩
  rw [sptLookup_sptInsert_ne key entry.1 value tree different]
  exact installed entry member

end Flapjack.Compiler.Backend.ClosToBvl
