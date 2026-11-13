module

public import Flapjack.Misc.Sptree
public import Flapjack.Misc.Sptree.FromAList.Lookup

@[expose] public section

/-! Auxiliary-code installation for the BVL-to-BVI relation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs

/-- Every named auxiliary entry is installed with its original pair payload. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "aux_code_installed_def"]
def auxCodeInstalled {α β : Type} : List (Nat × α × β) → Spt (α × β) → Prop
  | [], _ => True
  | (name, arity, body) :: rest, code =>
    sptLookup name code = some (arity, body) ∧ auxCodeInstalled rest code

/-- Installing an append entails installation of both constituent lists. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "aux_code_installed_APPEND"]
theorem auxCodeInstalled_append {α β : Type} (xs ys : List (Nat × α × β)) (code : Spt (α × β)) :
    auxCodeInstalled (xs ++ ys) code → auxCodeInstalled xs code ∧ auxCodeInstalled ys code := by
  induction xs with
  | nil => simp [auxCodeInstalled]
  | cons entry rest ih =>
    rcases entry with ⟨name, arity, body⟩
    simp only [List.cons_append, auxCodeInstalled]
    intro ⟨first, tail⟩
    exact ⟨⟨first, (ih tail).1⟩, (ih tail).2⟩

/-- Installed auxiliary code remains installed in a source sparse-tree extension. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "aux_code_installed_subspt"]
theorem auxCodeInstalled_subspt {α β : Type} (xs : List (Nat × α × β)) (first second : Spt (α × β))
    (installed : auxCodeInstalled xs first) (extension : sptSubspt first second) :
    auxCodeInstalled xs second := by
  induction xs with
  | nil => trivial
  | cons entry rest ih =>
    rcases entry with ⟨name, arity, body⟩
    rcases installed with ⟨lookup, tail⟩
    have member : sptMem name first := (sptMem_iff_lookup name first).2 ⟨_, lookup⟩
    have same := (extension name member).2
    exact ⟨same.trans lookup, ih tail⟩

/-- A contiguous block of an association list with distinct keys is installed
by the sparse tree built from the whole list. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "aux_code_installed_sublist"]
theorem auxCodeInstalled_sublist {α β : Type} (aux ls : List (Nat × α × β))
    (premises : aux <:+: ls ∧ (ls.map Prod.fst).Nodup) :
    auxCodeInstalled aux (sptFromAList ls) := by
  rcases premises with ⟨sub, distinct⟩
  suffices ∀ aux' : List (Nat × α × β), (∀ entry, entry ∈ aux' → entry ∈ ls) →
      auxCodeInstalled aux' (sptFromAList ls) from this aux (fun _ member => sub.mem member)
  intro aux'
  induction aux' with
  | nil => intro _; trivial
  | cons entry rest ih =>
    intro contained
    rcases entry with ⟨name, arity, body⟩
    refine ⟨?_, ih ?_⟩
    · rw [sptLookupFromAList]
      exact holALookup_of_distinct_member ls name (arity, body) ⟨distinct, contained _ (by simp)⟩
    · intro entry member
      exact contained entry (by simp [member])

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
