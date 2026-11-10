module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeList
public import Flapjack.Compiler.Backend.ClosCall.Proofs.InsertDomain

@[expose] public section

/-! Well-formed direct-call compiler states. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack

/-- The emitted label set is exactly the successors of known locations, and
the code list has no duplicate labels. The map and payload types remain
independent, as in the HOL definition. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "wfg_def"]
def wellFormed {A B : Type} (g : Spt A × List (Nat × B)) : Prop :=
  { label | label ∈ g.2.map Prod.fst } = Set.image Nat.succ (sptDomain g.1) ∧
    (g.2.map Prod.fst).Nodup

/-- Every emitted label is the successor of a known location. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "wfg'_def"]
def weaklyWellFormed {A B : Type} (g : Spt A × List (Nat × B)) : Prop :=
  { label | label ∈ g.2.map Prod.fst } ⊆ Set.image Nat.succ (sptDomain g.1)

/-- If the function locations are known, adding their bodies preserves the
one-sided code invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "wfg'_code_list"]
theorem weaklyWellFormed_codeListSource {A B C : Type} (fns : List (A × B))
    (g : Spt C × List (Nat × A × B)) (loc : Nat)
    (h : weaklyWellFormed g ∧
      { n | n ∈ (List.range fns.length).map (fun i => loc + 2 * i) } ⊆ sptDomain g.1) :
    weaklyWellFormed (codeListSource loc fns g) := by
  obtain ⟨well, known⟩ := h
  unfold weaklyWellFormed at well ⊢
  rw [codeListSource_fst]
  intro label member
  simp only [Set.mem_ofPred_eq, codeListSource_labels, List.mem_append,
    List.mem_reverse, List.mem_map, List.mem_range] at member
  rcases member with ⟨i, bound, rfl⟩ | old
  · refine ⟨loc + 2 * i, known ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, List.mem_map, List.mem_range]
      exact ⟨i, bound, rfl⟩
    · omega
  · apply well
    simpa only [Set.mem_ofPred_eq, List.mem_map] using old

/-- Adding known locations preserves the one-sided code invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "wfg'_insert_each"]
theorem weaklyWellFormed_insertEach {A : Type} (n : Nat) (g : NumSet × List (Nat × A))
    (loc : Nat) (h : weaklyWellFormed g) : weaklyWellFormed (insertEachSource loc n g) := by
  have samePayload : ∀ (count pos : Nat) (state : NumSet × List (Nat × A)),
      (insertEachSource pos count state).2 = state.2 := by
    intro count
    induction count with
    | zero => intro pos state; rfl
    | succ count ih =>
      intro pos state
      cases state with
      | mk known payload => exact ih (pos + 2) (sptInsert pos () known, payload)
  unfold weaklyWellFormed at h ⊢
  rw [samePayload]
  intro label member
  obtain ⟨x, domain, eq⟩ := h member
  refine ⟨x, ?_, eq⟩
  rw [domain_insertEach]
  exact Or.inr domain

end Flapjack.Compiler.Backend.ClosCall
