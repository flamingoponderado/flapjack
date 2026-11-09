module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeList

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

/-- Exact well-formedness implies the one-sided code invariant. -/
theorem wellFormed_weak {A B : Type} (g : Spt A × List (Nat × B))
    (well : wellFormed g) : weaklyWellFormed g := by
  unfold weaklyWellFormed
  rw [well.1]

/-- If the function locations are known, adding their bodies preserves the
one-sided code invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "wfg'_code_list"]
theorem weaklyWellFormed_codeListSource {A B C : Type} (fns : List (A × B))
    (g : Spt C × List (Nat × A × B)) (loc : Nat)
    (well : weaklyWellFormed g)
    (known : { n | n ∈ (List.range fns.length).map (fun i => loc + 2 * i) } ⊆ sptDomain g.1) :
    weaklyWellFormed (codeListSource loc fns g) := by
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

/-- The executable fold-based generator obeys the same invariant. -/
theorem weaklyWellFormed_codeList (fns : List (Nat × ClosLang.Exp)) (g : State) (loc : Nat)
    (well : weaklyWellFormed g)
    (known : { n | n ∈ (List.range fns.length).map (fun i => loc + 2 * i) } ⊆ sptDomain g.1) :
    weaklyWellFormed (codeList loc fns g) := by
  rw [codeList_eq_source]
  exact weaklyWellFormed_codeListSource fns g loc well known

end Flapjack.Compiler.Backend.ClosCall
