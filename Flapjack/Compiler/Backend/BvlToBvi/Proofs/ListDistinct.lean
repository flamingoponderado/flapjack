module

public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.AuxNameRange
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.Namespace

@[expose] public section

/-! Ordered namespaces of lowered function labels. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs

open Classical in
/-- Compilation preserves distinct labels and records both generated namespaces. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_list_distinct_locs"]
theorem compileList_distinctLocs (n : Nat) (prog : List (Nat × Nat × Bvl.Exp))
    (codeApp : AppList (Nat × Nat × Bvi.Exp)) (code : List (Nat × Nat × Bvi.Exp)) (n' : Nat)
    (premises : (prog.map Prod.fst).Nodup ∧ compileProgramsSource n prog = (codeApp, n') ∧
      code = appListAppend codeApp) :
    (code.map Prod.fst).Nodup ∧
    (∀ name ∈ (code.map Prod.fst).filter (fun name => decide (inNs 1 (name - bvlNumStubs))),
      bvlNumStubs + bvlToBviNamespaces * n ≤ name ∧
        name < bvlNumStubs + bvlToBviNamespaces * n') ∧
    (code.map Prod.fst).filter (fun name => decide (inNs 0 (name - bvlNumStubs))) =
      (prog.map Prod.fst).map (fun name => bvlNumStubs + bvlToBviNamespaces * name) ∧
    (∀ name ∈ code.map Prod.fst, bvlNumStubs ≤ name) ∧
    (∀ name ∈ code.map Prod.fst, ¬ inNs 2 (name - bvlNumStubs) ∧ ¬ inNs 3 (name - bvlNumStubs)) ∧
    n ≤ n' := by
  obtain ⟨distinct, run, rfl⟩ := premises
  have range := compileProgramsSource_nameRange n prog
  have nodup := compileProgramsSource_names_nodup n prog distinct
  have ordered := compileProgramsSource_translatedNames n prog
  simp only [run] at range nodup ordered
  refine ⟨nodup, ?_, ordered, ?_, ?_, range.1⟩
  · intro name member
    obtain ⟨member, selected⟩ := List.mem_filter.mp member
    have ns : inNs 1 (name - bvlNumStubs) := of_decide_eq_true selected
    rcases range.2 name member with ⟨input, _, equal⟩ | ⟨index, lower, upper, equal⟩
    · simp only [inNs, bvlToBviNamespaces] at ns
      simp only [bvlToBviNamespaces] at equal
      omega
    · simp only [bvlToBviNamespaces] at equal ⊢
      omega
  · intro name member
    rcases range.2 name member with ⟨input, _, equal⟩ | ⟨index, _, _, equal⟩ <;> omega
  · intro name member
    rcases range.2 name member with ⟨input, _, equal⟩ | ⟨index, _, _, equal⟩
    · simp only [inNs, bvlToBviNamespaces] at ⊢ equal
      omega
    · simp only [inNs, bvlToBviNamespaces] at ⊢ equal
      omega

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
