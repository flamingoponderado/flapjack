import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Accumulator
import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLocations

/-! Origins of labels in closure-to-BVL program conversion. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

private abbrev Aux := List (Nat × Nat × Bvl.Exp)

/-- Recursive-group construction emits exactly the old labels and the
evenly spaced labels reserved for the group. -/
theorem buildAux_label_iff (entries : List (Nat × Bvl.Exp)) (start : Nat)
    (aux : Aux) (label : Nat) :
    label ∈ (buildAux start entries aux).2.map Prod.fst ↔
      label ∈ aux.map Prod.fst ∨ ∃ index, index < entries.length ∧ label = start + 2 * index := by
  constructor
  · exact buildAux_label_mem entries start aux label
  · intro origin
    cases origin with
    | inl previous =>
      obtain ⟨entry, entryMem, entryLabel⟩ := List.mem_map.mp previous
      obtain ⟨added, equal⟩ := buildAux_acc entries start aux
      apply List.mem_map.mpr
      exact ⟨entry, by rw [equal]; exact List.mem_append_right added entryMem, entryLabel⟩
    | inr generated =>
      obtain ⟨index, bound, rfl⟩ := generated
      have built : buildAux start entries aux =
          ((buildAux start entries aux).1, (buildAux start entries aux).2) := by
        cases buildAux start entries aux
        rfl
      obtain ⟨item, member⟩ := buildAux_mem entries start aux _ _ built index bound
      exact List.mem_map.mpr ⟨(start + 2 * index, item), member, rfl⟩

/-- Zipping one compiled expression per source entry retains exactly the
source entry labels, shifted by the runtime-stub prefix. -/
private theorem zip_entry_labels (offset : Nat) (program : List (Nat × Nat × ClosLang.Exp))
    (compiled : List Bvl.Exp) (lengthEq : compiled.length = program.length) :
    (((program.zip compiled).map (fun ((loc, arity, _), body) => (loc + offset, arity, body))).map Prod.fst) =
      program.map (fun entry => entry.1 + offset) := by
  induction program generalizing compiled with
  | nil => simp
  | cons first rest ih =>
    cases compiled with
    | nil => simp at lengthEq
    | cons body remaining =>
      obtain ⟨name, arity, expression⟩ := first
      simp only [List.length_cons, Nat.succ.injEq] at lengthEq
      simp [ih remaining lengthEq]

/-- Program conversion's entry labels are precisely its shifted input labels;
all other labels are those generated in its auxiliary accumulator. -/
theorem compileProgHOL_label_origins (maxApp : Nat) (program : List (Nat × Nat × ClosLang.Exp)) :
    (compileProgHOL maxApp program).map Prod.fst =
      program.map (fun entry => entry.1 + numStubs maxApp) ++
        ((compileExpListHOL maxApp (program.map (fun (_, _, body) => body)) []).2.map Prod.fst) := by
  have lengthEq := compileExpList_length maxApp (program.map (fun (_, _, body) => body)) []
  simp only [List.length_map] at lengthEq
  simp only [compileProgHOL, List.map_append]
  rw [zip_entry_labels (numStubs maxApp) program _ lengthEq]

/-- The same label decomposition holds for the checked converter actually
used by preprocessing. -/
theorem compileProg_checked_label_origins (maxApp : Nat) (program : List (Nat × Nat × ClosLang.Exp))
    (compiled : Aux) (run : compileProg? maxApp program = some compiled) :
    compiled.map Prod.fst =
      program.map (fun entry => entry.1 + numStubs maxApp) ++
        ((compileExpListHOL maxApp (program.map (fun (_, _, body) => body)) []).2.map Prod.fst) := by
  have exactRun := compileProg_checked_eq maxApp program
  have equal : compiled = compileProgHOL maxApp program := Option.some.inj (run.symm.trans exactRun)
  rw [equal]
  exact compileProgHOL_label_origins maxApp program

end Flapjack.Compiler.Backend.ClosToBvl
