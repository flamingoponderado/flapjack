module

public import Flapjack.Compiler.Backend.BviToData.Proofs.CodeLabels
public import Flapjack.Compiler.Backend.BviToData.Proofs.Program
public import Flapjack.Compiler.Backend.Semantics.DataProps.CodeLabels.Good
public import Flapjack.Compiler.Backend.DataSimp.Proofs.CodeLabels
public import Flapjack.Compiler.Backend.DataLive.Proofs.CodeLabels
public import Flapjack.Compiler.Backend.DataSpace.Proofs.CodeLabels

@[expose] public section

/-! Program code-label preservation for BVI-to-data compilation. -/

namespace Flapjack.Compiler.Backend.BviToData
open Flapjack

/-- Flapjack proof infrastructure: the optimization pipeline cannot add
labels to a compiled BVI expression. -/
private theorem compileExp_labels (n : Nat) (exp : Bvi.Exp) :
    DataSem.getCodeLabels (compileExp n exp) ⊆ BviProps.getCodeLabels exp := by
  have base : DataSem.getCodeLabels (compileSource n (List.range n) true [] [exp]).1 ⊆
      BviProps.getCodeLabels exp := by
    simpa [BviProps.getCodeLabelsList_eq, BviProps.getCodeLabelsList] using
      getCodeLabels_compile n (List.range n) true [] [exp]
  have live := DataLive.getCodeLabels_compile (compileSource n (List.range n) true [] [exp]).1 .ln
  have simplified := DataSimp.getCodeLabels_simp
    (DataLive.compile (compileSource n (List.range n) true [] [exp]).1 .ln).1 .skip
  simp only [DataSem.getCodeLabels, Set.union_empty] at simplified
  unfold compileExp optimise
  rw [DataSpace.getCodeLabels_compile]
  exact simplified.trans (live.trans base)

/-- A program with good code labels retains that property after compilation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "compile_prog_good_code_labels"]
theorem compileProg_goodCodeLabels (program : List (Nat × Nat × Bvi.Exp)) (external : Set Nat)
    (good : BviProps.goodCodeLabels program external) :
    DataSem.goodCodeLabels (compileProg program) external := by
  simp only [DataSem.goodCodeLabels, BviProps.goodCodeLabels, Set.subset_def,
    Set.mem_sUnion, Set.mem_image, Set.mem_ofPred_eq, List.mem_map] at good ⊢
  intro label ⟨set, ⟨entry, membership, setEq⟩, has⟩
  subst set
  obtain ⟨key, count, exp⟩ := entry
  simp only [compileProg, List.mem_map] at membership
  obtain ⟨⟨sourceKey, sourceCount, sourceExp⟩, sourceMem, equality⟩ := membership
  simp only [compilePart, Prod.mk.injEq] at equality
  obtain ⟨rfl, rfl, rfl⟩ := equality
  have sourceLabel := compileExp_labels sourceCount sourceExp has
  have allowed := good label ⟨BviProps.getCodeLabels sourceExp,
    ⟨(sourceKey, sourceCount, sourceExp), sourceMem, rfl⟩, sourceLabel⟩
  simp only [compileProg, List.mem_map]
  simpa [List.map_map, Function.comp_def, compilePart] using allowed

end Flapjack.Compiler.Backend.BviToData
