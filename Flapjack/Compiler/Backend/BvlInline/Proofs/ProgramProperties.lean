module

public import Flapjack.Compiler.Backend.BvlInline.SourceCompile
public import Flapjack.Compiler.Backend.BvlHandle.Proofs.GeneratedShape

@[expose] public section

/-! Properties of the source BVL program optimizer. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs

/-- Optimizing program entries preserves their first components. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "MAP_FST_MAP_optimise"]
theorem mapFstMapOptimise {α : Type} (splitSeq : Bool) (cutSize : Nat)
    (program : List (α × Nat × Bvl.Exp)) :
    (program.map (optimise splitSeq cutSize)).map Prod.fst = program.map Prod.fst := by
  induction program with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨name, arity, body⟩ := entry
    simp [optimise, ih]

/-- Whole-program compilation preserves the complete list of program names. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "compile_prog_names"]
theorem compileProg_names (limit : Nat) (splitSeq : Bool) (cutSize : Nat)
    (program : List (Nat × Nat × Bvl.Exp)) (inlines : Spt (Nat × Bvl.Exp))
    (output : List (Nat × Nat × Bvl.Exp))
    (run : compileProg limit splitSeq cutSize program = (inlines, output)) :
    output.map Prod.fst = program.map Prod.fst := by
  cases inlineRun : tickCompileProg limit .ln program with
  | mk cache inlined =>
    have names := mapFstTickInlineAll limit .ln program
    simp only [compileProg, compileInc, inlineRun] at run
    cases run
    rw [mapFstMapOptimise]
    change (tickCompileProg limit .ln program).2.map Prod.fst = program.map Prod.fst at names
    simpa [inlineRun] using names


/-- Optimized program bodies satisfy the handler invariant. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "handle_ok_optimise"]
theorem handleOk_optimise {α : Type} (splitSeq : Bool) (cutSize : Nat)
    (program : List (α × Nat × Bvl.Exp)) :
    BvlHandle.Proofs.handleOk ((program.map (optimise splitSeq cutSize)).map fun entry => entry.2.2) := by
  rw [BvlHandle.Proofs.handleOk_every, List.forall_iff_forall_mem]
  intro body member
  simp only [List.mem_map] at member
  obtain ⟨entry, ⟨original, _, rfl⟩, rfl⟩ := member
  obtain ⟨name, arity, originalBody⟩ := original
  exact BvlHandle.Proofs.compileAny_handleOk splitSeq cutSize arity _

/-- Every whole-program compiler output satisfies the handler invariant. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "compile_prog_handle_ok"]
theorem compileProg_handleOk (limit : Nat) (splitSeq : Bool) (cutSize : Nat)
    (program : List (Nat × Nat × Bvl.Exp)) (inlines : Spt (Nat × Bvl.Exp))
    (output : List (Nat × Nat × Bvl.Exp))
    (run : compileProg limit splitSeq cutSize program = (inlines, output)) :
    BvlHandle.Proofs.handleOk (output.map fun entry => entry.2.2) := by
  cases inlineRun : tickCompileProg limit .ln program with
  | mk cache inlined =>
    simp only [compileProg, compileInc, inlineRun] at run
    cases run
    exact handleOk_optimise splitSeq cutSize inlined

end Flapjack.Compiler.Backend.BvlInline.Proofs
