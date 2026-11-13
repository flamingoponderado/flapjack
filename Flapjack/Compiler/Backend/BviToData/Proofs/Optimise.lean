module

public import Flapjack.Compiler.Backend.DataSpace.Proofs.Seq
public import Flapjack.Compiler.Backend.DataLive.Proofs.CompileCorrect
public import Flapjack.Compiler.Backend.DataSimp.Proofs.Correct
public import Flapjack.Compiler.Backend.BviToData.Optimise

@[expose] public section

/-! Correctness of the complete data optimization pipeline. -/

namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- The three data optimization passes preserve any stopped non-type-error result. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "optimise_correct"]
theorem optimise_correct {C F : Type} (program : DataLang.Prog) (source : State C F)
    (notType : (evaluate program source).1 ≠ some (.err (.abort .typeError)))
    (stopped : (evaluate program source).1 ≠ none) :
    ∃ safe peak stackMax localsSize,
      evaluate (optimise program) source =
        ((evaluate program source).1, { (evaluate program source).2 with localsSize := localsSize, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) := by
  obtain ⟨localsSize, stackMax, safe, peak, liveRun⟩ :=
    DataLive.compile_correct program source notType stopped
  have simpRun := (DataSimp.simp_correct (DataLive.compile program .ln).1 source).trans liveRun
  have noType : (evaluate (DataSimp.simp (DataLive.compile program .ln).1 .skip) source).1 ≠
      some (.err (.abort .typeError)) := by simpa [simpRun] using notType
  have nonzero : (evaluate (DataSimp.simp (DataLive.compile program .ln).1 .skip) source).1 ≠ none := by
    simpa [simpRun] using stopped
  obtain ⟨safe2, peak2, mx2, spaceRun⟩ :=
    DataSpace.compile_correct (DataSimp.simp (DataLive.compile program .ln).1 .skip) source nonzero noType
  refine ⟨safe2, peak2, mx2, localsSize, ?_⟩
  simpa [optimise, simpRun] using spaceRun

end Flapjack.Compiler.Backend.BviToData
