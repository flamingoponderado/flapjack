module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Call
public import Flapjack.Compiler.Backend.BviToData.Proofs.Install

@[expose] public section

/-! Initial-state and program-label facts for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Compiling a program part preserves its function name. -/
@[simp, hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "FST_compile_part"]
theorem fst_compilePart (part : Nat × Nat × Bvi.Exp) :
    (compilePart part).1 = part.1 := by
  rfl

/-- Compiling a program preserves the sequence of function names. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "MAP_FST_compile_prog"]
theorem map_fst_compileProg (program : List (Nat × Nat × Bvi.Exp)) :
    (compileProg program).map Prod.fst = program.map Prod.fst := by
  simp [compileProg, List.map_map, Function.comp_def, fst_compilePart]

/-- Initial BVI and data states satisfy the simulation relation when the data
code and compiler oracle are obtained by compiling the BVI program lists. -/
theorem initialState_related {C F : Type} (ffi : HolFfiState F)
    (program : List (Nat × Nat × Bvi.Exp)) (oracle : BviSem.CompileOracle C)
    (compiler : DataSem.Compiler C) (stamps : Bool) (limits : DataSem.Limits)
    (sizes : Spt Nat) (clock : Nat) :
    stateRel
      (BviSem.initialState ffi (sptFromAList program) oracle
        (fun cfg code => compiler cfg (compileProg code)) clock)
      (DataSem.initialState ffi (sptFromAList (compileProg program))
        (fun n => let (cfg, code) := oracle n; (cfg, compileProg code))
        compiler stamps limits sizes clock) := by
  simp [stateRel, BviSem.initialState, DataSem.initialState, codeRel_compileProg,
    HolFiniteMapExact.empty, sptMap]

end Flapjack.Compiler.Backend.BviToData
