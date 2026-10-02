import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticRegisterWrites

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticInstFPArithWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInstFPArithWitnesses

/-- Full original native FPSqrt opcode case with all six premises and complete
Error-exempt source-permutation simulation. Original frame derives all fixed
binary64 FP reads and the identical native operation and finite-map write.
SSA, next and general locals are unchanged. Missing reads retain Error
exemption; no target-run, successful-source or post-state premise is added.
The Inst/evaluator and arithmetic boundary inherit reals_as_rational_cuts
(SOUNDNESS item 8), including choice-based rounding and quiet NaN selection.
Native roundTiesToEven and Fma accumulator ordering are preserved. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstFPSqrt {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next dst arg : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.inst (.fp (.fpSqrt dst arg))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.fp (.fpSqrt dst arg))) source target ssa next tables := by
  have same_arg : WordSemStateFiniteExact.getFpVar arg source = WordSemStateFiniteExact.getFpVar arg target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  refine ⟨target.permute, ?_⟩
  cases read_arg : WordSemStateFiniteExact.getFpVar arg source <;>
    simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
      WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setFpVar,
      ssaCcTrans, ssaCcTransInst, Flapjack.WordAlloc.wordStateEqRel]

/-- Full original native FPAdd opcode case with all six premises and complete
Error-exempt source-permutation simulation. Original frame derives all fixed
binary64 FP reads and the identical native operation and finite-map write.
SSA, next and general locals are unchanged. Missing reads retain Error
exemption; no target-run, successful-source or post-state premise is added.
The Inst/evaluator and arithmetic boundary inherit reals_as_rational_cuts
(SOUNDNESS item 8), including choice-based rounding and quiet NaN selection.
Native roundTiesToEven and Fma accumulator ordering are preserved. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstFPAdd {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next dst arg other : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.inst (.fp (.fpAdd dst arg other))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.fp (.fpAdd dst arg other))) source target ssa next tables := by
  have same_arg : WordSemStateFiniteExact.getFpVar arg source = WordSemStateFiniteExact.getFpVar arg target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  have same_other : WordSemStateFiniteExact.getFpVar other source = WordSemStateFiniteExact.getFpVar other target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  refine ⟨target.permute, ?_⟩
  cases read_arg : WordSemStateFiniteExact.getFpVar arg source <;>
  cases read_other : WordSemStateFiniteExact.getFpVar other source <;>
    simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
      WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setFpVar,
      ssaCcTrans, ssaCcTransInst, Flapjack.WordAlloc.wordStateEqRel]

/-- Full original native FPSub opcode case with all six premises and complete
Error-exempt source-permutation simulation. Original frame derives all fixed
binary64 FP reads and the identical native operation and finite-map write.
SSA, next and general locals are unchanged. Missing reads retain Error
exemption; no target-run, successful-source or post-state premise is added.
The Inst/evaluator and arithmetic boundary inherit reals_as_rational_cuts
(SOUNDNESS item 8), including choice-based rounding and quiet NaN selection.
Native roundTiesToEven and Fma accumulator ordering are preserved. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstFPSub {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next dst arg other : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.inst (.fp (.fpSub dst arg other))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.fp (.fpSub dst arg other))) source target ssa next tables := by
  have same_arg : WordSemStateFiniteExact.getFpVar arg source = WordSemStateFiniteExact.getFpVar arg target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  have same_other : WordSemStateFiniteExact.getFpVar other source = WordSemStateFiniteExact.getFpVar other target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  refine ⟨target.permute, ?_⟩
  cases read_arg : WordSemStateFiniteExact.getFpVar arg source <;>
  cases read_other : WordSemStateFiniteExact.getFpVar other source <;>
    simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
      WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setFpVar,
      ssaCcTrans, ssaCcTransInst, Flapjack.WordAlloc.wordStateEqRel]

/-- Full original native FPMul opcode case with all six premises and complete
Error-exempt source-permutation simulation. Original frame derives all fixed
binary64 FP reads and the identical native operation and finite-map write.
SSA, next and general locals are unchanged. Missing reads retain Error
exemption; no target-run, successful-source or post-state premise is added.
The Inst/evaluator and arithmetic boundary inherit reals_as_rational_cuts
(SOUNDNESS item 8), including choice-based rounding and quiet NaN selection.
Native roundTiesToEven and Fma accumulator ordering are preserved. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstFPMul {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next dst arg other : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.inst (.fp (.fpMul dst arg other))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.fp (.fpMul dst arg other))) source target ssa next tables := by
  have same_arg : WordSemStateFiniteExact.getFpVar arg source = WordSemStateFiniteExact.getFpVar arg target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  have same_other : WordSemStateFiniteExact.getFpVar other source = WordSemStateFiniteExact.getFpVar other target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  refine ⟨target.permute, ?_⟩
  cases read_arg : WordSemStateFiniteExact.getFpVar arg source <;>
  cases read_other : WordSemStateFiniteExact.getFpVar other source <;>
    simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
      WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setFpVar,
      ssaCcTrans, ssaCcTransInst, Flapjack.WordAlloc.wordStateEqRel]

/-- Full original native FPDiv opcode case with all six premises and complete
Error-exempt source-permutation simulation. Original frame derives all fixed
binary64 FP reads and the identical native operation and finite-map write.
SSA, next and general locals are unchanged. Missing reads retain Error
exemption; no target-run, successful-source or post-state premise is added.
The Inst/evaluator and arithmetic boundary inherit reals_as_rational_cuts
(SOUNDNESS item 8), including choice-based rounding and quiet NaN selection.
Native roundTiesToEven and Fma accumulator ordering are preserved. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstFPDiv {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next dst arg other : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.inst (.fp (.fpDiv dst arg other))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.fp (.fpDiv dst arg other))) source target ssa next tables := by
  have same_arg : WordSemStateFiniteExact.getFpVar arg source = WordSemStateFiniteExact.getFpVar arg target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  have same_other : WordSemStateFiniteExact.getFpVar other source = WordSemStateFiniteExact.getFpVar other target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  refine ⟨target.permute, ?_⟩
  cases read_arg : WordSemStateFiniteExact.getFpVar arg source <;>
  cases read_other : WordSemStateFiniteExact.getFpVar other source <;>
    simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
      WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setFpVar,
      ssaCcTrans, ssaCcTransInst, Flapjack.WordAlloc.wordStateEqRel]

/-- Full original native FPFma opcode case with all six premises and complete
Error-exempt source-permutation simulation. Original frame derives all fixed
binary64 FP reads and the identical native operation and finite-map write.
SSA, next and general locals are unchanged. Missing reads retain Error
exemption; no target-run, successful-source or post-state premise is added.
The Inst/evaluator and arithmetic boundary inherit reals_as_rational_cuts
(SOUNDNESS item 8), including choice-based rounding and quiet NaN selection.
Native roundTiesToEven and Fma accumulator ordering are preserved. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstFPFma {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next dst arg other : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.inst (.fp (.fpFma dst arg other))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.fp (.fpFma dst arg other))) source target ssa next tables := by
  have same_arg : WordSemStateFiniteExact.getFpVar arg source = WordSemStateFiniteExact.getFpVar arg target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  have same_other : WordSemStateFiniteExact.getFpVar other source = WordSemStateFiniteExact.getFpVar other target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  have same_dst : WordSemStateFiniteExact.getFpVar dst source = WordSemStateFiniteExact.getFpVar dst target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  refine ⟨target.permute, ?_⟩
  cases read_arg : WordSemStateFiniteExact.getFpVar arg source <;>
  cases read_other : WordSemStateFiniteExact.getFpVar other source <;>
  cases read_dst : WordSemStateFiniteExact.getFpVar dst source <;>
    simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
      WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setFpVar,
      ssaCcTrans, ssaCcTransInst, Flapjack.WordAlloc.wordStateEqRel]

end Flapjack.Compiler.Backend.WordAlloc
