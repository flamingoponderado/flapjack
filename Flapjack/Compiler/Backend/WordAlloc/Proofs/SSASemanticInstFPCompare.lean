import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticRegisterWrites

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticInstFPCompareWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInstFPCompareWitnesses

/-- Full original native FP Less opcode case, with all six original premises
and the complete Error-exempt source-permutation simulation. Original frame
equality derives both FP reads; the native binary64 comparison determines the
word result, and the fresh-destination locals relation is derived internally.
Missing FP reads retain Error exemption. No target-run, successful-source or
post-state relation premise is added. The Inst/evaluator boundary inherits
reals_as_rational_cuts (SOUNDNESS item 8); comparison finite values use the inherited exact rational rendering of
HOL real values; fixed binary64 FP carriers and all NaN/infinity branches
are retained, and these cases introduce no rounding operation. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstFPLess {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next name left right : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.inst (.fp (.fpLess name left right))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.fp (.fpLess name left right))) source target ssa next tables := by
  have bound : name < next := by
    simpa [everyVarHOL, everyVarInstHOL] using h.2.2.2.1
  have sameLeft : WordSemStateFiniteExact.getFpVar left source = WordSemStateFiniteExact.getFpVar left target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  have sameRight : WordSemStateFiniteExact.getFpVar right source = WordSemStateFiniteExact.getFpVar right target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  have locals (value : WordLocW width) := ssaLocalsRelSetVar next ssa source.locals target.locals name value
    ⟨h.2.1, h.2.2.2.2.1, bound⟩
  refine ⟨target.permute, ?_⟩
  cases l : WordSemStateFiniteExact.getFpVar left source <;>
    cases r : WordSemStateFiniteExact.getFpVar right source <;>
    simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
      WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setVar,
      ssaCcTrans, ssaCcTransInst, nextVarRename, Flapjack.WordAlloc.wordStateEqRel]

/-- Full original native FP LessEqual opcode case, with all six original premises
and the complete Error-exempt source-permutation simulation. Original frame
equality derives both FP reads; the native binary64 comparison determines the
word result, and the fresh-destination locals relation is derived internally.
Missing FP reads retain Error exemption. No target-run, successful-source or
post-state relation premise is added. The Inst/evaluator boundary inherits
reals_as_rational_cuts (SOUNDNESS item 8); comparison finite values use the inherited exact rational rendering of
HOL real values; fixed binary64 FP carriers and all NaN/infinity branches
are retained, and these cases introduce no rounding operation. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstFPLessEqual {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next name left right : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.inst (.fp (.fpLessEqual name left right))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.fp (.fpLessEqual name left right))) source target ssa next tables := by
  have bound : name < next := by
    simpa [everyVarHOL, everyVarInstHOL] using h.2.2.2.1
  have sameLeft : WordSemStateFiniteExact.getFpVar left source = WordSemStateFiniteExact.getFpVar left target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  have sameRight : WordSemStateFiniteExact.getFpVar right source = WordSemStateFiniteExact.getFpVar right target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  have locals (value : WordLocW width) := ssaLocalsRelSetVar next ssa source.locals target.locals name value
    ⟨h.2.1, h.2.2.2.2.1, bound⟩
  refine ⟨target.permute, ?_⟩
  cases l : WordSemStateFiniteExact.getFpVar left source <;>
    cases r : WordSemStateFiniteExact.getFpVar right source <;>
    simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
      WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setVar,
      ssaCcTrans, ssaCcTransInst, nextVarRename, Flapjack.WordAlloc.wordStateEqRel]

/-- Full original native FP Equal opcode case, with all six original premises
and the complete Error-exempt source-permutation simulation. Original frame
equality derives both FP reads; the native binary64 comparison determines the
word result, and the fresh-destination locals relation is derived internally.
Missing FP reads retain Error exemption. No target-run, successful-source or
post-state relation premise is added. The Inst/evaluator boundary inherits
reals_as_rational_cuts (SOUNDNESS item 8); comparison finite values use the inherited exact rational rendering of
HOL real values; fixed binary64 FP carriers and all NaN/infinity branches
are retained, and these cases introduce no rounding operation. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstFPEqual {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next name left right : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.inst (.fp (.fpEqual name left right))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.fp (.fpEqual name left right))) source target ssa next tables := by
  have bound : name < next := by
    simpa [everyVarHOL, everyVarInstHOL] using h.2.2.2.1
  have sameLeft : WordSemStateFiniteExact.getFpVar left source = WordSemStateFiniteExact.getFpVar left target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  have sameRight : WordSemStateFiniteExact.getFpVar right source = WordSemStateFiniteExact.getFpVar right target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  have locals (value : WordLocW width) := ssaLocalsRelSetVar next ssa source.locals target.locals name value
    ⟨h.2.1, h.2.2.2.2.1, bound⟩
  refine ⟨target.permute, ?_⟩
  cases l : WordSemStateFiniteExact.getFpVar left source <;>
    cases r : WordSemStateFiniteExact.getFpVar right source <;>
    simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
      WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setVar,
      ssaCcTrans, ssaCcTransInst, nextVarRename, Flapjack.WordAlloc.wordStateEqRel]

end Flapjack.Compiler.Backend.WordAlloc
