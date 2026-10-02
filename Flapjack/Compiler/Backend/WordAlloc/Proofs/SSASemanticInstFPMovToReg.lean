import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticRegisterWrites

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticInstFPMovToRegWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInstFPMovToRegWitnesses

/-- Full original FPMovToReg case with all six premises and complete
Error-exempt source-permutation simulation. Original frame derives the fixed64
FP read; width64 gives one fresh write, other widths give two sequential fresh
writes with original low/high extraction. Original SSA setVar and map extension
lemmas derive final locals, including aliased destinations. No target-run,
successful-source or post-state premise is added. Missing FP read retains Error
exemption. Inst/evaluator inherits reals_as_rational_cuts (SOUNDNESS item 8);
this transfer itself only copies/extracts bits. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstFPMovToReg {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next first second fp : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next))
        (.inst (.fp (.fpMovToReg first second fp))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.fp (.fpMovToReg first second fp))) source target ssa next tables := by
  have same : source.fpRegs = target.fpRegs := h.1.1.symm
  refine ⟨target.permute, ?_⟩
  cases read : target.fpRegs.lookup fp with
  | none =>
    simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
      WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  | some value =>
    by_cases size : width = 64
    · have bound : first < next := by
        simpa [everyVarHOL, everyVarInstHOL, size] using h.2.2.2.1
      have locals := ssaLocalsRelSetVar next ssa source.locals target.locals first (.word (value.setWidth width))
        ⟨h.2.1, h.2.2.2.2.1, bound⟩
      simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
        WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setVar,
        ssaCcTrans, ssaCcTransInst, nextVarRename, Flapjack.WordAlloc.wordStateEqRel]
    · have bounds : first < next ∧ second < next := by
        simpa [everyVarHOL, everyVarInstHOL, size] using h.2.2.2.1
      have notPhysical : ¬ isPhyVar next := by
        have allocated := h.2.2.1
        simp [isAllocVar, isPhyVar] at allocated ⊢
        omega
      have extended := ssaMapOKExtend next ssa first ⟨h.2.2.2.2.1, notPhysical⟩
      have lowLocals := ssaLocalsRelSetVar next ssa source.locals target.locals first
        (.word (holWordExtract 31 0 value width)) ⟨h.2.1, h.2.2.2.2.1, bounds.1⟩
      have highLocals := ssaLocalsRelSetVar (next + 4) (sptInsert first next ssa)
        (sptInsert first (.word (holWordExtract 31 0 value width)) source.locals)
        (sptInsert next (.word (holWordExtract 31 0 value width)) target.locals) second
        (.word (holWordExtract 63 32 value width)) ⟨lowLocals, extended, by omega⟩
      simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
        WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setVar,
        ssaCcTrans, ssaCcTransInst, nextVarRename, Flapjack.WordAlloc.wordStateEqRel]

end Flapjack.Compiler.Backend.WordAlloc
