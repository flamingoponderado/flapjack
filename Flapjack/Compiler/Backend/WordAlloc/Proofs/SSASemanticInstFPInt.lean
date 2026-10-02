import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticRegisterWrites

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticInstFPIntWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInstFPIntWitnesses

/-- Full original native FPToInt opcode case, retaining all six original
premises and complete Error-exempt source-permutation simulation. Original
frame equality derives identical FP reads, width64/other-width decisions,
conversion/range outcomes and half-register extraction/insertion. Native
finite-map writes establish the postframe; SSA, next and general locals are
unchanged. No target-run, successful-source or post-state premise is added.
The evaluator/conversion boundary inherits reals_as_rational_cuts (SOUNDNESS
item 8); real-to-float is used only at integer inputs, within its rational domain. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
theorem ssaCcTransCorrectInstFPToInt {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next dst arg : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.inst (.fp (.fpToInt dst arg))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.fp (.fpToInt dst arg))) source target ssa next tables := by
  have same : source.fpRegs = target.fpRegs := h.1.1.symm
  refine ⟨target.permute, ?_⟩
  cases read : target.fpRegs.lookup arg with
  | none =>
    simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
      WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  | some f =>
    cases converted : holFp64ToInt .roundTiesToEven f with
    | none =>
      simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
        WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
    | some i =>
      by_cases valid : (BitVec.ofInt 32 i).toInt = i
      <;> by_cases size : width = 64
      <;> cases half : target.fpRegs.lookup (dst / 2)
      <;> simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
        WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setFpVar,
        ssaCcTrans, ssaCcTransInst, Flapjack.WordAlloc.wordStateEqRel]

/-- Full original native FPFromInt opcode case, retaining all six original
premises and complete Error-exempt source-permutation simulation. Original
frame equality derives identical FP reads, width64/other-width decisions,
conversion/range outcomes and half-register extraction/insertion. Native
finite-map writes establish the postframe; SSA, next and general locals are
unchanged. No target-run, successful-source or post-state premise is added.
The evaluator/conversion boundary inherits reals_as_rational_cuts (SOUNDNESS
item 8); real-to-float is used only at integer inputs, within its rational domain. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstFPFromInt {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next dst arg : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.inst (.fp (.fpFromInt dst arg))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.fp (.fpFromInt dst arg))) source target ssa next tables := by
  have same : source.fpRegs = target.fpRegs := h.1.1.symm
  refine ⟨target.permute, ?_⟩
  by_cases size : width = 64
  <;> cases read : target.fpRegs.lookup arg
  <;> cases half : target.fpRegs.lookup (arg / 2)
  <;> simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
    WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setFpVar,
    ssaCcTrans, ssaCcTransInst, Flapjack.WordAlloc.wordStateEqRel]

end Flapjack.Compiler.Backend.WordAlloc
