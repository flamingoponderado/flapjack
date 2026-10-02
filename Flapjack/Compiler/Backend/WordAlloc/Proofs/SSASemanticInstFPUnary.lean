import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticRegisterWrites

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticInstFPUnaryWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInstFPUnaryWitnesses

/-- Full original native FPMov opcode case. All six original premises and
complete Error-exempt source-permutation simulation are retained. Frame
equality derives the fixed binary64 FP read and the same finite-map update;
general locals, SSA and next are unchanged. Missing FP reads retain Error
exemption. No target-run/success/post-state premise is added. The Inst/evaluator
boundary inherits reals_as_rational_cuts (SOUNDNESS item 8); these operations
copy or change only the binary64 sign, retaining NaN payloads and infinities. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstFPMov {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next dst arg : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.inst (.fp (.fpMov dst arg))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.fp (.fpMov dst arg))) source target ssa next tables := by
  have same : WordSemStateFiniteExact.getFpVar arg source = WordSemStateFiniteExact.getFpVar arg target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  refine ⟨target.permute, ?_⟩
  cases read : WordSemStateFiniteExact.getFpVar arg source <;>
    simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
      WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setFpVar,
      ssaCcTrans, ssaCcTransInst, Flapjack.WordAlloc.wordStateEqRel]

/-- Full original native FPAbs opcode case. All six original premises and
complete Error-exempt source-permutation simulation are retained. Frame
equality derives the fixed binary64 FP read and the same finite-map update;
general locals, SSA and next are unchanged. Missing FP reads retain Error
exemption. No target-run/success/post-state premise is added. The Inst/evaluator
boundary inherits reals_as_rational_cuts (SOUNDNESS item 8); these operations
copy or change only the binary64 sign, retaining NaN payloads and infinities. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstFPAbs {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next dst arg : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.inst (.fp (.fpAbs dst arg))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.fp (.fpAbs dst arg))) source target ssa next tables := by
  have same : WordSemStateFiniteExact.getFpVar arg source = WordSemStateFiniteExact.getFpVar arg target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  refine ⟨target.permute, ?_⟩
  cases read : WordSemStateFiniteExact.getFpVar arg source <;>
    simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
      WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setFpVar,
      ssaCcTrans, ssaCcTransInst, Flapjack.WordAlloc.wordStateEqRel]

/-- Full original native FPNeg opcode case. All six original premises and
complete Error-exempt source-permutation simulation are retained. Frame
equality derives the fixed binary64 FP read and the same finite-map update;
general locals, SSA and next are unchanged. Missing FP reads retain Error
exemption. No target-run/success/post-state premise is added. The Inst/evaluator
boundary inherits reals_as_rational_cuts (SOUNDNESS item 8); these operations
copy or change only the binary64 sign, retaining NaN payloads and infinities. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstFPNeg {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next dst arg : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.inst (.fp (.fpNeg dst arg))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.fp (.fpNeg dst arg))) source target ssa next tables := by
  have same : WordSemStateFiniteExact.getFpVar arg source = WordSemStateFiniteExact.getFpVar arg target := by
    simp_all [WordSemStateFiniteExact.getFpVar, Flapjack.WordAlloc.wordStateEqRel]
  refine ⟨target.permute, ?_⟩
  cases read : WordSemStateFiniteExact.getFpVar arg source <;>
    simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
      WordSemStateFiniteExact.getFpVar, WordSemStateFiniteExact.setFpVar,
      ssaCcTrans, ssaCcTransInst, Flapjack.WordAlloc.wordStateEqRel]

end Flapjack.Compiler.Backend.WordAlloc
