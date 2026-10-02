import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticControl

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticPrimitiveWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticPrimitiveWitnesses

/-- Full original resumed semantic Skip case. All six original premises
and the full existential source-permutation/result/frame/result-sensitive
locals conclusion are retained. Skip preserves the complete original locals relation.
No target evaluation, successful-clock or post-state relation is assumed. The
full evaluator inherits reals_as_rational_cuts (SOUNDNESS item 8); this case
executes no FP operation. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectSkip {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.skip : WordLangProgHOL (BitVec width)) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation .skip source target ssa next tables := by
  refine ⟨target.permute, ?_⟩
  simpa [WordSemStateFiniteExact.evaluate, ssaCcTrans,
    Flapjack.WordAlloc.wordStateEqRel] using ⟨h.1, h.2.1⟩

/-- Full original resumed semantic Tick case. All six original premises
and the full existential source-permutation/result/frame/result-sensitive
locals conclusion are retained. Both zero-clock timeout/flush and positive-clock decrement paths are derived from the original frame.
No target evaluation, successful-clock or post-state relation is assumed. The
full evaluator inherits reals_as_rational_cuts (SOUNDNESS item 8); this case
executes no FP operation. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectTick {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.tick : WordLangProgHOL (BitVec width)) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation .tick source target ssa next tables := by
  refine ⟨target.permute, ?_⟩
  have clock : target.clock = source.clock := by
    rcases h.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, same, _, _, _, _, _, _, _, _⟩
    exact same
  by_cases zero : source.clock = 0
  · simp_all [WordSemStateFiniteExact.evaluate, ssaCcTrans,
      WordSemStateFiniteExact.flushState, Flapjack.WordAlloc.wordStateEqRel]
  · simp_all [WordSemStateFiniteExact.evaluate, ssaCcTrans,
      WordSemStateFiniteExact.decClock, Flapjack.WordAlloc.wordStateEqRel]

end Flapjack.Compiler.Backend.WordAlloc
