import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticSeq
import Flapjack.Compiler.Backend.Semantics.WordSem.Env

namespace Flapjack.Compiler.Backend.WordAlloc

namespace LoopSemanticHelperWitnesses

/-- Canonical roundtrip of the imported native finite-map state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end LoopSemanticHelperWitnesses

/-- Full original local sequence-collapse lemma. The sole premise is the
successful first evaluation; the native evaluator's fix_clock law supplies
exact continuation execution without a new clock/frame premise. Inherits the
evaluator reals_as_rational_cuts assumption, SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_seq_collapse"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem evaluateSeqCollapse {width : Nat} [NeZero width] {C F : Type}
    (first second : WordLangProgHOL (BitVec width))
    (source after : WordSemStateFiniteExact width C F)
    (run : WordSemStateFiniteExact.evaluate first source = (none,after)) :
    WordSemStateFiniteExact.evaluate (.seq first second) source =
      WordSemStateFiniteExact.evaluate second after := by
  simp only [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.fix_clock_evaluate]
  rw [run]

/-- Full original local empty-tree cut identity. The mapping function keeps
its arbitrary Nat/Unit pair type; no tree validity or successful cut is assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "cut_env_fromAList_LN"]
theorem cutEnvFromAListLN {α : Type} (names : Spt Unit) (locals : Spt α)
    (map : Nat × Unit → Nat × Unit) :
    wordSemCutEnv (names,sptFromAList ((sptToAList (.ln : Spt Unit)).map map)) locals =
      wordSemCutEnv (names,.ln) locals := by
  simp [sptFromAList]

end Flapjack.Compiler.Backend.WordAlloc
