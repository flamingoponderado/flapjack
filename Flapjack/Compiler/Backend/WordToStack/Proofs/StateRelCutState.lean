import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRelRegisterUpdate
namespace Flapjack.WordToStackProofs.StateRelCutState
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
/-- Genuine canonical source codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Genuine canonical target codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original successful-cut law; only the original cut and full relation
premises are retained (original7750–7765). This structural law introduces
no evaluator assumption or independent FP agreement claim. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_cut_state"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelCutState {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source post : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat) (names : Spt Unit)
    (related : stateRel ac k f frame source target lens 0)
    (cut : WordSemStateFiniteExact.cutState (names,.ln) source = some post) :
    stateRel ac k f frame post target lens 0 := by
  by_cases live : LoopSemStateFiniteExact.sptSubsetLive names source.locals
  · by_cases emptyLive : LoopSemStateFiniteExact.sptSubsetLive (Spt.ln : Spt Unit) source.locals
    · simp only [WordSemStateFiniteExact.cutState,wordSemCutEnv,wordSemCutEnvs,
        wordSemCutNames,live,emptyLive,if_true,Option.some.injEq] at cut
      subst post
      unfold stateRel at related ⊢
      obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
        h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,
        h37,h38,hloc⟩ := related
      refine ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
        h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,?_,
        h37,h38,?_⟩
      · exact sptWfUnion _ _ ⟨sptWfInter _ _,sptWfInter _ _⟩
      · intro n v found
        simp only [sptLookup_sptUnion,sptLookup_sptInterCases] at found
        cases original : sptLookup n source.locals <;> simp [original] at found
        next value =>
          cases selected : sptLookup n names <;> simp [selected] at found
          next chosen =>
            exact hloc n v (by simpa [found] using original)
    · simp [WordSemStateFiniteExact.cutState,wordSemCutEnv,wordSemCutEnvs,
        wordSemCutNames,live,emptyLive] at cut
  · simp [WordSemStateFiniteExact.cutState,wordSemCutEnv,wordSemCutEnvs,
      wordSemCutNames,live] at cut
end Flapjack.WordToStackProofs.StateRelCutState
