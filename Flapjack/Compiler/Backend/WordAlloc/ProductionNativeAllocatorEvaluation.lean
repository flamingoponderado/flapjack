import Flapjack.Compiler.Backend.WordAlloc.ProductionNativeCleanupChainEvaluation
import Flapjack.Compiler.Backend.WordAlloc.ProductionNativeColouringEvaluation
import Flapjack.Compiler.Backend.WordAlloc.ProductionNativeSSAEvaluation
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingle
import Flapjack.Pancake.Proofs.WordConvs.SSAFlatFull

/-! Whole executed allocator stage.

The executed allocator `cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy`
(`RiscV/WordDeadCode.lean`) runs the SSA producer, the cleanup chain and register
colouring: the `full_ssa_cc_trans` .. `word_alloc` segment of HOL `compile_single`
(`word_to_wordScript.sml:26-33`). This module composes `nativeSsa`, the cleanup chain
(`nativeCleanupChain_evaluation`) and `nativeAllocator_colouringEvaluation` into one
evaluation theorem for the executed stage, in the shape HOL `compile_single_correct`
composes those passes. It is Flapjack API infrastructure with no separate HOL original;
the preceding `word_simp`/`inst_select` stages and the production/native evaluator relation
are separate obligations. -/

namespace Flapjack.WordAlloc
open WordSemStateFiniteExact Compiler.Backend.WordCopy Compiler.Backend.WordInst
  Compiler.Backend.WordUnreach Compiler.Backend.WordCse RiscV RiscV.CakeRegAlloc
  Compiler.Encoders.Asm Compiler.Backend.WordAlloc
open Compiler.Backend.WordAlloc.Proofs (evenStartingLocals)
set_option autoImplicit false

/-- A successful executed allocator run retains, as its program, the final dead-code
output of the cleanup chain applied to its SSA producer's result (Flapjack structural
fact about the executed definition; no HOL declaration). -/
theorem allocatorWithSsaAndCopy_program {α : Type} [OfNat α 0] [WordCseHash α] [BEq α]
    (copy dead : WordProg α → WordProg α) (unreach : WordProg α → Option (WordProg α))
    (ssaProducer : Nat → WordProg α → Option (WordSsaState × List Nat × WordProg α))
    (label : Nat) (parameters : List Nat) (program : WordProg α)
    (output : CakeAllocationWithColour α)
    (allocated : cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy copy dead unreach
      ssaProducer label parameters program = some output) :
    ∃ (ssaOutput : WordSsaState × List Nat × WordProg α) (unreached : WordProg α),
      ssaProducer parameters.length program = some ssaOutput ∧
      unreach (wordThreeToTwoReg (copy (wordCseProp (dead ssaOutput.2.2)))) = some unreached ∧
      output.program = dead unreached := by
  unfold cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy at allocated
  split at allocated
  · simp at allocated
  · simp only [Option.bind_eq_some_iff] at allocated
    obtain ⟨ssaOutput, produced, rest⟩ := allocated
    split at rest
    · simp at rest
    · cases reached : unreach (wordThreeToTwoReg (copy (wordCseProp (dead ssaOutput.2.2)))) with
      | none => simp [reached] at rest
      | some unreached =>
        refine ⟨ssaOutput, unreached, produced, reached, ?_⟩
        simp only [reached] at rest
        split at rest
        · simp at rest
        · split at rest
          · simp at rest
          · split at rest
            · simp at rest
            · simp only [Option.some.injEq] at rest
              rw [← rest]

/-- SSA's starting-locals domain (`even_list`) consists of physical variables, as the
colouring theorem's `even_starting_locals` premise requires (Flapjack infrastructure). -/
theorem evenStartingLocals_of_evenList {width : Nat} [NeZero width]
    (locals : Spt (WordLocW width)) (count : Nat)
    (domain : sptDomain locals = (fun key => key ∈ evenList count)) :
    evenStartingLocals locals := by
  intro key member
  rw [domain] at member
  simp only [evenList, List.mem_map, List.mem_range] at member
  obtain ⟨index, -, rfl⟩ := member
  simp [Flapjack.isPhyVar]

open Classical in
/-- The whole executed allocator stage satisfies the native evaluation conclusion that HOL
`compile_single_correct` composes for `full_ssa_cc_trans` .. `word_alloc`: on an encoded
flat source and a starting state whose locals domain is `even_list (LENGTH parameters)`,
the executed allocator succeeds, its coloured program is encoded, and for some
permutation the source run either errors or agrees with the coloured run on the result,
the `word_state_eq_rel` fields and, for returning results, the locals. The colouring
theorem's executed memory guard is retained; allocator success, every intermediate
encoding and each phase relation are derived. Flapjack composition; no HOL original. -/
theorem nativeAllocator_evaluation {width : Nat} [NeZero width] {C F : Type}
    (label : Nat) (parameters : List Nat) (source : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (supported : allocatorMemorySupported source = true)
    (config : AsmConfigExact width) (target : config.isa = .riscv)
    (flat : flatExpConventions native = true)
    (st : WordSemStateFiniteExact width C F)
    (domain : sptDomain st.locals = (fun key => key ∈ evenList parameters.length)) :
    ∃ (output : CakeAllocationWithColour (BitVec width))
        (colouredNative : WordLangProgHOL (BitVec width)),
      cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy
        wordCopyPropViaHOL wordRemoveDeadProgramViaHOL wordRemoveUnreachViaHOL?
        wordFullSsaCcTransNativeWithState label parameters source = some output ∧
      wordLangProgToHOL output.colouredProgram = some colouredNative ∧
      ∃ permutation : Nat → Nat → Nat,
        let sourceRun := evaluate native {st with permute := permutation}
        if sourceRun.1 = some .error then True else
          let targetRun := evaluate colouredNative st
          sourceRun.1 = targetRun.1 ∧ wordStateEqRel sourceRun.2 targetRun.2 ∧
            match sourceRun.1 with
            | none => True
            | some (.break _) => True
            | some (.continue _) => True
            | some _ => sourceRun.2.locals = targetRun.2.locals := by
  -- colouring phase at the original state
  obtain ⟨output, nativeOutput, colouredNative, allocated, outputEncoded, colouredEncoded,
    colourPermutation, colourPost⟩ :=
    nativeAllocator_colouringEvaluation label parameters source native encoded supported
      config target st (evenStartingLocals_of_evenList st.locals parameters.length domain)
  -- the retained program is the cleanup chain on the SSA producer's output
  obtain ⟨ssaOutput, unreached, produced, reached, programEq⟩ :=
    allocatorWithSsaAndCopy_program _ _ _ _ _ _ _ _ allocated
  have producedNative : wordFullSsaCcTransNativeWithStateFromHOL parameters.length native =
      some ssaOutput := by
    simpa only [wordFullSsaCcTransNativeWithState, encoded, Option.bind_some] using produced
  have ssaEncoded := nativeSsaDecodedProgram_literal parameters.length source native encoded
    ssaOutput producedNative
  have ssaFlat := fullSsaCcTrans_flatExpConventions native parameters.length flat
  -- SSA at the colouring phase's permuted state
  let permuted : WordSemStateFiniteExact width C F := {st with permute := colourPermutation}
  obtain ⟨permutation, ssaPost⟩ :=
    fullSsaCcTransCorrect native permuted parameters.length (by simpa only [permuted] using domain)
  refine ⟨output, colouredNative, allocated, colouredEncoded, permutation, ?_⟩
  have restate : ({permuted with permute := permutation} : WordSemStateFiniteExact width C F) =
      {st with permute := permutation} := rfl
  simp only [restate] at ssaPost
  simp only
  rcases sourceRun : evaluate native {st with permute := permutation} with
    ⟨sourceResult, sourceFinal⟩
  rw [sourceRun] at ssaPost
  simp only at ssaPost ⊢
  split
  · trivial
  rename_i nonerror
  rw [if_neg nonerror] at ssaPost
  rcases ssaRun : evaluate (fullSsaCcTrans parameters.length native) permuted with
    ⟨ssaResult, ssaFinal⟩
  rw [ssaRun] at ssaPost
  obtain ⟨sameResult, ssaRel, ssaLocals⟩ := ssaPost
  subst sameResult
  -- the cleanup chain on the SSA output
  obtain ⟨unreached', cleaned, reached', deadRouted, cleanedDecoded, cleanLocals, cleanRun,
    cleanSame⟩ := nativeCleanupChain_evaluation ssaOutput.2.2 _ ssaEncoded permuted ssaFinal
      sourceResult ⟨ssaFlat, ssaRun, nonerror⟩
  rw [reached] at reached'
  cases Option.some.inj reached'
  have chainWf := removeDeadProg_setsWf _ (removeUnreach_setsWf _ (copyProp_setsWf _
    (wordCommonSubexpElim_setsWf _ (removeDeadProg_setsWf _
      (productionProgram_setsWf _ _ ssaEncoded)))))
  have chainEncoded := canonicalProgram_codec _ cleaned
    (by simpa only [threeToTwoRegProg, Bool.false_eq_true, if_false] using chainWf) cleanedDecoded
  rw [← deadRouted, ← programEq, outputEncoded] at chainEncoded
  cases Option.some.inj chainEncoded
  -- colouring post-condition at the cleaned program's run
  rw [show ({st with permute := colourPermutation} : WordSemStateFiniteExact width C F) =
    permuted from rfl, cleanRun] at colourPost
  simp only [if_neg nonerror] at colourPost
  rcases colourRun : evaluate colouredNative st with ⟨colourResult, colourFinal⟩
  rw [colourRun] at colourPost
  obtain ⟨sameColour, colourRel, colourLocals⟩ := colourPost
  refine ⟨sameColour, ?_, ?_⟩
  · exact Compiler.Backend.WordToWord.wordStateEqRel_trans ssaRel (by simpa [wordStateEqRel] using colourRel)
  · cases sourceResult with
    | none => trivial
    | some value =>
      cases value <;> simp_all

end Flapjack.WordAlloc
