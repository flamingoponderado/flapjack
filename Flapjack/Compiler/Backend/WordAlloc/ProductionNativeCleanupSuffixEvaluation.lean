import Flapjack.Compiler.Backend.WordAlloc.ProductionNativeUnreachEvaluation
import Flapjack.Compiler.Backend.WordAlloc.ProductionNativeDeadEvaluation
import Flapjack.Compiler.Backend.WordAlloc.ProductionThreeToTwoIdentity
import Flapjack.Compiler.Backend.WordCopy.Production
import Flapjack.Compiler.Backend.WordCopy.Proofs.Correct
import Flapjack.Compiler.Backend.WordUnreach.ProductionCanonicalImage
import Flapjack.Pancake.Proofs.WordConvs.CopyProp
import Flapjack.Pancake.Proofs.WordConvs.ThreeToTwo
import Flapjack.Pancake.Proofs.WordConvs.Unreach

/-! Executed post-CSE allocator cleanup suffix.

After `wordCseProp`, the executed allocator
(`cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy`, `RiscV/WordDeadCode.lean`)
runs `wordCopyPropViaHOL`, `wordThreeToTwoReg`, `wordRemoveUnreachViaHOL?` and
`wordRemoveDeadProgramViaHOL`, the tail of HOL `compile_single`
(`word_to_wordScript.sml:29-32`: `copy_prop`, `three_to_two_reg_prog`, `remove_unreach`,
`remove_dead_prog`). This module composes the four phases with their original evaluation
theorems. It is Flapjack API infrastructure with no separate HOL original; the preceding
SSA/CSE phases and the production/native evaluator relation are separate obligations. -/

namespace Flapjack.WordAlloc
open WordSemStateFiniteExact Compiler.Backend.WordCopy Compiler.Backend.WordInst
  Compiler.Backend.WordUnreach RiscV
set_option autoImplicit false

/-- Native instruction copy propagation returns `Skip` or an instruction, neither of which
carries a cutset (Flapjack codec infrastructure; no HOL declaration). -/
theorem copyPropInst_setsWf {width : Nat} [NeZero width]
    (i : WordLangInst (BitVec width)) (cs : CopyState) :
    WordAllocatorProgramSetsWf (copyPropInst i cs).1 := by
  unfold copyPropInst
  split <;> simp [WordAllocatorProgramSetsWf]

/-- Native copy propagation keeps every retained cutset field: Call/Alloc/Install/FFI/Loop
cutsets are copied unchanged and the remaining outputs carry none. Flapjack codec
infrastructure; no HOL declaration. -/
theorem copyPropProg_setsWf {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (cs : CopyState)
    (valid : WordAllocatorProgramSetsWf program) :
    WordAllocatorProgramSetsWf (copyPropProg program cs).1 := by
  fun_induction copyPropProg program cs <;> simp_all [WordAllocatorProgramSetsWf, copyPropInst_setsWf]

/-- Native `copy_prop` keeps the canonical cutset image (Flapjack codec infrastructure). -/
theorem copyProp_setsWf {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (valid : WordAllocatorProgramSetsWf program) :
    WordAllocatorProgramSetsWf (copyProp program) := by
  simpa only [copyProp] using copyPropProg_setsWf program emptyEq valid

/-- The executed post-CSE cleanup suffix on an encoded flat source satisfies the complete
original evaluation conclusion. The executed copy output re-encodes literally to
`copy_prop native` (canonical cutsets derived from the source encoder), RISC-V's disabled
`three_to_two_reg_prog F` is the identity, `remove_unreach` and the final
`remove_dead_prog` are evaluated by their original theorems. The only premises are the
original flat convention, the source evaluation and its non-error result; executed phase
success and every intermediate encoding are derived. Flapjack composition; no HOL
original. -/
theorem nativeCleanupSuffix_evaluation {width : Nat} [NeZero width] {C F : Type}
    (source : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (state finalState : WordSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (sourceConditions : flatExpConventions native = true ∧
      evaluate native state = (result, finalState) ∧ result ≠ some .error) :
    ∃ unreached output : WordProg (BitVec width),
      RiscV.wordRemoveUnreachViaHOL? (wordThreeToTwoReg (wordCopyPropViaHOL source)) =
        some unreached ∧
      RiscV.wordRemoveDeadProgramViaHOL unreached = output ∧
      wordLangProgFromHOL
        (removeDeadProg (removeUnreach (threeToTwoRegProg false (copyProp native)))) =
          some output ∧
      ∃ targetLocals : Spt (WordLocW width),
        evaluate (removeDeadProg (removeUnreach (threeToTwoRegProg false (copyProp native))))
            state = (result, {finalState with locals := targetLocals}) ∧
        match (generalizing := false) result with
        | none => True
        | some (.break _) => True
        | some (.continue _) => True
        | some _ => finalState.locals = targetLocals := by
  obtain ⟨flat, run, nonerror⟩ := sourceConditions
  -- copy: literal re-encoding and the original `evaluate_copy_prop`
  obtain ⟨copied, copyDecoded, copyRouted⟩ := wordCopyPropViaHOL_sourceNative source native encoded
  have copyEncoded : wordLangProgToHOL (wordCopyPropViaHOL source) = some (copyProp native) := by
    rw [copyRouted]
    exact canonicalProgram_codec _ copied
      (copyProp_setsWf native (productionProgram_setsWf source native encoded)) copyDecoded
  have copyFlat := WordConvs.flat_exp_conventions_copy_prop native flat
  have copyRun : evaluate (copyProp native) state = (result, finalState) := by
    rw [evaluateCopyProp (by rw [run]; exact nonerror), run]
  -- three-to-two: disabled on RISC-V, literally the identity
  have twoEncoded := wordThreeToTwoReg_nativeDisabled _ _ copyEncoded copyFlat
  have twoFlat := WordConvs.threeToTwoRegProg_flatExpConventions false _ copyFlat
  have twoRun : evaluate (threeToTwoRegProg false (copyProp native)) state =
      (result, finalState) := by
    simpa only [threeToTwoRegProg, Bool.false_eq_true, if_false] using copyRun
  -- unreach: actual output and its literal re-encoding
  obtain ⟨unreached, unreachRouted, unreachEncoded⟩ :=
    executedUnreach_literalImage _ _ twoEncoded
  obtain ⟨unreached', unreachRouted', -, unreachRun⟩ :=
    nativeUnreach_evaluation _ _ twoEncoded state finalState result twoRun nonerror
  rw [unreachRouted] at unreachRouted'
  cases Option.some.inj unreachRouted'
  have unreachFlat := WordConvs.flatExpConventions_removeUnreach _ twoFlat
  -- final dead-code removal
  obtain ⟨output, deadDecoded, deadRouted, targetLocals, deadRun, locals⟩ :=
    nativeDead_evaluation unreached _ unreachEncoded state finalState result
      ⟨unreachFlat, unreachRun, nonerror⟩
  exact ⟨unreached, output, unreachRouted, deadRouted, deadDecoded, targetLocals, deadRun,
    locals⟩

end Flapjack.WordAlloc
