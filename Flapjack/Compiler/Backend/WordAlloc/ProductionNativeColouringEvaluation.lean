import Flapjack.Compiler.Backend.WordAlloc.ProductionNativeColouringOk

namespace Flapjack.WordAlloc
open RegAlloc RiscV RiscV.CakeRegAlloc Compiler.Encoders.Asm
open WordSemStateFiniteExact
open Compiler.Backend.WordAlloc.Proofs (evenStartingLocals)

open Classical in
/-- This witness uses the executed native-copy (`wordCopyPropViaHOL`) cleanup
consumer. It does not describe the legacy copy-propagation route.

 The actual native SSA allocator's colour phase satisfies the full native
evaluation conclusion, including the source permutation, error alternative,
state relation and non-Break/Continue locals equality. Its actual result and
both program encodings are constructed from the source; the original physical
starting-locals premise is retained. No target run or output colouring validity
is assumed. This has no independent HOL original: simulation of the preceding
SSA/cleanup phases and the production evaluator remains separate work. -/
theorem nativeAllocator_colouringEvaluation {width : Nat} [NeZero width] {C F : Type}
    (label : Nat) (parameters : List Nat) (source : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (supported : allocatorMemorySupported source = true)
    (config : AsmConfigExact width) (target : config.isa = .riscv)
    (st : WordSemStateFiniteExact width C F) (physical : evenStartingLocals st.locals) :
    ∃ (output : CakeAllocationWithColour (BitVec width))
        (nativeOutput colouredNative : WordLangProgHOL (BitVec width)),
      cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy
        wordCopyPropViaHOL wordRemoveDeadProgramViaHOL wordRemoveUnreachViaHOL?
        wordFullSsaCcTransNativeWithState label parameters source = some output ∧
      wordLangProgToHOL output.program = some nativeOutput ∧
      wordLangProgToHOL output.colouredProgram = some colouredNative ∧
      ∃ perm',
        let (res, rst) := evaluate nativeOutput { st with permute := perm' }
        if res = some .error then True
        else
          let (res', rcst) := evaluate colouredNative st
          res = res' ∧ wordStateEqRel rst rcst ∧
            match res with
            | none => True
            | some (.break _) => True
            | some (.continue _) => True
            | some _ => rst.locals = rcst.locals := by
  obtain ⟨output, nativeOutput, allocated, outputEncoded, colouredEncoded, valid⟩ :=
    nativeAllocator_colouringOk label parameters source native encoded supported config target
  obtain ⟨other, otherNative, livein, flivein, allocatedOther, encodedOther,
    _, _, conventions, support, _⟩ :=
    nativeAllocator_colouringContract label parameters source native encoded supported config target
  rw [allocated] at allocatedOther
  cases allocatedOther
  rw [outputEncoded] at encodedOther
  cases encodedOther
  have fixes : ∀ n, isPhyVar n = true → totalColour (sptFromAList output.colouring) n = n := by
    apply totalColour_phys
    intro x v lookup phy
    have domain : sptDomain (sptFromAList output.colouring) x := by simp [sptDomain, lookup]
    have value := (conventions x (support x domain)).2
    rw [if_pos phy] at value
    have lookupValue : spDefault (sptFromAList output.colouring) x = v := by simp [spDefault, lookup]
    rw [lookupValue] at value
    simp only [isPhyVar, decide_eq_true_eq] at phy
    omega
  have post := evaluateApplyColour nativeOutput st st
    (totalColour (sptFromAList output.colouring)) .ln []
    ⟨valid, by simp only [wordStateEqRel, and_self],
      strongLocals_self _ st.locals _ physical fixes⟩
  exact ⟨output, nativeOutput, applyColour (totalColour (sptFromAList output.colouring)) nativeOutput,
    allocated, outputEncoded, colouredEncoded, post_to_goal _ _ _ st rfl post⟩

end Flapjack.WordAlloc
