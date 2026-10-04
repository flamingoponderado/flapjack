import Flapjack.Compiler.Backend.WordAlloc.ProductionNativeColouringContract
import Flapjack.Compiler.Backend.WordAlloc.ProductionAllocatorSetWF
import Flapjack.Compiler.Backend.WordAlloc.Proofs.WordAllocCorrect

namespace Flapjack.WordAlloc
open RegAlloc RiscV RiscV.CakeRegAlloc Compiler.Encoders.Asm

/-- The source codec's established canonical-set invariant implies HOL's
cutset well-formedness. This is Flapjack proof factoring, not a separate port. -/
theorem allocatorSetsWf_cutsets {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width))
    (valid : WordAllocatorProgramSetsWf program) : wfCutsets program := by
  fun_induction WordAllocatorProgramSetsWf program <;>
    simp_all [wfCutsets, wfNames, StackOnlySetsWf]
  case case8 =>
    split at valid <;> simp_all [wfCutsets]
    split at valid <;> simp_all [wfCutsets, wfNames]

/-- The actual native SSA allocator returns a colouring valid for its actual
cleanup program. Cutset validity is derived from that program's real encoder;
checker success is derived from native allocation. Neither is assumed as an
output property. This has no separate HOL original; full state/evaluation
simulation remains the original semantic theorem's obligation. -/
theorem nativeAllocator_colouringOk {width : Nat} [NeZero width]
    (label : Nat) (parameters : List Nat) (source : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (supported : allocatorMemorySupported source = true)
    (config : AsmConfigExact width) (target : config.isa = .riscv) :
    ∃ (output : CakeAllocationWithColour (BitVec width))
        (nativeOutput : WordLangProgHOL (BitVec width)),
      cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy
        wordCopyPropViaHOL wordRemoveDeadProgramViaHOL wordRemoveUnreachViaHOL?
        wordFullSsaCcTransNativeWithState label parameters source = some output ∧
      wordLangProgToHOL output.program = some nativeOutput ∧
      wordLangProgToHOL output.colouredProgram =
        some (applyColour (totalColour (sptFromAList output.colouring)) nativeOutput) ∧
      colouringOk (totalColour (sptFromAList output.colouring)) nativeOutput .ln [] := by
  obtain ⟨output, nativeOutput, livein, flivein, allocated, outputEncoded,
    colouredEncoded, checked, conventions, support, forced⟩ :=
    nativeAllocator_colouringContract label parameters source native encoded supported config target
  have wf := allocatorSetsWf_cutsets nativeOutput
    (productionProgram_setsWf output.program nativeOutput outputEncoded)
  have empty : ∀ x, ¬ sptDomain (.ln : NumSet) x := by
    intro x h
    simp [sptDomain, sptLookup] at h
  have image : ∀ (f : Nat → Nat), sptDomain (.ln : NumSet) =
      (fun y => ∃ x, sptDomain (.ln : NumSet) x ∧ f x = y) := by
    intro f
    funext y
    apply propext
    exact ⟨fun h => absurd h (empty y), fun ⟨x, hx, _⟩ => absurd hx (empty x)⟩
  have injective : ∀ a b : Nat, (fun x => 2 * x) a = (fun x => 2 * x) b → a = b := by
    intro a b h
    simp only at h
    omega
  have doubled := checkClashTreeInj (getClashTree nativeOutput [])
    (spDefault (sptFromAList output.colouring)) (fun x => 2 * x)
    .ln .ln .ln ⟨injective, image _⟩
  rw [checked] at doubled
  obtain ⟨mappedLive, doubledCheck, _⟩ := doubled
  rw [← totalColourAlt] at doubledCheck
  have valid := (clashTreeColouringOk nativeOutput []
    (totalColour (sptFromAList output.colouring)) .ln .ln livein mappedLive
    ⟨wf, rfl, (fun _ h => by cases h), image _,
      (fun a _ ha => absurd ha (empty a)), doubledCheck⟩).2.2.1
  exact ⟨output, nativeOutput, allocated, outputEncoded, colouredEncoded, valid⟩

end Flapjack.WordAlloc
