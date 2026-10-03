import Flapjack.Pancake.LoopToWord.Proofs.NoFP
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.CompHOLImage
import Flapjack.Compiler.Backend.WordAlloc.ProductionNormalizedMemoryGuard

namespace Flapjack.LoopToWord
open WordAlloc

/-- Every exact Loop-to-Word compiler output satisfies the extra actual
allocator memory domain. Ordinary instructions emitted by compHOL use only
Load32/Load8/Store32/Store8; shared operations have their separate carrier.
This universal source-image fact has no HOL original and does not narrow
any HOL compiler correctness theorem or assume a target result. -/
theorem compHOLAllocatorMemoryImage {width : Nat} [NeZero width]
    (context : Spt Nat) (source : HolLoopProg width) (labels : Nat × Nat) :
    nativeMemorySupported (compHOL context source labels).1 = true := by
  fun_induction compHOL context source labels
  case case26 target arguments labels values live =>
    cases labels <;> simp [nativeMemorySupported]
  case case27 target arguments labels values live newLabels exception first second cut
      outFirst labelsFirst hFirst outSecond labelsSecond hSecond ihFirst ihSecond =>
    cases labels
    cases labelsFirst
    cases labelsSecond
    simp_all +zetaDelta [nativeMemorySupported]
  all_goals simp_all [nativeMemorySupported]

/-- The complete exact function wrapper also lies in the actual allocator's
memory domain, with no source or output support premise. -/
theorem compFuncAllocatorMemoryImage {width : Nat} [NeZero width]
    (name : Nat) (parameters : List Nat) (source : HolLoopProg width) :
    nativeMemorySupported (loopToWordCompFuncHOL name parameters source) = true := by
  unfold loopToWordCompFuncHOL
  exact compHOLAllocatorMemoryImage _ source _

/-- Actual decoder support follows from the universal exact compiler image;
the decoder equation binds the output, rather than assuming output support. -/
theorem compFuncDecodedAllocatorMemoryImage {width : Nat} [NeZero width]
    (name : Nat) (parameters : List Nat) (source : HolLoopProg width)
    (output : WordProg (BitVec width))
    (decoded : wordLangProgFromHOL (loopToWordCompFuncHOL name parameters source) = some output) :
    RiscV.allocatorMemorySupported output = true := by
  rw [decodedMemoryGuard _ output decoded]
  exact compFuncAllocatorMemoryImage name parameters source

/-- Every exact function source produces a decodable, re-encodable actual
program in the allocator memory domain. All availability and support facts
are derived from the source, not supplied as target-result assumptions.
Flapjack carrier infrastructure with no HOL original. -/
theorem compFuncAllocatorMemoryDomain {width : Nat} [NeZero width]
    (name : Nat) (parameters : List Nat) (source : HolLoopProg width) :
    ∃ output : WordProg (BitVec width),
      wordLangProgFromHOL (loopToWordCompFuncHOL name parameters source) = some output ∧
      RiscV.allocatorMemorySupported output = true ∧
      (wordLangProgToHOL output).isSome = true := by
  have available : wordLangProgFromHOL (loopToWordCompFuncHOL name parameters source) ≠ none := by
    unfold loopToWordCompFuncHOL
    exact wordLangProgFromHOL_compHOL_ne_none _ source _
  cases decoded : wordLangProgFromHOL (loopToWordCompFuncHOL name parameters source) with
  | none => exact False.elim (available decoded)
  | some output =>
      refine ⟨output, rfl, compFuncDecodedAllocatorMemoryImage name parameters source output decoded, ?_⟩
      have encoded := wordLangProgToHOL_of_fromHOL _ output decoded
      simp [encoded]

end Flapjack.LoopToWord
