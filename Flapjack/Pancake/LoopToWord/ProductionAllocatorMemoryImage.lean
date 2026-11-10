module

public import Flapjack.Pancake.LoopToWord.Proofs.NoFP
public import Flapjack.Compiler.Backend.WordAlloc.ProductionMemoryGuard

@[expose] public section

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

end Flapjack.LoopToWord
