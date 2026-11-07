import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileConventions.Output
import Flapjack.Compiler.Backend.WordAlloc.ProductionCallInputs
import Flapjack.Compiler.Backend.RegAlloc.ProductionWrapper
import Flapjack.Compiler.Backend.WordAlloc.ProductionStackOnlyCache
import Flapjack.Compiler.Backend.RegAlloc.Proofs.DoRegAllocCorrect
import Flapjack.RiscV.CakeAllocatorBitsBridge
import Flapjack.RiscV.PipelineDiagnostics
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile

namespace Flapjack.ProductionBitmapTransport
open RiscV Compiler.Backend.WordToStack

/-! Flapjack infrastructure for the executed bitmap carrier. These are not
additional HOL theorem ports. Encoding preserves arbitrary stored counts,
including inconsistent counts; live-cutset and whole-body transport remain open. -/

/-- Full physical-frame to source-bitmap index arithmetic, including the
empty frame and truncating subtraction beyond its bounds. -/
theorem physicalSlot_bitmapIndex (slots distance : Nat) :
    ((if slots = 0 then 0 else slots + 1) - 1 - distance) - 1 =
      slots - 1 - distance := by
  split <;> omega

/-- Source-shaped allocator input after full SSA and all six cleanup stages.
This is a composition of existing executable definitions, with no independent
HOL original. Production codec transport of this complete expression remains
a separate step; no output convention is assumed. -/
def nativeAllocatorInput {width : Nat} [NeZero width] (count : Nat) (two : Bool)
    (program : WordLangProgHOL (BitVec width)) : WordLangProgHOL (BitVec width) :=
  WordAlloc.removeDeadProg (Compiler.Backend.WordUnreach.removeUnreach (Compiler.Backend.WordInst.threeToTwoRegProg two
    (Compiler.Backend.WordCopy.copyProp (Compiler.Backend.WordCse.wordCommonSubexpElim
      (WordAlloc.removeDeadProg (Compiler.Backend.WordAlloc.fullSsaCcTrans count program))))))

/-- Original unconditional full SSA convention and every cleanup preservation
law discharge the complete allocator-input stack convention, for arbitrary
source programs and either three-to-two mode. -/
theorem nativeAllocatorInput_preConventions {width : Nat} [NeZero width]
    (count : Nat) (two : Bool) (program : WordLangProgHOL (BitVec width))
    (config : Compiler.Encoders.Asm.AsmConfigExact width) :
    preAllocConventionsHOL (nativeAllocatorInput count two program) = true := by
  unfold nativeAllocatorInput
  apply (WordConvs.removeDeadProgConventions (fun _ => true) _ config).2.2.1
  apply WordConvs.preAllocConventions_removeUnreach
  apply WordConvs.threeToTwoRegProg_preAllocConventions
  apply WordConvs.pre_alloc_conventions_copy_prop
  apply Compiler.Backend.WordCse.pre_alloc_conventions_word_common_subexp_elim
  apply (WordConvs.removeDeadProgConventions (fun _ => true) _ config).2.2.1
  exact WordAlloc.fullSsaCcTrans_preAllocConventions _ _

end Flapjack.ProductionBitmapTransport
