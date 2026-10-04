import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSAAllocation
import Flapjack.Compiler.Backend.WordCopy.Production

namespace Flapjack.RiscV.CakeRegAlloc

/-- Executed fixed-width full SSA route. The source codec image executes native
setup and body renaming, then the shared cleanup/IRC consumer. The broader Word
extension retains its historical behavior on encoder rejection. Native output
acceptance is proved by the codec closure, not used as a fallback condition.

The rejected-input branch is a raw `WordProg` API extension, outside the original
HOL instruction carrier: `WordProgCarrierCodec.codecDomain` identifies rejection
exactly with a nested five-register `.addCarry` (including either optional Call
body). The four-position `.cakeAddCarry` is codec-accepted. No original HOL
correctness or final output codec guarantee is asserted for that extension,
even when legacy cleanup later removes its unsupported instruction. The branch
is preserved for historical raw-Word clients. `ProductionWordRemoveCaller` proves
that actual `panToWordCompileProg` source rows select the native branch without
assuming allocation success; its public caller theorem distinguishes real
allocator failure from the unreachable source cleanup-codec error. -/
def cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy
    {width : Nat} [NeZero width] (currentFunction : Nat)
    (parameters : List Nat) (program : WordProg (BitVec width)) :
    Option (WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState) :=
  match wordLangProgToHOL program with
  | none => cakeAllocateWordFunctionAfterDead currentFunction parameters program
  | some native =>
      (cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy wordCopyPropViaHOL wordRemoveDeadProgramViaHOL
      wordRemoveUnreachViaHOL?
        (fun count _ => wordFullSsaCcTransNativeWithStateFromHOL count native)
        currentFunction parameters program).map CakeAllocationWithColour.toLegacy


end Flapjack.RiscV.CakeRegAlloc
