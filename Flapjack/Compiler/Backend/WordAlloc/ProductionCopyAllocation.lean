import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSAAllocation
import Flapjack.Compiler.Backend.WordCopy.Production

namespace Flapjack.RiscV.CakeRegAlloc

/-- Executed fixed-width full SSA route. The source codec image executes native
setup and body renaming, then the shared cleanup/IRC consumer. The broader Word
extension retains its historical behavior on encoder rejection. Native output
acceptance is proved by the codec closure, not used as a fallback condition. -/
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
