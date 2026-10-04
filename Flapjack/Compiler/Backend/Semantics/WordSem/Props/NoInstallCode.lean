import Flapjack.Pancake.WordConvs.NoInstall
import Flapjack.Misc.Sptree
namespace Flapjack
namespace WordProps

/-- Literal source code-map convention on arbitrary Spt trees and entries.
The word dimension is the only representation translation; the tree carrier
and lookup are the reviewed HOL constructor-for-constructor port. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def noInstallCode {width : Nat} [NeZero width]
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) : Prop :=
  ∀ (key argumentCount : Nat) (program : WordLangProgHOL (BitVec width)),
    sptLookup key code = some (argumentCount,program) → noInstallSubprogsHOL program = true
end WordProps
end Flapjack
