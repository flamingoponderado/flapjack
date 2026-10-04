import Flapjack.Compiler.Backend.LabToTarget.Native

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabToTarget
/-- HOL pre-encoding predicate; caches and lengths are not inspected. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def lineOkPreHOL {width : Nat} [NeZero width] (config : AsmConfigExact width) :
    LabLineHOL width → Prop
  | .asm instruction _ _ => asmOkExact (cbwToAsmHOL instruction) config = true
  | _ => True

/-- HOL EVERY over the actual section line list. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def secOkPreHOL {width : Nat} [NeZero width] (config : AsmConfigExact width)
    (sectionData : Section (LabLineHOL width)) : Prop :=
  ∀ line ∈ sectionData.lines, lineOkPreHOL config line

-- Untagged infrastructure for the HOL overload, which has no declaration name.
def allEncOkPreHOL {width : Nat} [NeZero width] (config : AsmConfigExact width)
    (sections : List (Section (LabLineHOL width))) : Prop :=
  ∀ sectionData ∈ sections, secOkPreHOL config sectionData
end Flapjack.Compiler.Backend.LabProps
