module

public import Flapjack.Compiler.Backend.LabToTarget.SectionNopEncoding

@[expose] public section

/-!
# Shared LabToTarget section-alignment fixtures

The `enc`/`shortenc` encoders and the two non-aligned-line rows shared by
`Flapjack/Test/LabToTargetSectionAligned0NopParity.lean` and
`Flapjack/Test/LabToTargetSectionAlignedNopParity.lean`. `enc` writes the word
twice; `shortenc` writes `skip` as `[0,0]` and everything else as `[7]`.
-/

namespace Flapjack.Test.Fixtures.LabToTargetSectionNop

open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

def enc : HolAsm 8 → List (BitVec 8)
  | .jump w => [w,w]
  | .jumpCmp _ _ _ w => [w,w]
  | .loc _ w => [w,w]
  | _ => [0,0]

def shortenc : HolAsm 8 → List (BitVec 8)
  | .inst .skip => [0,0]
  | _ => [7]

/-- A `halt` line with odd byte count is encoded but not aligned. -/
theorem haltLineNotAligned :
    lineEncd shortenc .ln [] 7 (.labAsm .halt 77 [7] 4) ∧
    ¬lineAligned (width := 8) 2 (.labAsm .halt 77 [7] 4) ∧
    ¬lineEncWithNop shortenc .ln [] 7 (.labAsm .halt 77 (padBytes [7] 4 [0,0]) 4) := by
  simp only [lineEncd,lineAligned,lineLen,lineLength,lineEncWithNop,encWithNop]
  decide +kernel

/-- A `jump` line with odd byte count is encoded but not aligned. -/
theorem jumpLineNotAligned :
    lineEncd enc .ln [] 7 (.labAsm (.jump (.lab 1 2)) 77 [249,249] 3) ∧
    ¬lineAligned (width := 8) 2 (.labAsm (.jump (.lab 1 2)) 77 [249,249] 3) ∧
    ¬lineEncWithNop enc .ln [] 7 (.labAsm (.jump (.lab 1 2)) 77 (padBytes [249,249] 3 [0,0]) 3) :=
        by
  simp only [lineEncd,lineAligned,lineLen,lineLength,lineEncWithNop,encWithNop]
  decide +kernel

end Flapjack.Test.Fixtures.LabToTargetSectionNop
