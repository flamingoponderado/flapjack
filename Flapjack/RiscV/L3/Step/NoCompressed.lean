import Flapjack.RiscV.L3.Step.Next

/-! riscv-mi rejects every compressed (RVC) instruction, matching riscv-zkvm,
which models no compressed encodings. Fetch still reads the HOL instruction
length from the low two bits, but every 16-bit parcel decodes to
`UnknownInstruction`, whose handler raises `Illegal_Instr`, so no step that
fetches a compressed parcel succeeds. Branch-specific Flapjack theorems with
no HOL counterpart; the full HOL model decodes RVC instead. -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

/-- Every 16-bit parcel decodes to `UnknownInstruction`. -/
theorem DecodeAny_half_unknown (h : BitVec 16) :
    DecodeAny (.Half h) = .UnknownInstruction := rfl

/-- Running a decoded compressed parcel requests an `Illegal_Instr` trap. -/
theorem Run_DecodeAny_half (h : BitVec 16) (s : riscv_state) :
    NextFetch (Run (DecodeAny (.Half h)) s) =
      some (.Trap { (Flapjack.holArb SynchronousTrap) with
        trap := .Illegal_Instr, badaddr := none }) := by
  simp [DecodeAny_half_unknown, Run, «dfn'UnknownInstruction», signalException, setTrap,
    «write'NextFetch», NextFetch, holUpdate]

/-- No step succeeds after fetching a compressed parcel: whatever the state,
`NextRISCV` yields `none`. -/
theorem NextRISCV_half_none (s fetched : riscv_state) (h : BitVec 16)
    (hfetch : Fetch s = (.Half h, fetched)) :
    NextRISCV s = none := by
  rw [NextRISCV_equation, hfetch]
  dsimp only
  have htrap := Run_DecodeAny_half h fetched
  split
  · rfl
  · rw [htrap]

end Flapjack.RiscV.L3.Step
