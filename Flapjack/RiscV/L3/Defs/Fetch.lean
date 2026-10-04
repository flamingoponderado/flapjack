import Flapjack.RiscV.L3.Defs
import Flapjack.RiscV.L3.Defs.MMU.Translate
import Flapjack.RiscV.L3.Defs.ReadInst
namespace Flapjack.RiscV.L3

/-- Integer-only fetch delta; differs from HOL by removing floating-point data. -/
noncomputable def Fetch (_u_ : Unit) (state : riscv_state) : FetchResult × riscv_state :=
  let pc := PC state
  if pc.getLsbD 0 then (.F_Error (.Internal (.FETCH_MISALIGNED pc)), state)
  else
    let (address, state) := translateAddr (pc, .Instruction, .Read) state
    match address with
    | none => (.F_Error (.Internal (.FETCH_FAULT pc)), state)
    | some address =>
      let (raw, state) := rawReadInst address state
      let delta : StateDelta :=
        { (Delta state) with
          exc_taken := false
          fetch_exc := false
          pc := pc
          rinstr := raw
          addr := none
          data1 := none
          data2 := none
          st_width := none }
      (.F_Result raw, «write'Delta» delta state)

end Flapjack.RiscV.L3
