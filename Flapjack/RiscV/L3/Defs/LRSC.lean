import Flapjack.RiscV.L3.Defs.Reservation
import Flapjack.RiscV.L3.Defs.AddressException
import Flapjack.RiscV.L3.Defs.MMU.Translate
namespace Flapjack.RiscV.L3

/-- Literal source7463-7505: full word1 aq/rl and word5 rd/rs1 arguments,
arbitrary native state. The original unused aq/rl payloads remain present.
Misaligned virtual addresses signal AMO_Misaligned before translation; aligned
addresses use Data/Read. Failure retains the returned translation state and
original virtual address. Success reads that returned state's low32 signed word,
writes GPR there, then reserves the virtual address on that same resulting state.
No core/alignment/success premise; no whole atomic/Run/Next correctness claim. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'LR_W_def"]
noncomputable def «dfn'LR_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × (BitVec 5))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, rs1))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Read))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v) s) | some pAddr => («write'ReserveLoad» (some v) ((«write'GPR» ((((BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s))))), rd)) s)))))))))

/-- Flapjack-only whole-state normal form of the literal equation; no separate
HOL theorem is claimed. It retains every branch without a premise. -/
theorem lrWWholeState (aq rl : BitVec 1) (rd rs : BitVec 5) (s : riscv_state) :
    «dfn'LR_W» (aq,rl,rd,rs) s =
    let v := GPR rs s
    if !(holWordExtract 2 1 0 v == BitVec.ofNat 2 0) then
      signalAddressException (.AMO_Misaligned,v) s
    else
      let (addr,t) := translateAddr (v,fetchType.Data,accessType.Read) s
      match addr with
      | none => signalAddressException (.Load_Fault,v) t
      | some p => «write'ReserveLoad» (some v)
          («write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 (rawReadData p t)),rd) t) := by
  rfl

end Flapjack.RiscV.L3
