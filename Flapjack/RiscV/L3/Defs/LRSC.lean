import Flapjack.RiscV.L3.Defs.IntegerLoadMode
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

/-- Literal source7506-7554: complete LR_D; full order/register payloads retained.
The original mode test precedes address calculation and forwards its returned
state to illegal-instruction, low3 alignment and Data/Read translation routes.
Success reads the entire returned-state word64, writes GPR, then reserves the
original virtual address. No alignment/mode/success/core premise is added. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'LR_D_def"]
noncomputable def «dfn'LR_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × (BitVec 5))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, rs1))) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((let v_1 : (BitVec 64) := (GPR rs1 s); (if ((!(((holWordExtract 3 2 0 v_1) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v_1) s)) else ((match (translateAddr ((v_1, (fetchType.Data, accessType.Read))) s) with | (v0, s_1) => (match v0 with | none => (signalAddressException (ExceptionType.Load_Fault, v_1) s_1) | some pAddr => («write'ReserveLoad» (some v_1) ((«write'GPR» (((rawReadData pAddr s_1), rd)) s_1))))))))))))

/-- Flapjack-only unconditional complete-state normal form; no separately named
HOL theorem is claimed and no original branch is removed. -/
theorem lrDWholeState (aq rl : BitVec 1) (rd rs : BitVec 5) (s : riscv_state) :
    «dfn'LR_D» (aq,rl,rd,rs) s =
    let (is32,t) := in32BitMode () s
    if is32 then signalException .Illegal_Instr t else
    let v := GPR rs t
    if !(holWordExtract 3 2 0 v == BitVec.ofNat 3 0) then
      signalAddressException (.AMO_Misaligned,v) t
    else
      let (addr,u) := translateAddr (v,fetchType.Data,accessType.Read) t
      match addr with
      | none => signalAddressException (.Load_Fault,v) u
      | some p => «write'ReserveLoad» (some v)
          («write'GPR» (rawReadData p u,rd) u) := by
  rfl

/-- Literal source7555-7607: full order/register payloads and arbitrary native
state. Low2 virtual alignment is tested before reservation; a failed reservation
writes GPR1 without translation or clearing the reservation. The original
translation is Data/Read (not modern-ISA Write); failure raises Store_AMO_Fault
with original virtual address on the returned state. Success reads rs2 from
that returned state, writes four bytes, then GPR0, then clears its reservation.
No alignment/reservation/success/core premise or preferred THE NONE is added. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SC_W_def"]
noncomputable def «dfn'SC_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((if ((!(matchLoadReservation v state))) then ((«write'GPR» (((BitVec.ofNat 64 1), rd)) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Read))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => («write'ReserveLoad» ((none : (Option (BitVec 64)))) ((«write'GPR» (((BitVec.ofNat 64 0), rd)) ((rawWriteData ((pAddr, (((GPR rs2 s), 4)))) s)))))))))))))

/-- Flapjack-only whole-state normal form; all original ordered clauses remain
and no standalone HOL theorem is claimed. -/
theorem scWWholeState (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5) (s : riscv_state) :
    «dfn'SC_W» (aq,rl,rd,rs1,rs2) s =
    let v := GPR rs1 s
    if !(holWordExtract 2 1 0 v == BitVec.ofNat 2 0) then
      signalAddressException (.AMO_Misaligned,v) s
    else if !(matchLoadReservation v s) then «write'GPR» (1,rd) s
    else
      let (addr,t) := translateAddr (v,fetchType.Data,accessType.Read) s
      match addr with
      | none => signalAddressException (.Store_AMO_Fault,v) t
      | some p => «write'ReserveLoad» none
          («write'GPR» (0,rd) (rawWriteData (p,GPR rs2 t,4) t)) := by
  rfl

/-- Literal source7608-7672: full order/register payloads and arbitrary native
state. Original mode rejection comes first and forwards its returned state to
all subsequent routes: virtual low3 AMO_Misaligned, reservation failure GPR1
without translation/clear, then literal Data/Read translation. Fault retains
returned translation state and original virtual address; success reads rs2
there, writes eight bytes, writes GPR0, then clears the current reservation.
No mode/alignment/reservation/success/core premise; THE NONE stays unspecified. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'SC_D_def"]
noncomputable def «dfn'SC_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (match (in32BitMode () state) with | (v, s) => (if v then (signalException ExceptionType.Illegal_Instr s) else ((let v_1 : (BitVec 64) := (GPR rs1 s); (if ((!(((holWordExtract 3 2 0 v_1) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v_1) s)) else ((if ((!(matchLoadReservation v_1 s))) then ((«write'GPR» (((BitVec.ofNat 64 1), rd)) s)) else ((match (translateAddr ((v_1, (fetchType.Data, accessType.Read))) s) with | (v0, s_1) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v_1) s_1) | some pAddr => («write'ReserveLoad» ((none : (Option (BitVec 64)))) ((«write'GPR» (((BitVec.ofNat 64 0), rd)) ((rawWriteData ((pAddr, (((GPR rs2 s_1), 8)))) s_1))))))))))))))))

/-- Flapjack-only unconditional complete-state normal form; no standalone HOL
original theorem is claimed and all source ordered branches are retained. -/
theorem scDWholeState (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5) (s : riscv_state) :
    «dfn'SC_D» (aq,rl,rd,rs1,rs2) s =
    let (is32,t) := in32BitMode () s
    if is32 then signalException .Illegal_Instr t else
    let v := GPR rs1 t
    if !(holWordExtract 3 2 0 v == BitVec.ofNat 3 0) then
      signalAddressException (.AMO_Misaligned,v) t
    else if !(matchLoadReservation v t) then «write'GPR» (1,rd) t
    else
      let (addr,u) := translateAddr (v,fetchType.Data,accessType.Read) t
      match addr with
      | none => signalAddressException (.Store_AMO_Fault,v) u
      | some p => «write'ReserveLoad» none
          («write'GPR» (0,rd) (rawWriteData (p,GPR rs2 u,8) u)) := by
  rfl

end Flapjack.RiscV.L3
