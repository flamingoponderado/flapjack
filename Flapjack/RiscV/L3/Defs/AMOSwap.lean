import Flapjack.RiscV.L3.Defs.IntegerStore
namespace Flapjack.RiscV.L3

/-- Literal original AMOSWAP equation over the full native state. Virtual
alignment precedes Data/Write translation. The store operand is read from the
translation state before the destination register receives the old memory value;
this preserves rs2=rd behavior. No architecture or success premise is added. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOSWAP_W_def"]
noncomputable def «dfn'AMOSWAP_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (rawWriteData ((pAddr, (((GPR rs2 s), 4)))) ((«write'GPR» ((((BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s))))), rd)) s)))))))))

/-- Literal original AMOSWAP equation over the full native state. Virtual
alignment precedes Data/Write translation. The store operand is read from the
translation state before the destination register receives the old memory value;
this preserves rs2=rd behavior. No architecture or success premise is added. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOSWAP_D_def"]
noncomputable def «dfn'AMOSWAP_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 3 2 0 v) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (rawWriteData ((pAddr, (((GPR rs2 s), 8)))) ((«write'GPR» (((rawReadData pAddr s), rd)) s)))))))))


/-- Flapjack-only unconditional whole-state normal form for the complete
source equation; this helper has no separately named HOL declaration. -/
theorem amoSwapWWholeState (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5)
    (s : riscv_state) :
    «dfn'AMOSWAP_W» (aq,rl,rd,rs1,rs2) s =
    let v := GPR rs1 s
    if !(holWordExtract 2 1 0 v == BitVec.ofNat 2 0) then
      signalAddressException (.AMO_Misaligned,v) s
    else
      let (addr,t) := translateAddr (v,fetchType.Data,accessType.Write) s
      match addr with
      | none => signalAddressException (.Store_AMO_Fault,v) t
      | some p => rawWriteData (p,GPR rs2 t,4) («write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 (rawReadData p t)),rd) t) := by
  rfl

/-- Flapjack-only unconditional whole-state normal form for the complete
source equation; this helper has no separately named HOL declaration. -/
theorem amoSwapDWholeState (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5)
    (s : riscv_state) :
    «dfn'AMOSWAP_D» (aq,rl,rd,rs1,rs2) s =
    let v := GPR rs1 s
    if !(holWordExtract 3 2 0 v == BitVec.ofNat 3 0) then
      signalAddressException (.AMO_Misaligned,v) s
    else
      let (addr,t) := translateAddr (v,fetchType.Data,accessType.Write) s
      match addr with
      | none => signalAddressException (.Store_AMO_Fault,v) t
      | some p => rawWriteData (p,GPR rs2 t,8) («write'GPR» (rawReadData p t,rd) t) := by
  rfl

end Flapjack.RiscV.L3
