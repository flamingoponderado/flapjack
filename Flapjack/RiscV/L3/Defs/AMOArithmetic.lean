import Flapjack.RiscV.L3.Defs.IntegerStore
namespace Flapjack.RiscV.L3

/-- Literal original complete atomic arithmetic/bitwise equation. Virtual
alignment precedes Data/Write translation; the returned state supplies both old
memory and source register operands before the destination update. W sign-extends
the low32 old value before the word64 operation and writes four bytes; D uses
full64 and eight bytes. No architecture/success/core-bound premise is added. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOXOR_W_def"]
noncomputable def «dfn'AMOXOR_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s)))); (rawWriteData ((pAddr, (((((GPR rs2 s) ^^^ v_1)), 4)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- Literal original complete atomic arithmetic/bitwise equation. Virtual
alignment precedes Data/Write translation; the returned state supplies both old
memory and source register operands before the destination update. W sign-extends
the low32 old value before the word64 operation and writes four bytes; D uses
full64 and eight bytes. No architecture/success/core-bound premise is added. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOXOR_D_def"]
noncomputable def «dfn'AMOXOR_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 3 2 0 v) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (rawReadData pAddr s); (rawWriteData ((pAddr, (((((GPR rs2 s) ^^^ v_1)), 8)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- Literal original complete atomic arithmetic/bitwise equation. Virtual
alignment precedes Data/Write translation; the returned state supplies both old
memory and source register operands before the destination update. W sign-extends
the low32 old value before the word64 operation and writes four bytes; D uses
full64 and eight bytes. No architecture/success/core-bound premise is added. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOOR_W_def"]
noncomputable def «dfn'AMOOR_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s)))); (rawWriteData ((pAddr, (((((GPR rs2 s) ||| v_1)), 4)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- Literal original complete atomic arithmetic/bitwise equation. Virtual
alignment precedes Data/Write translation; the returned state supplies both old
memory and source register operands before the destination update. W sign-extends
the low32 old value before the word64 operation and writes four bytes; D uses
full64 and eight bytes. No architecture/success/core-bound premise is added. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOOR_D_def"]
noncomputable def «dfn'AMOOR_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 3 2 0 v) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (rawReadData pAddr s); (rawWriteData ((pAddr, (((((GPR rs2 s) ||| v_1)), 8)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- Literal original complete atomic arithmetic/bitwise equation. Virtual
alignment precedes Data/Write translation; the returned state supplies both old
memory and source register operands before the destination update. W sign-extends
the low32 old value before the word64 operation and writes four bytes; D uses
full64 and eight bytes. No architecture/success/core-bound premise is added. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOAND_W_def"]
noncomputable def «dfn'AMOAND_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s)))); (rawWriteData ((pAddr, (((((GPR rs2 s) &&& v_1)), 4)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- Literal original complete atomic arithmetic/bitwise equation. Virtual
alignment precedes Data/Write translation; the returned state supplies both old
memory and source register operands before the destination update. W sign-extends
the low32 old value before the word64 operation and writes four bytes; D uses
full64 and eight bytes. No architecture/success/core-bound premise is added. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOAND_D_def"]
noncomputable def «dfn'AMOAND_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 3 2 0 v) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (rawReadData pAddr s); (rawWriteData ((pAddr, (((((GPR rs2 s) &&& v_1)), 8)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- Literal original complete atomic arithmetic/bitwise equation. Virtual
alignment precedes Data/Write translation; the returned state supplies both old
memory and source register operands before the destination update. W sign-extends
the low32 old value before the word64 operation and writes four bytes; D uses
full64 and eight bytes. No architecture/success/core-bound premise is added. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOADD_W_def"]
noncomputable def «dfn'AMOADD_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s)))); (rawWriteData ((pAddr, (((((GPR rs2 s) + v_1)), 4)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- Literal original complete atomic arithmetic/bitwise equation. Virtual
alignment precedes Data/Write translation; the returned state supplies both old
memory and source register operands before the destination update. W sign-extends
the low32 old value before the word64 operation and writes four bytes; D uses
full64 and eight bytes. No architecture/success/core-bound premise is added. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOADD_D_def"]
noncomputable def «dfn'AMOADD_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 3 2 0 v) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (rawReadData pAddr s); (rawWriteData ((pAddr, (((((GPR rs2 s) + v_1)), 8)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- Flapjack-only unconditional complete-state normal form; no separately
named HOL original exists for this helper. -/
theorem amoAddWWholeState (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5)
    (s : riscv_state) :
    «dfn'AMOADD_W» (aq,rl,rd,rs1,rs2) s =
    let v := GPR rs1 s
    if !(holWordExtract 2 1 0 v == BitVec.ofNat 2 0) then
      signalAddressException (.AMO_Misaligned,v) s
    else
      let (addr,t) := translateAddr (v,fetchType.Data,accessType.Write) s
      match addr with
      | none => signalAddressException (.Store_AMO_Fault,v) t
      | some p =>
        let old := BitVec.signExtend 64 (holWordExtract 32 31 0 (rawReadData p t))
        rawWriteData (p,GPR rs2 t + old,4) («write'GPR» (old,rd) t) := by
  rfl

/-- Flapjack-only unconditional complete-state normal form; no separately
named HOL original exists for this helper. -/
theorem amoAddDWholeState (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5)
    (s : riscv_state) :
    «dfn'AMOADD_D» (aq,rl,rd,rs1,rs2) s =
    let v := GPR rs1 s
    if !(holWordExtract 3 2 0 v == BitVec.ofNat 3 0) then
      signalAddressException (.AMO_Misaligned,v) s
    else
      let (addr,t) := translateAddr (v,fetchType.Data,accessType.Write) s
      match addr with
      | none => signalAddressException (.Store_AMO_Fault,v) t
      | some p =>
        let old := rawReadData p t
        rawWriteData (p,GPR rs2 t + old,8) («write'GPR» (old,rd) t) := by
  rfl

/-- Flapjack-only unconditional complete-state normal form; no separately
named HOL original exists for this helper. -/
theorem amoXorWWholeState (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5)
    (s : riscv_state) :
    «dfn'AMOXOR_W» (aq,rl,rd,rs1,rs2) s =
    let v := GPR rs1 s
    if !(holWordExtract 2 1 0 v == BitVec.ofNat 2 0) then
      signalAddressException (.AMO_Misaligned,v) s
    else
      let (addr,t) := translateAddr (v,fetchType.Data,accessType.Write) s
      match addr with
      | none => signalAddressException (.Store_AMO_Fault,v) t
      | some p =>
        let old := BitVec.signExtend 64 (holWordExtract 32 31 0 (rawReadData p t))
        rawWriteData (p,GPR rs2 t ^^^ old,4) («write'GPR» (old,rd) t) := by
  rfl

/-- Flapjack-only unconditional complete-state normal form; no separately
named HOL original exists for this helper. -/
theorem amoXorDWholeState (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5)
    (s : riscv_state) :
    «dfn'AMOXOR_D» (aq,rl,rd,rs1,rs2) s =
    let v := GPR rs1 s
    if !(holWordExtract 3 2 0 v == BitVec.ofNat 3 0) then
      signalAddressException (.AMO_Misaligned,v) s
    else
      let (addr,t) := translateAddr (v,fetchType.Data,accessType.Write) s
      match addr with
      | none => signalAddressException (.Store_AMO_Fault,v) t
      | some p =>
        let old := rawReadData p t
        rawWriteData (p,GPR rs2 t ^^^ old,8) («write'GPR» (old,rd) t) := by
  rfl

/-- Flapjack-only unconditional complete-state normal form; no separately
named HOL original exists for this helper. -/
theorem amoAndWWholeState (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5)
    (s : riscv_state) :
    «dfn'AMOAND_W» (aq,rl,rd,rs1,rs2) s =
    let v := GPR rs1 s
    if !(holWordExtract 2 1 0 v == BitVec.ofNat 2 0) then
      signalAddressException (.AMO_Misaligned,v) s
    else
      let (addr,t) := translateAddr (v,fetchType.Data,accessType.Write) s
      match addr with
      | none => signalAddressException (.Store_AMO_Fault,v) t
      | some p =>
        let old := BitVec.signExtend 64 (holWordExtract 32 31 0 (rawReadData p t))
        rawWriteData (p,GPR rs2 t &&& old,4) («write'GPR» (old,rd) t) := by
  rfl

/-- Flapjack-only unconditional complete-state normal form; no separately
named HOL original exists for this helper. -/
theorem amoAndDWholeState (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5)
    (s : riscv_state) :
    «dfn'AMOAND_D» (aq,rl,rd,rs1,rs2) s =
    let v := GPR rs1 s
    if !(holWordExtract 3 2 0 v == BitVec.ofNat 3 0) then
      signalAddressException (.AMO_Misaligned,v) s
    else
      let (addr,t) := translateAddr (v,fetchType.Data,accessType.Write) s
      match addr with
      | none => signalAddressException (.Store_AMO_Fault,v) t
      | some p =>
        let old := rawReadData p t
        rawWriteData (p,GPR rs2 t &&& old,8) («write'GPR» (old,rd) t) := by
  rfl

/-- Flapjack-only unconditional complete-state normal form; no separately
named HOL original exists for this helper. -/
theorem amoOrWWholeState (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5)
    (s : riscv_state) :
    «dfn'AMOOR_W» (aq,rl,rd,rs1,rs2) s =
    let v := GPR rs1 s
    if !(holWordExtract 2 1 0 v == BitVec.ofNat 2 0) then
      signalAddressException (.AMO_Misaligned,v) s
    else
      let (addr,t) := translateAddr (v,fetchType.Data,accessType.Write) s
      match addr with
      | none => signalAddressException (.Store_AMO_Fault,v) t
      | some p =>
        let old := BitVec.signExtend 64 (holWordExtract 32 31 0 (rawReadData p t))
        rawWriteData (p,GPR rs2 t ||| old,4) («write'GPR» (old,rd) t) := by
  rfl

/-- Flapjack-only unconditional complete-state normal form; no separately
named HOL original exists for this helper. -/
theorem amoOrDWholeState (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5)
    (s : riscv_state) :
    «dfn'AMOOR_D» (aq,rl,rd,rs1,rs2) s =
    let v := GPR rs1 s
    if !(holWordExtract 3 2 0 v == BitVec.ofNat 3 0) then
      signalAddressException (.AMO_Misaligned,v) s
    else
      let (addr,t) := translateAddr (v,fetchType.Data,accessType.Write) s
      match addr with
      | none => signalAddressException (.Store_AMO_Fault,v) t
      | some p =>
        let old := rawReadData p t
        rawWriteData (p,GPR rs2 t ||| old,8) («write'GPR» (old,rd) t) := by
  rfl

end Flapjack.RiscV.L3
