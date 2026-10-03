import Flapjack.RiscV.L3.Defs.IntegerStore
namespace Flapjack.RiscV.L3

/-- Literal complete original atomic min/max equation. W sign-extends the
old low32 memory value before the original signed/unsigned word64 comparison.
Virtual alignment precedes Data/Write translation; operands are read from its
returned state before the destination update. No mode or success premise. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOMIN_W_def"]
noncomputable def «dfn'AMOMIN_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s)))); (rawWriteData ((pAddr, ((((if BitVec.slt (GPR rs2 s) v_1 then (GPR rs2 s) else v_1)), 4)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- Literal complete original atomic min/max equation. W sign-extends the
old low32 memory value before the original signed/unsigned word64 comparison.
Virtual alignment precedes Data/Write translation; operands are read from its
returned state before the destination update. No mode or success premise. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOMIN_D_def"]
noncomputable def «dfn'AMOMIN_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 3 2 0 v) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (rawReadData pAddr s); (rawWriteData ((pAddr, ((((if BitVec.slt (GPR rs2 s) v_1 then (GPR rs2 s) else v_1)), 8)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- Literal complete original atomic min/max equation. W sign-extends the
old low32 memory value before the original signed/unsigned word64 comparison.
Virtual alignment precedes Data/Write translation; operands are read from its
returned state before the destination update. No mode or success premise. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOMINU_W_def"]
noncomputable def «dfn'AMOMINU_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s)))); (rawWriteData ((pAddr, ((((if BitVec.ult (GPR rs2 s) v_1 then (GPR rs2 s) else v_1)), 4)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- Literal complete original atomic min/max equation. W sign-extends the
old low32 memory value before the original signed/unsigned word64 comparison.
Virtual alignment precedes Data/Write translation; operands are read from its
returned state before the destination update. No mode or success premise. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOMINU_D_def"]
noncomputable def «dfn'AMOMINU_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 3 2 0 v) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (rawReadData pAddr s); (rawWriteData ((pAddr, ((((if BitVec.ult (GPR rs2 s) v_1 then (GPR rs2 s) else v_1)), 8)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- Literal complete original atomic min/max equation. W sign-extends the
old low32 memory value before the original signed/unsigned word64 comparison.
Virtual alignment precedes Data/Write translation; operands are read from its
returned state before the destination update. No mode or success premise. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOMAX_W_def"]
noncomputable def «dfn'AMOMAX_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s)))); (rawWriteData ((pAddr, ((((if BitVec.slt (GPR rs2 s) v_1 then v_1 else (GPR rs2 s))), 4)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- Literal complete original atomic min/max equation. W sign-extends the
old low32 memory value before the original signed/unsigned word64 comparison.
Virtual alignment precedes Data/Write translation; operands are read from its
returned state before the destination update. No mode or success premise. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOMAX_D_def"]
noncomputable def «dfn'AMOMAX_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 3 2 0 v) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (rawReadData pAddr s); (rawWriteData ((pAddr, ((((if BitVec.slt (GPR rs2 s) v_1 then v_1 else (GPR rs2 s))), 8)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- Literal complete original atomic min/max equation. W sign-extends the
old low32 memory value before the original signed/unsigned word64 comparison.
Virtual alignment precedes Data/Write translation; operands are read from its
returned state before the destination update. No mode or success premise. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOMAXU_W_def"]
noncomputable def «dfn'AMOMAXU_W» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 2 1 0 v) == (BitVec.ofNat 2 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (BitVec.signExtend 64 ((holWordExtract 32 31 0 (rawReadData pAddr s)))); (rawWriteData ((pAddr, ((((if BitVec.ult (GPR rs2 s) v_1 then v_1 else (GPR rs2 s))), 4)))) ((«write'GPR» (v_1, rd) s))))))))))

/-- Literal complete original atomic min/max equation. W sign-extends the
old low32 memory value before the original signed/unsigned word64 comparison.
Virtual alignment precedes Data/Write translation; operands are read from its
returned state before the destination update. No mode or success premise. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'AMOMAXU_D_def"]
noncomputable def «dfn'AMOMAXU_D» (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 5) × ((BitVec 5) × (BitVec 5)))))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (_aq, (_rl, (rd, (rs1, rs2)))) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (GPR rs1 state); (if ((!(((holWordExtract 3 2 0 v) == (BitVec.ofNat 3 0))))) then ((signalAddressException (ExceptionType.AMO_Misaligned, v) state)) else ((match (translateAddr ((v, (fetchType.Data, accessType.Write))) state) with | (v0, s) => (match v0 with | none => (signalAddressException (ExceptionType.Store_AMO_Fault, v) s) | some pAddr => (let v_1 : (BitVec 64) := (rawReadData pAddr s); (rawWriteData ((pAddr, ((((if BitVec.ult (GPR rs2 s) v_1 then v_1 else (GPR rs2 s))), 8)))) ((«write'GPR» (v_1, rd) s))))))))))


/-- Flapjack-only unconditional whole-state normal form; no separately
named HOL original exists for this helper. -/
theorem amoMinWWholeState (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5)
    (s : riscv_state) :
    «dfn'AMOMIN_W» (aq,rl,rd,rs1,rs2) s =
    let v := GPR rs1 s
    if !(holWordExtract 2 1 0 v == BitVec.ofNat 2 0) then
      signalAddressException (.AMO_Misaligned,v) s
    else
      let (addr,t) := translateAddr (v,fetchType.Data,accessType.Write) s
      match addr with
      | none => signalAddressException (.Store_AMO_Fault,v) t
      | some p =>
        let old := BitVec.signExtend 64 (holWordExtract 32 31 0 (rawReadData p t))
        rawWriteData (p,(if BitVec.slt (GPR rs2 t) old then GPR rs2 t else old),4)
          («write'GPR» (old,rd) t) := by
  rfl

/-- Flapjack-only unconditional whole-state normal form; no separately
named HOL original exists for this helper. -/
theorem amoMinDWholeState (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5)
    (s : riscv_state) :
    «dfn'AMOMIN_D» (aq,rl,rd,rs1,rs2) s =
    let v := GPR rs1 s
    if !(holWordExtract 3 2 0 v == BitVec.ofNat 3 0) then
      signalAddressException (.AMO_Misaligned,v) s
    else
      let (addr,t) := translateAddr (v,fetchType.Data,accessType.Write) s
      match addr with
      | none => signalAddressException (.Store_AMO_Fault,v) t
      | some p =>
        let old := rawReadData p t
        rawWriteData (p,(if BitVec.slt (GPR rs2 t) old then GPR rs2 t else old),8)
          («write'GPR» (old,rd) t) := by
  rfl

/-- Flapjack-only unconditional whole-state normal form; no separately
named HOL original exists for this helper. -/
theorem amoMaxWWholeState (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5)
    (s : riscv_state) :
    «dfn'AMOMAX_W» (aq,rl,rd,rs1,rs2) s =
    let v := GPR rs1 s
    if !(holWordExtract 2 1 0 v == BitVec.ofNat 2 0) then
      signalAddressException (.AMO_Misaligned,v) s
    else
      let (addr,t) := translateAddr (v,fetchType.Data,accessType.Write) s
      match addr with
      | none => signalAddressException (.Store_AMO_Fault,v) t
      | some p =>
        let old := BitVec.signExtend 64 (holWordExtract 32 31 0 (rawReadData p t))
        rawWriteData (p,(if BitVec.slt (GPR rs2 t) old then old else GPR rs2 t),4)
          («write'GPR» (old,rd) t) := by
  rfl

/-- Flapjack-only unconditional whole-state normal form; no separately
named HOL original exists for this helper. -/
theorem amoMaxDWholeState (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5)
    (s : riscv_state) :
    «dfn'AMOMAX_D» (aq,rl,rd,rs1,rs2) s =
    let v := GPR rs1 s
    if !(holWordExtract 3 2 0 v == BitVec.ofNat 3 0) then
      signalAddressException (.AMO_Misaligned,v) s
    else
      let (addr,t) := translateAddr (v,fetchType.Data,accessType.Write) s
      match addr with
      | none => signalAddressException (.Store_AMO_Fault,v) t
      | some p =>
        let old := rawReadData p t
        rawWriteData (p,(if BitVec.slt (GPR rs2 t) old then old else GPR rs2 t),8)
          («write'GPR» (old,rd) t) := by
  rfl

/-- Flapjack-only unconditional whole-state normal form; no separately
named HOL original exists for this helper. -/
theorem amoMinuWWholeState (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5)
    (s : riscv_state) :
    «dfn'AMOMINU_W» (aq,rl,rd,rs1,rs2) s =
    let v := GPR rs1 s
    if !(holWordExtract 2 1 0 v == BitVec.ofNat 2 0) then
      signalAddressException (.AMO_Misaligned,v) s
    else
      let (addr,t) := translateAddr (v,fetchType.Data,accessType.Write) s
      match addr with
      | none => signalAddressException (.Store_AMO_Fault,v) t
      | some p =>
        let old := BitVec.signExtend 64 (holWordExtract 32 31 0 (rawReadData p t))
        rawWriteData (p,(if BitVec.ult (GPR rs2 t) old then GPR rs2 t else old),4)
          («write'GPR» (old,rd) t) := by
  rfl

/-- Flapjack-only unconditional whole-state normal form; no separately
named HOL original exists for this helper. -/
theorem amoMinuDWholeState (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5)
    (s : riscv_state) :
    «dfn'AMOMINU_D» (aq,rl,rd,rs1,rs2) s =
    let v := GPR rs1 s
    if !(holWordExtract 3 2 0 v == BitVec.ofNat 3 0) then
      signalAddressException (.AMO_Misaligned,v) s
    else
      let (addr,t) := translateAddr (v,fetchType.Data,accessType.Write) s
      match addr with
      | none => signalAddressException (.Store_AMO_Fault,v) t
      | some p =>
        let old := rawReadData p t
        rawWriteData (p,(if BitVec.ult (GPR rs2 t) old then GPR rs2 t else old),8)
          («write'GPR» (old,rd) t) := by
  rfl

/-- Flapjack-only unconditional whole-state normal form; no separately
named HOL original exists for this helper. -/
theorem amoMaxuWWholeState (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5)
    (s : riscv_state) :
    «dfn'AMOMAXU_W» (aq,rl,rd,rs1,rs2) s =
    let v := GPR rs1 s
    if !(holWordExtract 2 1 0 v == BitVec.ofNat 2 0) then
      signalAddressException (.AMO_Misaligned,v) s
    else
      let (addr,t) := translateAddr (v,fetchType.Data,accessType.Write) s
      match addr with
      | none => signalAddressException (.Store_AMO_Fault,v) t
      | some p =>
        let old := BitVec.signExtend 64 (holWordExtract 32 31 0 (rawReadData p t))
        rawWriteData (p,(if BitVec.ult (GPR rs2 t) old then old else GPR rs2 t),4)
          («write'GPR» (old,rd) t) := by
  rfl

/-- Flapjack-only unconditional whole-state normal form; no separately
named HOL original exists for this helper. -/
theorem amoMaxuDWholeState (aq rl : BitVec 1) (rd rs1 rs2 : BitVec 5)
    (s : riscv_state) :
    «dfn'AMOMAXU_D» (aq,rl,rd,rs1,rs2) s =
    let v := GPR rs1 s
    if !(holWordExtract 3 2 0 v == BitVec.ofNat 3 0) then
      signalAddressException (.AMO_Misaligned,v) s
    else
      let (addr,t) := translateAddr (v,fetchType.Data,accessType.Write) s
      match addr with
      | none => signalAddressException (.Store_AMO_Fault,v) t
      | some p =>
        let old := rawReadData p t
        rawWriteData (p,(if BitVec.ult (GPR rs2 t) old then old else GPR rs2 t),8)
          («write'GPR» (old,rd) t) := by
  rfl

end Flapjack.RiscV.L3
