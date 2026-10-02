import Flapjack.RiscV.L3.Support
import Flapjack.Misc.BinaryIeeeRound
import Flapjack.Misc.BinaryIeeeConvert
import Flapjack.Misc.MachineIeee.Convert

/-!
# Complete original L3 floating-point comparison, integer and cross-precision conversion equations

This coherent section contains the complete original equations for both
precisions, together with their exact state-access/update/rounding dependency
closure. It is not a definition of full Run or NextRISCV; those declarations
and the remaining instruction cases have their own open model obligations.
Each body is rendered from the original elaborated HOL theorem by selecting
roots and their full dependency closure, never by narrowing its branches.
The real-valued primitive rendering uses the stated SOUNDNESS item8 assumption.
-/
set_option maxRecDepth 200000
namespace Flapjack.RiscV.L3
open Flapjack.Basis.Pure.MlString

/-- HOL `riscv$MCSR` (`MCSR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "MCSR_def"]
def MCSR (state : riscv_state) : MachineCSR :=
  (state.c_MCSR state.procID)

/-- HOL `riscv$write'NextFetch` (`write'NextFetch_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'NextFetch_def"]
def «write'NextFetch» (value : (Option TransferControl)) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (let r := state; { r with c_NextFetch := ((fun (_eta1 : ((BitVec 8) → (Option TransferControl))) => (holUpdate state.procID value state.c_NextFetch))) r.c_NextFetch }))

/-- HOL `riscv$setTrap` (`setTrap_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "setTrap_def"]
noncomputable def setTrap (arg0 : (ExceptionType × (Option (BitVec 64)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (e, badaddr) =>
  (fun (state : riscv_state) => («write'NextFetch» ((some ((TransferControl.Trap ((let r := ((let r := (Flapjack.holArb SynchronousTrap); { r with trap := ((fun (_eta1 : ExceptionType) => e)) r.trap })); { r with badaddr := ((fun (_eta1 : (Option (BitVec 64))) => badaddr)) r.badaddr })))))) state))

/-- HOL `riscv$signalException` (`signalException_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "signalException_def"]
noncomputable def signalException (e : ExceptionType) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (setTrap ((e, ((none : (Option (BitVec 64)))))) state))

/-- HOL `riscv$gpr` (`gpr_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "gpr_def"]
def gpr (n : (BitVec 5)) : (riscv_state → (BitVec 64)) :=
  (fun (state : riscv_state) => (state.c_gpr state.procID n))

/-- HOL `riscv$GPR` (`GPR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "GPR_def"]
def GPR (n : (BitVec 5)) : (riscv_state → (BitVec 64)) :=
  (fun (state : riscv_state) => (if ((n == (BitVec.ofNat 5 0))) then (BitVec.ofNat 64 0) else (gpr n state)))

/-- HOL `riscv$write'MCSR` (`write'MCSR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'MCSR_def"]
def «write'MCSR» (value : MachineCSR) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (let r := state; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => (holUpdate state.procID value state.c_MCSR))) r.c_MCSR }))

/-- HOL `riscv$ext_status` (`ext_status_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "ext_status_def"]
def ext_status (e : ExtStatus) : (BitVec 2) :=
  (match e with | .Off => (BitVec.ofNat 2 0) | .Initial => (BitVec.ofNat 2 1) | .Clean => (BitVec.ofNat 2 2) | .Dirty => (BitVec.ofNat 2 3))

/-- HOL `riscv$Delta` (`Delta_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "Delta_def"]
def Delta (state : riscv_state) : StateDelta :=
  (state.c_update state.procID)

/-- HOL `riscv$write'Delta` (`write'Delta_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'Delta_def"]
def «write'Delta» (value : StateDelta) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (let r := state; { r with c_update := ((fun (_eta1 : ((BitVec 8) → StateDelta)) => (holUpdate state.procID value state.c_update))) r.c_update }))

/-- HOL `riscv$write'gpr` (`write'gpr_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'gpr_def"]
def «write'gpr» (arg0 : ((BitVec 64) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (value, n) =>
  (fun (state : riscv_state) => (let r := state; { r with c_gpr := ((fun (_eta1 : ((BitVec 8) → ((BitVec 5) → (BitVec 64)))) => ((holUpdate state.procID ((holUpdate n value (state.c_gpr state.procID))) state.c_gpr)))) r.c_gpr }))

/-- HOL `riscv$write'GPR` (`write'GPR_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'GPR_def"]
def «write'GPR» (arg0 : ((BitVec 64) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (value, n) =>
  (fun (state : riscv_state) => (if ((!((n == (BitVec.ofNat 5 0))))) then ((«write'gpr» (value, n) state)) else state))

/-- HOL `riscv$fpr` (`fpr_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "fpr_def"]
def fpr (n : (BitVec 5)) : (riscv_state → (BitVec 64)) :=
  (fun (state : riscv_state) => (state.c_fpr state.procID n))

/-- HOL `riscv$FPRS` (`FPRS_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "FPRS_def"]
def FPRS (n : (BitVec 5)) : (riscv_state → (BitVec 32)) :=
  (fun (state : riscv_state) => (holWordExtract 32 31 0 (fpr n state)))

/-- HOL `riscv$FPRD` (`FPRD_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "FPRD_def"]
def FPRD (n : (BitVec 5)) : (riscv_state → (BitVec 64)) :=
  (fun (state : riscv_state) => (fpr n state))

/-- HOL `riscv$write'fpr` (`write'fpr_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'fpr_def"]
def «write'fpr» (arg0 : ((BitVec 64) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (value, n) =>
  (fun (state : riscv_state) => (let r := state; { r with c_fpr := ((fun (_eta1 : ((BitVec 8) → ((BitVec 5) → (BitVec 64)))) => ((holUpdate state.procID ((holUpdate n value (state.c_fpr state.procID))) state.c_fpr)))) r.c_fpr }))

/-- HOL `riscv$write'FPRS` (`write'FPRS_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'FPRS_def"]
def «write'FPRS» (arg0 : ((BitVec 32) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (value, n) =>
  (fun (state : riscv_state) => («write'fpr» ((((holBitFieldInsert 31 0 value (fpr n state))), n)) state))

/-- HOL `riscv$write'FPRD` (`write'FPRD_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'FPRD_def"]
def «write'FPRD» (arg0 : ((BitVec 64) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (value, n) =>
  (fun (state : riscv_state) => («write'fpr» (value, n) state))

/-- HOL `riscv$FP32_Sign` (`FP32_Sign_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "FP32_Sign_def"]
def FP32_Sign (x : (BitVec 32)) : Bool :=
  (x.getLsbD 31)

/-- HOL `riscv$writeFPRS` (`writeFPRS_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "writeFPRS_def"]
def writeFPRS (arg0 : ((BitVec 5) × (BitVec 32))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, val) =>
  (fun (state : riscv_state) => (match (let s : riscv_state := («write'FPRS» (val, rd) state); ((MCSR s), s)) with | (v, s) => (match (let s0 : riscv_state := («write'MCSR» ((let r := v; { r with mstatus := ((fun (_eta1 : mstatus) => ((let r := v.mstatus; { r with MFS := ((fun (_eta1 : (BitVec 2)) => (ext_status ExtStatus.Dirty))) r.MFS })))) r.mstatus })) s); ((MCSR s0), s0)) with | (v_1, s_1) => (match (let s0 : riscv_state := («write'MCSR» ((let r := v_1; { r with mstatus := ((fun (_eta1 : mstatus) => ((let r := v_1.mstatus; { r with MSD := ((fun (_eta1 : Bool) => true)) r.MSD })))) r.mstatus })) s_1); ((Delta s0), s0)) with | (v, s) => («write'Delta» ((let r := v; { r with data1 := ((fun (_eta1 : (Option (BitVec 64))) => ((some (BitVec.setWidth 64 val))))) r.data1 })) s)))))

/-- HOL `riscv$FP64_Sign` (`FP64_Sign_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "FP64_Sign_def"]
def FP64_Sign (x : (BitVec 64)) : Bool :=
  (x.getLsbD 63)

/-- HOL `riscv$writeFPRD` (`writeFPRD_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "writeFPRD_def"]
def writeFPRD (arg0 : ((BitVec 5) × (BitVec 64))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, val) =>
  (fun (state : riscv_state) => (match (let s : riscv_state := («write'FPRD» (val, rd) state); ((MCSR s), s)) with | (v, s) => (match (let s0 : riscv_state := («write'MCSR» ((let r := v; { r with mstatus := ((fun (_eta1 : mstatus) => ((let r := v.mstatus; { r with MFS := ((fun (_eta1 : (BitVec 2)) => (ext_status ExtStatus.Dirty))) r.MFS })))) r.mstatus })) s); ((MCSR s0), s0)) with | (v_1, s_1) => (match (let s0 : riscv_state := («write'MCSR» ((let r := v_1; { r with mstatus := ((fun (_eta1 : mstatus) => ((let r := v_1.mstatus; { r with MSD := ((fun (_eta1 : Bool) => true)) r.MSD })))) r.mstatus })) s_1); ((Delta s0), s0)) with | (v, s) => («write'Delta» ((let r := v; { r with data1 := ((fun (_eta1 : (Option (BitVec 64))) => (some val))) r.data1 })) s)))))

/-- HOL `riscv$l3round` (`l3round_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "l3round_def"]
def l3round (rnd : Rounding) : (Option HolRounding) :=
  (match rnd with | .RNE => (some HolRounding.roundTiesToEven) | .RTZ => (some HolRounding.roundTowardZero) | .RDN => (some HolRounding.roundTowardNegative) | .RUP => (some HolRounding.roundTowardPositive) | .RMM => (none : (Option HolRounding)) | .RDYN => (none : (Option HolRounding)))

/-- HOL `riscv$fcsr` (`fcsr_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "fcsr_def"]
def fcsr (state : riscv_state) : FPCSR :=
  (state.c_UCSR state.procID).fpcsr

/-- HOL `riscv$rnd_mode_dynamic` (`rnd_mode_dynamic_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rnd_mode_dynamic_def"]
def rnd_mode_dynamic (rnd : (BitVec 3)) : (Option Rounding) :=
  (((fun (v : (BitVec 3)) => (if ((v == (BitVec.ofNat 3 0))) then (some Rounding.RNE) else ((if ((v == (BitVec.ofNat 3 1))) then (some Rounding.RTZ) else ((if ((v == (BitVec.ofNat 3 2))) then (some Rounding.RDN) else ((if ((v == (BitVec.ofNat 3 3))) then (some Rounding.RUP) else ((if ((v == (BitVec.ofNat 3 4))) then (some Rounding.RMM) else ((none : (Option Rounding)))))))))))))) rnd)

/-- HOL `riscv$rnd_mode_static` (`rnd_mode_static_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rnd_mode_static_def"]
def rnd_mode_static (rnd : (BitVec 3)) : (Option Rounding) :=
  (((fun (v : (BitVec 3)) => (if ((v == (BitVec.ofNat 3 0))) then (some Rounding.RNE) else ((if ((v == (BitVec.ofNat 3 1))) then (some Rounding.RTZ) else ((if ((v == (BitVec.ofNat 3 2))) then (some Rounding.RDN) else ((if ((v == (BitVec.ofNat 3 3))) then (some Rounding.RUP) else ((if ((v == (BitVec.ofNat 3 4))) then (some Rounding.RMM) else ((if ((v == (BitVec.ofNat 3 7))) then (some Rounding.RDYN) else ((none : (Option Rounding)))))))))))))))) rnd)

/-- HOL `riscv$round` (`round_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "round_def"]
def round (rnd : (BitVec 3)) : (riscv_state → (Option HolRounding)) :=
  (fun (state : riscv_state) => (match (rnd_mode_static rnd) with | none => (none : (Option HolRounding)) | some v => (match v with | .RNE => (l3round Rounding.RNE) | .RTZ => (l3round Rounding.RTZ) | .RDN => (l3round Rounding.RDN) | .RUP => (l3round Rounding.RUP) | .RMM => (l3round Rounding.RMM) | .RDYN => (match (rnd_mode_dynamic ((fcsr state).FRM)) with | none => (none : (Option HolRounding)) | some frm => (l3round frm)))))

/-- HOL `riscv$dfn'FCVT_W_S` (`dfn'FCVT_W_S_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_W_S_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_W_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (let v : (BitVec 32) := (FPRS rs state); (let val : Int := (holThe ((holFloatToInt r ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8)))); («write'GPR» ((((if ((((holFloatIsNan ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8))) || ((v == (BitVec.ofNat 32 2139095040))))) then ((BitVec.ofNat 64 (((2 ^ 31) - 1)))) else ((if ((v == (BitVec.ofNat 32 4286578688))) then ((-((BitVec.ofNat 64 (2 ^ 31))))) else ((if ((decide (val > (((((Int.ofNat 2) ^ 31)) - (Int.ofNat 1)))))) then ((BitVec.ofNat 64 (((2 ^ 31) - 1)))) else ((if ((decide (val < ((-(((Int.ofNat 2) ^ 31))))))) then ((-((BitVec.ofNat 64 (2 ^ 31))))) else (BitVec.ofInt 64 val))))))))), rd)) state)))))

/-- HOL `riscv$dfn'FCVT_W_D` (`dfn'FCVT_W_D_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_W_D_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_W_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (let v : (BitVec 64) := (FPRD rs state); (let val : Int := (holThe ((holFloatToInt r ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11)))); («write'GPR» ((((if ((((holFloatIsNan ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11))) || ((v == (BitVec.ofNat 64 9218868437227405312))))) then ((BitVec.ofNat 64 (((2 ^ 31) - 1)))) else ((if ((v == (BitVec.ofNat 64 18442240474082181120))) then ((-((BitVec.ofNat 64 (2 ^ 31))))) else ((if ((decide (val > (((((Int.ofNat 2) ^ 31)) - (Int.ofNat 1)))))) then ((BitVec.ofNat 64 (((2 ^ 31) - 1)))) else ((if ((decide (val < ((-(((Int.ofNat 2) ^ 31))))))) then ((-((BitVec.ofNat 64 (2 ^ 31))))) else (BitVec.ofInt 64 val))))))))), rd)) state)))))

/-- HOL `riscv$dfn'FCVT_WU_S` (`dfn'FCVT_WU_S_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_WU_S_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_WU_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (let v : (BitVec 32) := (FPRS rs state); (let val : Int := (holThe ((holFloatToInt r ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8)))); («write'GPR» ((((if ((((holFloatIsNan ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8))) || ((v == (BitVec.ofNat 32 2139095040))))) then ((BitVec.ofNat 64 (((2 ^ 32) - 1)))) else ((if ((v == (BitVec.ofNat 32 4286578688))) then (BitVec.ofNat 64 0) else ((if ((decide (val > (((((Int.ofNat 2) ^ 32)) - (Int.ofNat 1)))))) then ((BitVec.ofNat 64 (((2 ^ 32) - 1)))) else ((if ((decide (val < (Int.ofNat 0)))) then (BitVec.ofNat 64 0) else (BitVec.ofInt 64 val))))))))), rd)) state)))))

/-- HOL `riscv$dfn'FCVT_WU_D` (`dfn'FCVT_WU_D_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_WU_D_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_WU_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (let v : (BitVec 64) := (FPRD rs state); (let val : Int := (holThe ((holFloatToInt r ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11)))); («write'GPR» ((((if ((((holFloatIsNan ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11))) || ((v == (BitVec.ofNat 64 9218868437227405312))))) then ((BitVec.ofNat 64 (((2 ^ 32) - 1)))) else ((if ((v == (BitVec.ofNat 64 18442240474082181120))) then (BitVec.ofNat 64 0) else ((if ((decide (val > (((((Int.ofNat 2) ^ 32)) - (Int.ofNat 1)))))) then ((BitVec.ofNat 64 (((2 ^ 32) - 1)))) else ((if ((decide (val < (Int.ofNat 0)))) then (BitVec.ofNat 64 0) else (BitVec.ofInt 64 val))))))))), rd)) state)))))

/-- HOL `riscv$dfn'FCVT_S_WU` (`dfn'FCVT_S_WU_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_S_WU_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_S_WU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (writeFPRS ((rd, (((fun (a : HolFloat 23 8) => (a.sign ++ a.exponent ++ a.significand).cast (by decide)) (holRealToFloat r ((((BitVec.setWidth 33 ((BitVec.ofNat 1 0) ++ ((holWordExtract 32 31 0 (GPR rs state)))))).toInt) : Rat)))))) state)))

/-- HOL `riscv$dfn'FCVT_S_W` (`dfn'FCVT_S_W_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_S_W_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_S_W» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (writeFPRS ((rd, (((fun (a : HolFloat 23 8) => (a.sign ++ a.exponent ++ a.significand).cast (by decide)) (holRealToFloat r ((((holWordExtract 32 31 0 (GPR rs state))).toInt) : Rat)))))) state)))

/-- HOL `riscv$dfn'FCVT_S_LU` (`dfn'FCVT_S_LU_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_S_LU_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_S_LU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (writeFPRS ((rd, (((fun (a : HolFloat 23 8) => (a.sign ++ a.exponent ++ a.significand).cast (by decide)) (holRealToFloat r ((((BitVec.setWidth 65 ((BitVec.ofNat 1 0) ++ (GPR rs state)))).toInt) : Rat)))))) state)))

/-- HOL `riscv$dfn'FCVT_S_L` (`dfn'FCVT_S_L_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_S_L_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_S_L» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (writeFPRS ((rd, (((fun (a : HolFloat 23 8) => (a.sign ++ a.exponent ++ a.significand).cast (by decide)) (holRealToFloat r (((GPR rs state).toInt) : Rat)))))) state)))

/-- HOL `riscv$dfn'FCVT_S_D` (`dfn'FCVT_S_D_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_S_D_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_S_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (writeFPRS ((rd, ((holFp64ToFp32 r (FPRD rs state))))) state)))

/-- HOL `riscv$dfn'FCVT_L_S` (`dfn'FCVT_L_S_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_L_S_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_L_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (let v : (BitVec 32) := (FPRS rs state); (let val : Int := (holThe ((holFloatToInt r ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8)))); («write'GPR» ((((if ((((holFloatIsNan ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8))) || ((v == (BitVec.ofNat 32 2139095040))))) then ((BitVec.ofNat 64 (((2 ^ 63) - 1)))) else ((if ((v == (BitVec.ofNat 32 4286578688))) then ((-((BitVec.ofNat 64 (2 ^ 63))))) else ((if ((decide (val > (((((Int.ofNat 2) ^ 63)) - (Int.ofNat 1)))))) then ((BitVec.ofNat 64 (((2 ^ 63) - 1)))) else ((if ((decide (val < ((-(((Int.ofNat 2) ^ 63))))))) then ((-((BitVec.ofNat 64 (2 ^ 63))))) else (BitVec.ofInt 64 val))))))))), rd)) state)))))

/-- HOL `riscv$dfn'FCVT_L_D` (`dfn'FCVT_L_D_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_L_D_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_L_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (let v : (BitVec 64) := (FPRD rs state); (let val : Int := (holThe ((holFloatToInt r ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11)))); («write'GPR» ((((if ((((holFloatIsNan ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11))) || ((v == (BitVec.ofNat 64 9218868437227405312))))) then ((BitVec.ofNat 64 (((2 ^ 63) - 1)))) else ((if ((v == (BitVec.ofNat 64 18442240474082181120))) then ((-((BitVec.ofNat 64 (2 ^ 63))))) else ((if ((decide (val > (((((Int.ofNat 2) ^ 63)) - (Int.ofNat 1)))))) then ((BitVec.ofNat 64 (((2 ^ 63) - 1)))) else ((if ((decide (val < ((-(((Int.ofNat 2) ^ 63))))))) then ((-((BitVec.ofNat 64 (2 ^ 63))))) else (BitVec.ofInt 64 val))))))))), rd)) state)))))

/-- HOL `riscv$dfn'FCVT_LU_S` (`dfn'FCVT_LU_S_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_LU_S_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_LU_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (let v : (BitVec 32) := (FPRS rs state); (let val : Int := (holThe ((holFloatToInt r ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8)))); («write'GPR» ((((if ((((holFloatIsNan ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8))) || ((v == (BitVec.ofNat 32 2139095040))))) then ((BitVec.ofNat 64 (((2 ^ 64) - 1)))) else ((if ((v == (BitVec.ofNat 32 4286578688))) then (BitVec.ofNat 64 0) else ((if ((decide (val > (((((Int.ofNat 2) ^ 64)) - (Int.ofNat 1)))))) then ((BitVec.ofNat 64 (((2 ^ 64) - 1)))) else ((if ((decide (val < (Int.ofNat 0)))) then (BitVec.ofNat 64 0) else (BitVec.ofInt 64 val))))))))), rd)) state)))))

/-- HOL `riscv$dfn'FCVT_LU_D` (`dfn'FCVT_LU_D_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_LU_D_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_LU_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (let v : (BitVec 64) := (FPRD rs state); (let val : Int := (holThe ((holFloatToInt r ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11)))); («write'GPR» ((((if ((((holFloatIsNan ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11))) || ((v == (BitVec.ofNat 64 9218868437227405312))))) then ((BitVec.ofNat 64 (((2 ^ 64) - 1)))) else ((if ((v == (BitVec.ofNat 64 18442240474082181120))) then (BitVec.ofNat 64 0) else ((if ((decide (val > (((((Int.ofNat 2) ^ 64)) - (Int.ofNat 1)))))) then ((BitVec.ofNat 64 (((2 ^ 64) - 1)))) else ((if ((decide (val < (Int.ofNat 0)))) then (BitVec.ofNat 64 0) else (BitVec.ofInt 64 val))))))))), rd)) state)))))

/-- HOL `riscv$dfn'FCVT_D_WU` (`dfn'FCVT_D_WU_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_D_WU_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_D_WU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (writeFPRD ((rd, ((holIntToFp64 r (((BitVec.setWidth 33 ((BitVec.ofNat 1 0) ++ ((holWordExtract 32 31 0 (GPR rs state)))))).toInt))))) state)))

/-- HOL `riscv$dfn'FCVT_D_W` (`dfn'FCVT_D_W_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_D_W_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_D_W» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (writeFPRD ((rd, ((holIntToFp64 r (((holWordExtract 32 31 0 (GPR rs state))).toInt))))) state)))

/-- HOL `riscv$dfn'FCVT_D_S` (`dfn'FCVT_D_S_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_D_S_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_D_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some _r => (writeFPRD ((rd, ((holFp32ToFp64 (FPRS rs state))))) state)))

/-- HOL `riscv$dfn'FCVT_D_LU` (`dfn'FCVT_D_LU_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_D_LU_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_D_LU» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (writeFPRD ((rd, ((holIntToFp64 r (((BitVec.setWidth 65 ((BitVec.ofNat 1 0) ++ (GPR rs state)))).toInt))))) state)))

/-- HOL `riscv$dfn'FCVT_D_L` (`dfn'FCVT_D_L_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCVT_D_L_def" (reals_as_rational_cuts)]
noncomputable def «dfn'FCVT_D_L» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 3)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs, fprnd)) =>
  (fun (state : riscv_state) => (match (round fprnd state) with | none => (signalException ExceptionType.Illegal_Instr state) | some r => (writeFPRD ((rd, ((holIntToFp64 r ((GPR rs state).toInt))))) state)))

/-- HOL `riscv$FP32_IsSignalingNan` (`FP32_IsSignalingNan_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "FP32_IsSignalingNan_def"]
def FP32_IsSignalingNan (x : (BitVec 32)) : Bool :=
  ((((holWordExtract 8 30 23 x) == (BitVec.ofNat 8 255))) && (((((x.getLsbD 22) == false)) && ((!(((holWordExtract 22 21 0 x) == (BitVec.ofNat 22 0))))))))

/-- HOL `riscv$RV32_CanonicalNan` (`RV32_CanonicalNan_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "RV32_CanonicalNan_def"]
def RV32_CanonicalNan  : (BitVec 32) :=
  (BitVec.ofNat 32 2143289344)

/-- HOL `riscv$dfn'FCLASS_S` (`dfn'FCLASS_S_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCLASS_S_def"]
def «dfn'FCLASS_S» (arg0 : ((BitVec 5) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, rs) =>
  (fun (state : riscv_state) => (match ((FPRS rs state), (((BitVec.ofNat 10 0), state))) with | (v, s) => («write'GPR» ((((BitVec.setWidth 64 ((holBitFieldInsert 9 9 ((holV2w 1 (((v == RV32_CanonicalNan) :: (([] : (List Bool))))))) ((holBitFieldInsert 8 8 ((holV2w 1 (((FP32_IsSignalingNan v) :: (([] : (List Bool))))))) ((holBitFieldInsert 7 7 ((holV2w 1 ((((v == (BitVec.ofNat 32 2139095040))) :: (([] : (List Bool))))))) ((holBitFieldInsert 6 6 ((holV2w 1 ((((((!(FP32_Sign v))) && ((holFloatIsNormal ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8))))) :: (([] : (List Bool))))))) ((holBitFieldInsert 5 5 ((holV2w 1 ((((((!(FP32_Sign v))) && ((holFloatIsSubnormal ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8))))) :: (([] : (List Bool))))))) ((holBitFieldInsert 4 4 ((holV2w 1 ((((v == (BitVec.ofNat 32 0))) :: (([] : (List Bool))))))) ((holBitFieldInsert 3 3 ((holV2w 1 ((((v == (BitVec.ofNat 32 2147483648))) :: (([] : (List Bool))))))) ((holBitFieldInsert 2 2 ((holV2w 1 (((((FP32_Sign v) && ((holFloatIsSubnormal ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8))))) :: (([] : (List Bool))))))) ((holBitFieldInsert 1 1 ((holV2w 1 (((((FP32_Sign v) && ((holFloatIsNormal ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8))))) :: (([] : (List Bool))))))) ((holBitFieldInsert 0 0 ((holV2w 1 ((((v == (BitVec.ofNat 32 4286578688))) :: (([] : (List Bool))))))) s.1)))))))))))))))))))))), rd)) s.2)))

/-- HOL `riscv$FP64_IsSignalingNan` (`FP64_IsSignalingNan_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "FP64_IsSignalingNan_def"]
def FP64_IsSignalingNan (x : (BitVec 64)) : Bool :=
  ((((holWordExtract 11 62 52 x) == (BitVec.ofNat 11 2047))) && (((((x.getLsbD 51) == false)) && ((!(((holWordExtract 51 50 0 x) == (BitVec.ofNat 51 0))))))))

/-- HOL `riscv$RV64_CanonicalNan` (`RV64_CanonicalNan_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "RV64_CanonicalNan_def"]
def RV64_CanonicalNan  : (BitVec 64) :=
  (BitVec.ofNat 64 9221120237041090560)

/-- HOL `riscv$dfn'FCLASS_D` (`dfn'FCLASS_D_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FCLASS_D_def"]
def «dfn'FCLASS_D» (arg0 : ((BitVec 5) × (BitVec 5))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, rs) =>
  (fun (state : riscv_state) => (match ((FPRD rs state), (((BitVec.ofNat 10 0), state))) with | (v, s) => («write'GPR» ((((BitVec.setWidth 64 ((holBitFieldInsert 9 9 ((holV2w 1 (((v == RV64_CanonicalNan) :: (([] : (List Bool))))))) ((holBitFieldInsert 8 8 ((holV2w 1 (((FP64_IsSignalingNan v) :: (([] : (List Bool))))))) ((holBitFieldInsert 7 7 ((holV2w 1 ((((v == (BitVec.ofNat 64 9218868437227405312))) :: (([] : (List Bool))))))) ((holBitFieldInsert 6 6 ((holV2w 1 ((((((!(FP64_Sign v))) && ((holFloatIsNormal ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11))))) :: (([] : (List Bool))))))) ((holBitFieldInsert 5 5 ((holV2w 1 ((((((!(FP64_Sign v))) && ((holFloatIsSubnormal ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11))))) :: (([] : (List Bool))))))) ((holBitFieldInsert 4 4 ((holV2w 1 ((((v == (BitVec.ofNat 64 0))) :: (([] : (List Bool))))))) ((holBitFieldInsert 3 3 ((holV2w 1 ((((v == (BitVec.ofNat 64 9223372036854775808))) :: (([] : (List Bool))))))) ((holBitFieldInsert 2 2 ((holV2w 1 (((((FP64_Sign v) && ((holFloatIsSubnormal ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11))))) :: (([] : (List Bool))))))) ((holBitFieldInsert 1 1 ((holV2w 1 (((((FP64_Sign v) && ((holFloatIsNormal ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11))))) :: (([] : (List Bool))))))) ((holBitFieldInsert 0 0 ((holV2w 1 ((((v == (BitVec.ofNat 64 18442240474082181120))) :: (([] : (List Bool))))))) s.1)))))))))))))))))))))), rd)) s.2)))

/-- HOL `riscv$dfn'FMIN_S` (`dfn'FMIN_S_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FMIN_S_def" (reals_as_rational_cuts)]
def «dfn'FMIN_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 32) := (FPRS rs1 state); (let v0 : (BitVec 32) := (FPRS rs2 state); (writeFPRS ((rd, ((match (holFloatCompare ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8) ({ sign := v0.extractLsb' 31 1, exponent := v0.extractLsb' 23 8, significand := v0.extractLsb' 0 23 } : HolFloat 23 8)) with | .lt => v | .eq => v | .gt => v0 | .un => (if (((((FP32_IsSignalingNan v) || (FP32_IsSignalingNan v0))) || (((v == RV32_CanonicalNan) && (v0 == RV32_CanonicalNan))))) then RV32_CanonicalNan else ((if (v == RV32_CanonicalNan) then v0 else v))))))) state))))

/-- HOL `riscv$dfn'FMIN_D` (`dfn'FMIN_D_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FMIN_D_def" (reals_as_rational_cuts)]
def «dfn'FMIN_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (FPRD rs1 state); (let v0 : (BitVec 64) := (FPRD rs2 state); (writeFPRD ((rd, ((match (holFloatCompare ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11) ({ sign := v0.extractLsb' 63 1, exponent := v0.extractLsb' 52 11, significand := v0.extractLsb' 0 52 } : HolFloat 52 11)) with | .lt => v | .eq => v | .gt => v0 | .un => (if (((((FP64_IsSignalingNan v) || (FP64_IsSignalingNan v0))) || (((v == RV64_CanonicalNan) && (v0 == RV64_CanonicalNan))))) then RV64_CanonicalNan else ((if (v == RV64_CanonicalNan) then v0 else v))))))) state))))

/-- HOL `riscv$dfn'FMAX_S` (`dfn'FMAX_S_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FMAX_S_def" (reals_as_rational_cuts)]
def «dfn'FMAX_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 32) := (FPRS rs1 state); (let v0 : (BitVec 32) := (FPRS rs2 state); (writeFPRS ((rd, ((match (holFloatCompare ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8) ({ sign := v0.extractLsb' 31 1, exponent := v0.extractLsb' 23 8, significand := v0.extractLsb' 0 23 } : HolFloat 23 8)) with | .lt => v0 | .eq => v0 | .gt => v | .un => (if (((((FP32_IsSignalingNan v) || (FP32_IsSignalingNan v0))) || (((v == RV32_CanonicalNan) && (v0 == RV32_CanonicalNan))))) then RV32_CanonicalNan else ((if (v == RV32_CanonicalNan) then v0 else v))))))) state))))

/-- HOL `riscv$dfn'FMAX_D` (`dfn'FMAX_D_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FMAX_D_def" (reals_as_rational_cuts)]
def «dfn'FMAX_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (FPRD rs1 state); (let v0 : (BitVec 64) := (FPRD rs2 state); (writeFPRD ((rd, ((match (holFloatCompare ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11) ({ sign := v0.extractLsb' 63 1, exponent := v0.extractLsb' 52 11, significand := v0.extractLsb' 0 52 } : HolFloat 52 11)) with | .lt => v0 | .eq => v0 | .gt => v | .un => (if (((((FP64_IsSignalingNan v) || (FP64_IsSignalingNan v0))) || (((v == RV64_CanonicalNan) && (v0 == RV64_CanonicalNan))))) then RV64_CanonicalNan else ((if (v == RV64_CanonicalNan) then v0 else v))))))) state))))

/-- HOL `riscv$write'fcsr` (`write'fcsr_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "write'fcsr_def"]
def «write'fcsr» (value : FPCSR) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => (let s : riscv_state := (let r := state; { r with c_UCSR := ((fun (_eta1 : ((BitVec 8) → UserCSR)) => ((holUpdate state.procID ((let r := (state.c_UCSR state.procID); { r with fpcsr := ((fun (_eta1 : FPCSR) => value)) r.fpcsr })) state.c_UCSR)))) r.c_UCSR }); (let s_1 : riscv_state := (let v : MachineCSR := (s.c_MCSR s.procID); (let r := s; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate s.procID ((let r := v; { r with mstatus := ((fun (_eta1 : mstatus) => ((let r := v.mstatus; { r with MFS := ((fun (_eta1 : (BitVec 2)) => (ext_status ExtStatus.Dirty))) r.MFS })))) r.mstatus })) s.c_MCSR)))) r.c_MCSR })); (let v : MachineCSR := (s_1.c_MCSR s_1.procID); (let r := s_1; { r with c_MCSR := ((fun (_eta1 : ((BitVec 8) → MachineCSR)) => ((holUpdate s_1.procID ((let r := v; { r with mstatus := ((fun (_eta1 : mstatus) => ((let r := v.mstatus; { r with MSD := ((fun (_eta1 : Bool) => true)) r.MSD })))) r.mstatus })) s_1.c_MCSR)))) r.c_MCSR })))))

/-- HOL `riscv$setFP_Invalid` (`setFP_Invalid_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "setFP_Invalid_def"]
def setFP_Invalid (_u_ : Unit) : (riscv_state → riscv_state) :=
  (fun (state : riscv_state) => («write'fcsr» ((let r := (fcsr state); { r with NV := ((fun (_eta1 : Bool) => true)) r.NV })) state))

/-- HOL `riscv$dfn'FLT_S` (`dfn'FLT_S_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FLT_S_def" (reals_as_rational_cuts)]
def «dfn'FLT_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 32) := (FPRS rs1 state); (let v0 : (BitVec 32) := (FPRS rs2 state); (if ((((holFloatIsNan ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8))) || ((holFloatIsNan ({ sign := v0.extractLsb' 31 1, exponent := v0.extractLsb' 23 8, significand := v0.extractLsb' 0 23 } : HolFloat 23 8))))) then ((setFP_Invalid () ((«write'GPR» (((BitVec.ofNat 64 0), rd)) state)))) else ((«write'GPR» ((((match (holFloatCompare ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8) ({ sign := v0.extractLsb' 31 1, exponent := v0.extractLsb' 23 8, significand := v0.extractLsb' 0 23 } : HolFloat 23 8)) with | .lt => (BitVec.ofNat 64 1) | .eq => (BitVec.ofNat 64 0) | .gt => (BitVec.ofNat 64 0) | .un => (BitVec.ofNat 64 0))), rd)) state))))))

/-- HOL `riscv$dfn'FLT_D` (`dfn'FLT_D_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FLT_D_def" (reals_as_rational_cuts)]
def «dfn'FLT_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (FPRD rs1 state); (let v0 : (BitVec 64) := (FPRD rs2 state); (if ((((holFloatIsNan ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11))) || ((holFloatIsNan ({ sign := v0.extractLsb' 63 1, exponent := v0.extractLsb' 52 11, significand := v0.extractLsb' 0 52 } : HolFloat 52 11))))) then ((setFP_Invalid () ((«write'GPR» (((BitVec.ofNat 64 0), rd)) state)))) else ((«write'GPR» ((((match (holFloatCompare ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11) ({ sign := v0.extractLsb' 63 1, exponent := v0.extractLsb' 52 11, significand := v0.extractLsb' 0 52 } : HolFloat 52 11)) with | .lt => (BitVec.ofNat 64 1) | .eq => (BitVec.ofNat 64 0) | .gt => (BitVec.ofNat 64 0) | .un => (BitVec.ofNat 64 0))), rd)) state))))))

/-- HOL `riscv$dfn'FLE_S` (`dfn'FLE_S_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FLE_S_def" (reals_as_rational_cuts)]
def «dfn'FLE_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 32) := (FPRS rs1 state); (let v0 : (BitVec 32) := (FPRS rs2 state); (if ((((holFloatIsNan ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8))) || ((holFloatIsNan ({ sign := v0.extractLsb' 31 1, exponent := v0.extractLsb' 23 8, significand := v0.extractLsb' 0 23 } : HolFloat 23 8))))) then ((setFP_Invalid () ((«write'GPR» (((BitVec.ofNat 64 0), rd)) state)))) else ((«write'GPR» ((((match (holFloatCompare ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8) ({ sign := v0.extractLsb' 31 1, exponent := v0.extractLsb' 23 8, significand := v0.extractLsb' 0 23 } : HolFloat 23 8)) with | .lt => (BitVec.ofNat 64 1) | .eq => (BitVec.ofNat 64 1) | .gt => (BitVec.ofNat 64 0) | .un => (BitVec.ofNat 64 0))), rd)) state))))))

/-- HOL `riscv$dfn'FLE_D` (`dfn'FLE_D_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FLE_D_def" (reals_as_rational_cuts)]
def «dfn'FLE_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (FPRD rs1 state); (let v0 : (BitVec 64) := (FPRD rs2 state); (if ((((holFloatIsNan ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11))) || ((holFloatIsNan ({ sign := v0.extractLsb' 63 1, exponent := v0.extractLsb' 52 11, significand := v0.extractLsb' 0 52 } : HolFloat 52 11))))) then ((setFP_Invalid () ((«write'GPR» (((BitVec.ofNat 64 0), rd)) state)))) else ((«write'GPR» ((((match (holFloatCompare ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11) ({ sign := v0.extractLsb' 63 1, exponent := v0.extractLsb' 52 11, significand := v0.extractLsb' 0 52 } : HolFloat 52 11)) with | .lt => (BitVec.ofNat 64 1) | .eq => (BitVec.ofNat 64 1) | .gt => (BitVec.ofNat 64 0) | .un => (BitVec.ofNat 64 0))), rd)) state))))))

/-- HOL `riscv$dfn'FEQ_S` (`dfn'FEQ_S_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FEQ_S_def" (reals_as_rational_cuts)]
def «dfn'FEQ_S» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 32) := (FPRS rs1 state); (let v0 : (BitVec 32) := (FPRS rs2 state); (if (((FP32_IsSignalingNan v) || (FP32_IsSignalingNan v0))) then ((setFP_Invalid () ((«write'GPR» (((BitVec.ofNat 64 0), rd)) state)))) else ((«write'GPR» ((((match (holFloatCompare ({ sign := v.extractLsb' 31 1, exponent := v.extractLsb' 23 8, significand := v.extractLsb' 0 23 } : HolFloat 23 8) ({ sign := v0.extractLsb' 31 1, exponent := v0.extractLsb' 23 8, significand := v0.extractLsb' 0 23 } : HolFloat 23 8)) with | .lt => (BitVec.ofNat 64 0) | .eq => (BitVec.ofNat 64 1) | .gt => (BitVec.ofNat 64 0) | .un => (BitVec.ofNat 64 0))), rd)) state))))))

/-- HOL `riscv$dfn'FEQ_D` (`dfn'FEQ_D_def`), mechanically rendered from the elaborated HOL definition. Uses the original fixed binary32/binary64 field codecs and generic IEEE value/comparison operations with `(reals_as_rational_cuts)` (docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance remains open. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "dfn'FEQ_D_def" (reals_as_rational_cuts)]
def «dfn'FEQ_D» (arg0 : ((BitVec 5) × ((BitVec 5) × (BitVec 5)))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (rd, (rs1, rs2)) =>
  (fun (state : riscv_state) => (let v : (BitVec 64) := (FPRD rs1 state); (let v0 : (BitVec 64) := (FPRD rs2 state); (if (((FP64_IsSignalingNan v) || (FP64_IsSignalingNan v0))) then ((setFP_Invalid () ((«write'GPR» (((BitVec.ofNat 64 0), rd)) state)))) else ((«write'GPR» ((((match (holFloatCompare ({ sign := v.extractLsb' 63 1, exponent := v.extractLsb' 52 11, significand := v.extractLsb' 0 52 } : HolFloat 52 11) ({ sign := v0.extractLsb' 63 1, exponent := v0.extractLsb' 52 11, significand := v0.extractLsb' 0 52 } : HolFloat 52 11)) with | .lt => (BitVec.ofNat 64 0) | .eq => (BitVec.ofNat 64 1) | .gt => (BitVec.ofNat 64 0) | .un => (BitVec.ofNat 64 0))), rd)) state))))))

/-- HOL `riscv$NextFetch` (`NextFetch_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "NextFetch_def"]
def NextFetch (state : riscv_state) : (Option TransferControl) :=
  (state.c_NextFetch state.procID)


end Flapjack.RiscV.L3
