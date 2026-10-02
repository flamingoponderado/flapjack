import Flapjack.RiscV.L3.Defs
import Flapjack.RiscV.L3.Defs.MMU.Translate
import Flapjack.RiscV.L3.Defs.ReadInst

namespace Flapjack.RiscV.L3

/-- Source review: original model riscvScript.sml:11947-12156, distinct from
riscv_step Fetch. The Unit argument and full native state/carriers are retained.
Odd PC returns FETCH_MISALIGNED before translation, with the original state.
NONE translation returns FETCH_FAULT with the returned state. SOME reads the raw
instruction, then writes all nine Delta fields in literal source order:
exc_taken=false, fetch_exc=false, pc=virtual PC, rinstr=raw instruction,
addr/data1/data2/fp_data/st_width=NONE. The current-core Skip and MMU state effects
are retained; no alignment, successful-translation or core-bound premise. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "Fetch_def"]
noncomputable def Fetch (_u_ : Unit) : (riscv_state → (FetchResult × riscv_state)) :=
  (fun (state : riscv_state) => (let v : (BitVec 64) := (PC state); (if (v.getLsbD 0) then ((((FetchResult.F_Error ((instruction.Internal (Internal.FETCH_MISALIGNED v))))), state)) else ((match (translateAddr ((v, (fetchType.Instruction, accessType.Read))) state) with | (v0, s) => (match v0 with | none => (((FetchResult.F_Error ((instruction.Internal (Internal.FETCH_FAULT v))))), s) | some pPC => (match (rawReadInst pPC s) with | (v0_1, s_1) => ((FetchResult.F_Result v0_1), ((match (let s0 : riscv_state := («write'Delta» ((let r := (Delta s_1); { r with exc_taken := ((fun (_eta1 : Bool) => false)) r.exc_taken })) s_1); ((Delta s0), s0)) with | (v1, s) => (match (let s0 : riscv_state := («write'Delta» ((let r := v1; { r with fetch_exc := ((fun (_eta1 : Bool) => false)) r.fetch_exc })) s); ((Delta s0), s0)) with | (v1_1, s_1) => (match (let s0 : riscv_state := («write'Delta» ((let r := v1_1; { r with pc := ((fun (_eta1 : (BitVec 64)) => v)) r.pc })) s_1); ((Delta s0), s0)) with | (v1, s) => (match (let s0 : riscv_state := («write'Delta» ((let r := v1; { r with rinstr := ((fun (_eta1 : rawInstType) => v0_1)) r.rinstr })) s); ((Delta s0), s0)) with | (v_1, s_1) => (match (let s0 : riscv_state := («write'Delta» ((let r := v_1; { r with addr := ((fun (_eta1 : (Option (BitVec 64))) => ((none : (Option (BitVec 64)))))) r.addr })) s_1); ((Delta s0), s0)) with | (v_2, s) => (match (let s0 : riscv_state := («write'Delta» ((let r := v_2; { r with data1 := ((fun (_eta1 : (Option (BitVec 64))) => ((none : (Option (BitVec 64)))))) r.data1 })) s); ((Delta s0), s0)) with | (v_1, s_1) => (match (let s0 : riscv_state := («write'Delta» ((let r := v_1; { r with data2 := ((fun (_eta1 : (Option (BitVec 64))) => ((none : (Option (BitVec 64)))))) r.data2 })) s_1); ((Delta s0), s0)) with | (v_2, s) => (match (let s0 : riscv_state := («write'Delta» ((let r := v_2; { r with fp_data := ((fun (_eta1 : (Option (BitVec 64))) => ((none : (Option (BitVec 64)))))) r.fp_data })) s); ((Delta s0), s0)) with | (v_1, s_1) => («write'Delta» ((let r := v_1; { r with st_width := ((fun (_eta1 : (Option (BitVec 32))) => ((none : (Option (BitVec 32)))))) r.st_width })) s_1))))))))))))))))))

end Flapjack.RiscV.L3
