#!/usr/bin/env python3
"""Full target-state source/capture guard, not HOL-to-Lean equivalence."""
from pathlib import Path
import re
import shlex
ROOT = Path(__file__).resolve().parents[2]
EXPECTED = ['riscv_next_statement=∀s. riscv_next s = THE (NextRISCV s)', 'riscv_next_hypotheses=0', 'riscv_next_proved=T', 'riscv_next_type=:riscv_state -> riscv_state', 'riscv_ok_statement=∀ms. riscv_ok ms ⇔ (ms.c_MCSR ms.procID).mstatus.VM = 0w ∧ (ms.c_MCSR ms.procID).mcpuid.ArchBase = 2w ∧ ms.c_NextFetch ms.procID = NONE ∧ ms.exception = NoException ∧ aligned 2 (ms.c_PC ms.procID)', 'riscv_ok_hypotheses=0', 'riscv_ok_proved=T', 'riscv_ok_type=:riscv_state -> bool', 'riscv_proj_statement=∀d s. riscv_proj d s = ((s.c_MCSR s.procID).mstatus.VM,(s.c_MCSR s.procID).mcpuid.ArchBase,s.c_NextFetch s.procID,s.exception,s.c_gpr s.procID,fun2set (s.MEM8,d),s.c_PC s.procID)', 'riscv_proj_hypotheses=0', 'riscv_proj_proved=T', 'riscv_proj_type=:(word64 -> bool) -> riscv_state -> word5 # word2 # TransferControl option # exception # (word5 -> word64) # (word64 # word8 -> bool) # word64', 'riscv_target_statement=riscv_target = <|next := riscv_next; config := riscv_config; get_pc := (λs. s.c_PC s.procID); get_reg := (λs. s.c_gpr s.procID ∘ n2w); get_byte := riscv_state_MEM8; state_ok := riscv_ok; proj := riscv_proj|>', 'riscv_target_hypotheses=0', 'riscv_target_proved=T', 'riscv_target_type=:(64, riscv_state, word5 # word2 # TransferControl option # exception # (word5 -> word64) # (word64 # word8 -> bool) # word64) target', 'riscv_target_fp_field=ARB.get_fp_reg', 'riscv_target_fp_type=:riscv_state -> num -> word64']
HOL = {'riscv_next_def': 'riscv_next s = THE (NextRISCV s)', 'riscv_ok_def': 'riscv_ok ms <=>\n   ((ms.c_MCSR ms.procID).mstatus.VM = 0w) /\\\n   ((ms.c_MCSR ms.procID).mcpuid.ArchBase = 2w) /\\\n   (ms.c_NextFetch ms.procID = NONE) /\\\n   (ms.exception = NoException) /\\ aligned 2 (ms.c_PC ms.procID)', 'riscv_proj_def': 'riscv_proj d s =\n   ((s.c_MCSR s.procID).mstatus.VM,\n    (s.c_MCSR s.procID).mcpuid.ArchBase,\n    s.c_NextFetch s.procID,\n    s.exception,\n    s.c_gpr s.procID,\n    fun2set (s.MEM8,d),\n    s.c_PC s.procID)', 'riscv_target_def': 'riscv_target =\n   <| next := riscv_next\n    ; config := riscv_config\n    ; get_pc := (\\s. s.c_PC s.procID)\n    ; get_reg := (\\s. s.c_gpr s.procID o n2w)\n    ; get_byte := riscv_state_MEM8\n    ; state_ok := riscv_ok\n    ; proj := riscv_proj\n    |>'}
LEAN = {'riscvNext': ' (s : riscv_state) : riscv_state :=\n  holThe (RiscV.L3.Step.NextRISCV s)', 'riscvOk': ' (s : riscv_state) : Bool :=\n  ((s.c_MCSR s.procID).mstatus.VM == 0) &&\n  ((s.c_MCSR s.procID).mcpuid.ArchBase == 2) &&\n  (s.c_NextFetch s.procID == none) &&\n  (s.exception == exception.NoException) && holAligned 2 (s.c_PC s.procID)', 'riscvProj': ' (d : BitVec 64 → Prop) (s : riscv_state) : RiscVProjection :=\n  ((s.c_MCSR s.procID).mstatus.VM,\n   (s.c_MCSR s.procID).mcpuid.ArchBase,\n   s.c_NextFetch s.procID,\n   s.exception,\n   s.c_gpr s.procID,\n   SetSep.fun2Set (s.MEM8, d),\n   s.c_PC s.procID)', 'riscvTarget': ' : HolAsmTarget 64 riscv_state RiscVProjection where\n  next := riscvNext\n  config := riscvConfig\n  getPc := fun s => s.c_PC s.procID\n  getReg := fun s n => s.c_gpr s.procID (BitVec.ofNat 5 n)\n  getFpReg := (holArb (HolAsmTarget 64 riscv_state RiscVProjection)).getFpReg\n  getByte := riscv_state.MEM8\n  stateOk := riscvOk\n  proj := riscvProj'}
def check(output, original, lean, driver):
    if output.splitlines() != EXPECTED: raise ValueError("full original target capture drift")
    for name, expected in HOL.items():
        m = re.search(r"Definition " + name + r":\s*(.*?)\nEnd", original, re.S)
        if not m or "".join(m[1].split()) != "".join(expected.split()):
            raise ValueError("original target clause drift: " + name)
    for name, expected in LEAN.items():
        m = re.search(r"(?:noncomputable )?def " + name + r"\b(.*?)(?=\n\n)", lean, re.S)
        if not m or "".join(m[1].split()) != "".join(expected.split()):
            raise ValueError("reviewed Lean target clause drift: " + name)
    commands = [shlex.split(line) for line in driver.replace("\\\n", " ").splitlines()
                if line.startswith("run_probe riscv_target_state_probeScript.sml ")]
    expected = ["run_probe", "riscv_target_state_probeScript.sml", "riscv_target_state_probe.out"] + [
        row.split("=",1)[0] for row in EXPECTED] + [
        "$cake_dir/compiler/encoders/riscv/riscv_targetScript.sml", "$cake_dir/compiler/encoders/riscv"]
    if commands != [expected]: raise ValueError("full original target driver registration drift")
if __name__ == "__main__":
    check(Path(__file__).with_name("riscv_target_state_probe.out").read_text(),
          (ROOT / "cakeml/compiler/encoders/riscv/riscv_targetScript.sml").read_text(),
          (ROOT / "Flapjack/Compiler/Encoders/RiscV/Target/State.lean").read_text(),
          Path(__file__).with_name("regenerate.sh").read_text())
    print("PASS full four original target definitions, carriers, arbitrary record field and driver")
