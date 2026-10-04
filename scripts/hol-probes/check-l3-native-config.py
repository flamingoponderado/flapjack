#!/usr/bin/env python3
"""Original full native config and exact encoder-field evidence (not equivalence)."""
from pathlib import Path
import runpy
ROOT = Path(__file__).resolve().parents[2]
CONTRACTS = runpy.run_path(str(ROOT / "scripts/l3/lean_contracts.py"))
LEAN_PATH = 'Flapjack/Compiler/Encoders/RiscV/Target/Configuration.lean'
LEAN_EXPECTED = {
    'riscvConfig': """def riscvConfig : AsmConfigExact 64 where
  isa := .riscv
  encode := riscvEnc
  regCount := 32
  avoidRegs := [0,2,3,4,31]
  fpRegCount := 0
  linkReg := some 1
  twoRegArith := false
  bigEndian := false
  validImm := fun operator i =>
    (match operator with
     | .inl .sub => (-2048 : BitVec 64).slt i
     | _ => (-2048 : BitVec 64).sle i) && i.sle 2047
  addrOffset := (-2048,2047)
  hwOffset := (-2048,2047)
  byteOffset := (-2048,2047)
  jumpOffset := (-2147483648,0x7FFFF7FF)
  cjumpOffset := (-1048576+8,1048575+4)
  locOffset := (-2147483648,0x7FFFF7FF)
  codeAlignment := 2""",
}
EXPECTED = ['cfg_isa=RISC_V', 'cfg_reg_count=32', 'cfg_avoid_regs=[0; 2; 3; 4; 31]', 'cfg_fp_reg_count=0', 'cfg_link_reg=SOME 1', 'cfg_two_reg_arith=F', 'cfg_big_endian=F', 'cfg_code_alignment=2', 'cfg_addr_offset=(0xFFFFFFFFFFFFF800w,2047w)', 'cfg_hw_offset=(0xFFFFFFFFFFFFF800w,2047w)', 'cfg_byte_offset=(0xFFFFFFFFFFFFF800w,2047w)', 'cfg_jump_offset=(0xFFFFFFFF80000000w,0x7FFFF7FFw)', 'cfg_cjump_offset=(0xFFFFFFFFFFF00008w,0x100003w)', 'cfg_loc_offset=(0xFFFFFFFF80000000w,0x7FFFF7FFw)', 'valid_imm_sub_min12=F', 'valid_imm_sub_min12p1=T', 'valid_imm_add_min12=T', 'valid_imm_add_max12=T', 'valid_imm_add_max12p1=F', 'native_config_type=:64 asm_config', 'native_config_encode_type=:64 asm -> word8 list', 'native_config_hypotheses=0', 'native_config_definition=riscv_config = <|ISA := RISC_V; encode := riscv_enc; reg_count := 32; avoid_regs := [0; 2; 3; 4; 31]; fp_reg_count := 0; link_reg := SOME 1; two_reg_arith := F; big_endian := F; valid_imm := (λb i. (if b = INL Sub then 0xFFFFFFFFFFFFF800w < i else 0xFFFFFFFFFFFFF800w ≤ i) ∧ i ≤ 2047w); addr_offset := (0xFFFFFFFFFFFFF800w,2047w); hw_offset := (0xFFFFFFFFFFFFF800w,2047w); byte_offset := (0xFFFFFFFFFFFFF800w,2047w); jump_offset := (0xFFFFFFFF80000000w,0x7FFFF7FFw); cjump_offset := (0xFFFFFFFFFFF00000w + 8w,0xFFFFFw + 4w); loc_offset := (0xFFFFFFFF80000000w,0x7FFFF7FFw); code_alignment := 2|>', 'native_config_encode_equation=riscv_config.encode = riscv_enc', 'native_config_encode_hypotheses=0', 'cfg_imm_Add_0=F', 'cfg_imm_Add_1=T', 'cfg_imm_Add_2=T', 'cfg_imm_Add_3=T', 'cfg_imm_Add_4=T', 'cfg_imm_Add_5=F', 'cfg_imm_Sub_0=F', 'cfg_imm_Sub_1=F', 'cfg_imm_Sub_2=T', 'cfg_imm_Sub_3=T', 'cfg_imm_Sub_4=T', 'cfg_imm_Sub_5=F', 'cfg_imm_And_0=F', 'cfg_imm_And_1=T', 'cfg_imm_And_2=T', 'cfg_imm_And_3=T', 'cfg_imm_And_4=T', 'cfg_imm_And_5=F', 'cfg_imm_Or_0=F', 'cfg_imm_Or_1=T', 'cfg_imm_Or_2=T', 'cfg_imm_Or_3=T', 'cfg_imm_Or_4=T', 'cfg_imm_Or_5=F', 'cfg_imm_Xor_0=F', 'cfg_imm_Xor_1=T', 'cfg_imm_Xor_2=T', 'cfg_imm_Xor_3=T', 'cfg_imm_Xor_4=T', 'cfg_imm_Xor_5=F', 'cfg_imm_Equal_0=F', 'cfg_imm_Equal_1=T', 'cfg_imm_Equal_2=T', 'cfg_imm_Equal_3=T', 'cfg_imm_Equal_4=T', 'cfg_imm_Equal_5=F', 'cfg_imm_Less_0=F', 'cfg_imm_Less_1=T', 'cfg_imm_Less_2=T', 'cfg_imm_Less_3=T', 'cfg_imm_Less_4=T', 'cfg_imm_Less_5=F', 'cfg_imm_Lower_0=F', 'cfg_imm_Lower_1=T', 'cfg_imm_Lower_2=T', 'cfg_imm_Lower_3=T', 'cfg_imm_Lower_4=T', 'cfg_imm_Lower_5=F', 'cfg_imm_Test_0=F', 'cfg_imm_Test_1=T', 'cfg_imm_Test_2=T', 'cfg_imm_Test_3=T', 'cfg_imm_Test_4=T', 'cfg_imm_Test_5=F', 'cfg_imm_NotEqual_0=F', 'cfg_imm_NotEqual_1=T', 'cfg_imm_NotEqual_2=T', 'cfg_imm_NotEqual_3=T', 'cfg_imm_NotEqual_4=T', 'cfg_imm_NotEqual_5=F', 'cfg_imm_NotLess_0=F', 'cfg_imm_NotLess_1=T', 'cfg_imm_NotLess_2=T', 'cfg_imm_NotLess_3=T', 'cfg_imm_NotLess_4=T', 'cfg_imm_NotLess_5=F', 'cfg_imm_NotLower_0=F', 'cfg_imm_NotLower_1=T', 'cfg_imm_NotLower_2=T', 'cfg_imm_NotLower_3=T', 'cfg_imm_NotLower_4=T', 'cfg_imm_NotLower_5=F', 'cfg_imm_NotTest_0=F', 'cfg_imm_NotTest_1=T', 'cfg_imm_NotTest_2=T', 'cfg_imm_NotTest_3=T', 'cfg_imm_NotTest_4=T', 'cfg_imm_NotTest_5=F']
def check_lean(text):
    for name, expected in LEAN_EXPECTED.items():
        CONTRACTS["check_declaration"](text, 'def', name, expected, statement=False)

def check(text, lean=None):
    if [x for x in text.splitlines() if x] != EXPECTED:
        raise ValueError("original native config field/type/encoder/policy drift")
    check_lean((ROOT / LEAN_PATH).read_text() if lean is None else lean)

if __name__ == "__main__":
    check(Path(__file__).with_name("l3_native_config_probe.out").read_text())
    print("PASS original native config16fields/types/hyp0/encoder/78policy rows AND complete reviewed Lean config body")
