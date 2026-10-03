#!/usr/bin/env python3
"""Check every original arbitrary-payload/state Run dispatch equation.

The constructor/handler inventory is source-reviewed against the entire pinned
Run_def; the three identity clauses are explicit. These HOL/Lean clause checks
verify dispatch correspondence, not independent equivalence of the handlers
or an end-to-end compiler correctness theorem.
"""
from pathlib import Path
import sys

# (outer constructor, inner constructor, payload present)
CLAUSES = (
    ('AMO', 'AMOADD_D', True),
    ('AMO', 'AMOADD_W', True),
    ('AMO', 'AMOAND_D', True),
    ('AMO', 'AMOAND_W', True),
    ('AMO', 'AMOMAXU_D', True),
    ('AMO', 'AMOMAXU_W', True),
    ('AMO', 'AMOMAX_D', True),
    ('AMO', 'AMOMAX_W', True),
    ('AMO', 'AMOMINU_D', True),
    ('AMO', 'AMOMINU_W', True),
    ('AMO', 'AMOMIN_D', True),
    ('AMO', 'AMOMIN_W', True),
    ('AMO', 'AMOOR_D', True),
    ('AMO', 'AMOOR_W', True),
    ('AMO', 'AMOSWAP_D', True),
    ('AMO', 'AMOSWAP_W', True),
    ('AMO', 'AMOXOR_D', True),
    ('AMO', 'AMOXOR_W', True),
    ('AMO', 'LR_D', True),
    ('AMO', 'LR_W', True),
    ('AMO', 'SC_D', True),
    ('AMO', 'SC_W', True),
    ('ArithI', 'ADDI', True),
    ('ArithI', 'ADDIW', True),
    ('ArithI', 'ANDI', True),
    ('ArithI', 'AUIPC', True),
    ('ArithI', 'LUI', True),
    ('ArithI', 'ORI', True),
    ('ArithI', 'SLTI', True),
    ('ArithI', 'SLTIU', True),
    ('ArithI', 'XORI', True),
    ('ArithR', 'ADD', True),
    ('ArithR', 'ADDW', True),
    ('ArithR', 'AND', True),
    ('ArithR', 'OR', True),
    ('ArithR', 'SLT', True),
    ('ArithR', 'SLTU', True),
    ('ArithR', 'SUB', True),
    ('ArithR', 'SUBW', True),
    ('ArithR', 'XOR', True),
    ('Branch', 'BEQ', True),
    ('Branch', 'BGE', True),
    ('Branch', 'BGEU', True),
    ('Branch', 'BLT', True),
    ('Branch', 'BLTU', True),
    ('Branch', 'BNE', True),
    ('Branch', 'JAL', True),
    ('Branch', 'JALR', True),
    ('FArith', 'FADD_D', True),
    ('FArith', 'FADD_S', True),
    ('FArith', 'FDIV_D', True),
    ('FArith', 'FDIV_S', True),
    ('FArith', 'FEQ_D', True),
    ('FArith', 'FEQ_S', True),
    ('FArith', 'FLE_D', True),
    ('FArith', 'FLE_S', True),
    ('FArith', 'FLT_D', True),
    ('FArith', 'FLT_S', True),
    ('FArith', 'FMADD_D', True),
    ('FArith', 'FMADD_S', True),
    ('FArith', 'FMAX_D', True),
    ('FArith', 'FMAX_S', True),
    ('FArith', 'FMIN_D', True),
    ('FArith', 'FMIN_S', True),
    ('FArith', 'FMSUB_D', True),
    ('FArith', 'FMSUB_S', True),
    ('FArith', 'FMUL_D', True),
    ('FArith', 'FMUL_S', True),
    ('FArith', 'FNMADD_D', True),
    ('FArith', 'FNMADD_S', True),
    ('FArith', 'FNMSUB_D', True),
    ('FArith', 'FNMSUB_S', True),
    ('FArith', 'FSQRT_D', True),
    ('FArith', 'FSQRT_S', True),
    ('FArith', 'FSUB_D', True),
    ('FArith', 'FSUB_S', True),
    ('FConv', 'FCLASS_D', True),
    ('FConv', 'FCLASS_S', True),
    ('FConv', 'FCVT_D_L', True),
    ('FConv', 'FCVT_D_LU', True),
    ('FConv', 'FCVT_D_S', True),
    ('FConv', 'FCVT_D_W', True),
    ('FConv', 'FCVT_D_WU', True),
    ('FConv', 'FCVT_LU_D', True),
    ('FConv', 'FCVT_LU_S', True),
    ('FConv', 'FCVT_L_D', True),
    ('FConv', 'FCVT_L_S', True),
    ('FConv', 'FCVT_S_D', True),
    ('FConv', 'FCVT_S_L', True),
    ('FConv', 'FCVT_S_LU', True),
    ('FConv', 'FCVT_S_W', True),
    ('FConv', 'FCVT_S_WU', True),
    ('FConv', 'FCVT_WU_D', True),
    ('FConv', 'FCVT_WU_S', True),
    ('FConv', 'FCVT_W_D', True),
    ('FConv', 'FCVT_W_S', True),
    ('FConv', 'FMV_D_X', True),
    ('FConv', 'FMV_S_X', True),
    ('FConv', 'FMV_X_D', True),
    ('FConv', 'FMV_X_S', True),
    ('FConv', 'FSGNJN_D', True),
    ('FConv', 'FSGNJN_S', True),
    ('FConv', 'FSGNJX_D', True),
    ('FConv', 'FSGNJX_S', True),
    ('FConv', 'FSGNJ_D', True),
    ('FConv', 'FSGNJ_S', True),
    ('FENCE', None, True),
    ('FENCE_I', None, True),
    ('FPLoad', 'FLD', True),
    ('FPLoad', 'FLW', True),
    ('FPStore', 'FSD', True),
    ('FPStore', 'FSW', True),
    ('Internal', 'FETCH_FAULT', True),
    ('Internal', 'FETCH_MISALIGNED', True),
    ('Load', 'LB', True),
    ('Load', 'LBU', True),
    ('Load', 'LD', True),
    ('Load', 'LH', True),
    ('Load', 'LHU', True),
    ('Load', 'LW', True),
    ('Load', 'LWU', True),
    ('MulDiv', 'DIV', True),
    ('MulDiv', 'DIVU', True),
    ('MulDiv', 'DIVUW', True),
    ('MulDiv', 'DIVW', True),
    ('MulDiv', 'MUL', True),
    ('MulDiv', 'MULH', True),
    ('MulDiv', 'MULHSU', True),
    ('MulDiv', 'MULHU', True),
    ('MulDiv', 'MULW', True),
    ('MulDiv', 'REM', True),
    ('MulDiv', 'REMU', True),
    ('MulDiv', 'REMUW', True),
    ('MulDiv', 'REMW', True),
    ('Shift', 'SLL', True),
    ('Shift', 'SLLI', True),
    ('Shift', 'SLLIW', True),
    ('Shift', 'SLLW', True),
    ('Shift', 'SRA', True),
    ('Shift', 'SRAI', True),
    ('Shift', 'SRAIW', True),
    ('Shift', 'SRAW', True),
    ('Shift', 'SRL', True),
    ('Shift', 'SRLI', True),
    ('Shift', 'SRLIW', True),
    ('Shift', 'SRLW', True),
    ('Store', 'SB', True),
    ('Store', 'SD', True),
    ('Store', 'SH', True),
    ('Store', 'SW', True),
    ('System', 'CSRRC', True),
    ('System', 'CSRRCI', True),
    ('System', 'CSRRS', True),
    ('System', 'CSRRSI', True),
    ('System', 'CSRRW', True),
    ('System', 'CSRRWI', True),
    ('System', 'EBREAK', False),
    ('System', 'ECALL', False),
    ('System', 'ERET', False),
    ('System', 'MRTS', False),
    ('System', 'SFENCE_VM', True),
    ('System', 'WFI', False),
    ('UnknownInstruction', None, False),
 )


def expected_rows():
    rows = {"Run_type": ":instruction -> riscv_state -> riscv_state", "Run_hypotheses": "0"}
    for outer, inner, payload in CLAUSES:
        name = inner or outer
        if inner:
            printed_inner = "$DIV" if inner == "DIV" else inner
            arg = f"({printed_inner} x)" if payload else printed_inner
            ctor = f"({outer} {arg})"
        else:
            ctor = f"({outer} x)" if payload else outer
        rhs = "s" if name in {"FENCE", "FENCE_I", "WFI"} else f"dfn'{name}" + (" x" if payload else "") + " s"
        quantifier = "∀x s." if payload else "∀s."
        rows[f"Run_{name}_equation"] = f"{quantifier} Run {ctor} s = {rhs}"
        rows[f"Run_{name}_proof"] = "T"
    return rows


def check_rows(text):
    rows = {}
    for line in text.splitlines():
        if "=" not in line:
            raise ValueError(f"unexpected capture line: {line}")
        label, value = line.split("=", 1)
        if label in rows:
            raise ValueError(f"duplicate row: {label}")
        rows[label] = value
    expected = expected_rows()
    if rows != expected:
        missing = sorted(expected.keys() - rows.keys())
        extra = sorted(rows.keys() - expected.keys())
        changed = sorted(k for k in rows.keys() & expected.keys() if rows[k] != expected[k])
        raise ValueError(f"Run capture mismatch: missing={missing}, extra={extra}, changed={changed}")


if __name__ == "__main__":
    path = Path(__file__).with_name("l3_run_dispatch_probe.out")
    try:
        check_rows(path.read_text())
    except (OSError, ValueError) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
    print("PASS all 163 original generic Run dispatch equations/proofs, exact full type and zero hypotheses")
