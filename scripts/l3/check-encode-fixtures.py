#!/usr/bin/env python3
"""Complete native AST Encode observations from original HOL, kernel replayed.
Finite observations are regression evidence, not universal HOL-to-Lean agreement.
"""
from pathlib import Path
import re,sys
ROOT=Path(__file__).resolve().parents[2]
# Accepted whole instruction AST; outer/inner constructors and original word widths.
CLAUSES = (('AMO', 'AMOADD_D', (1, 1, 5, 5, 5)), ('AMO', 'AMOADD_W', (1, 1, 5, 5, 5)), ('AMO', 'AMOAND_D', (1, 1, 5, 5, 5)), ('AMO', 'AMOAND_W', (1, 1, 5, 5, 5)), ('AMO', 'AMOMAXU_D', (1, 1, 5, 5, 5)), ('AMO', 'AMOMAXU_W', (1, 1, 5, 5, 5)), ('AMO', 'AMOMAX_D', (1, 1, 5, 5, 5)), ('AMO', 'AMOMAX_W', (1, 1, 5, 5, 5)), ('AMO', 'AMOMINU_D', (1, 1, 5, 5, 5)), ('AMO', 'AMOMINU_W', (1, 1, 5, 5, 5)), ('AMO', 'AMOMIN_D', (1, 1, 5, 5, 5)), ('AMO', 'AMOMIN_W', (1, 1, 5, 5, 5)), ('AMO', 'AMOOR_D', (1, 1, 5, 5, 5)), ('AMO', 'AMOOR_W', (1, 1, 5, 5, 5)), ('AMO', 'AMOSWAP_D', (1, 1, 5, 5, 5)), ('AMO', 'AMOSWAP_W', (1, 1, 5, 5, 5)), ('AMO', 'AMOXOR_D', (1, 1, 5, 5, 5)), ('AMO', 'AMOXOR_W', (1, 1, 5, 5, 5)), ('AMO', 'LR_D', (1, 1, 5, 5)), ('AMO', 'LR_W', (1, 1, 5, 5)), ('AMO', 'SC_D', (1, 1, 5, 5, 5)), ('AMO', 'SC_W', (1, 1, 5, 5, 5)), ('ArithI', 'ADDI', (5, 5, 12)), ('ArithI', 'ADDIW', (5, 5, 12)), ('ArithI', 'ANDI', (5, 5, 12)), ('ArithI', 'AUIPC', (5, 20)), ('ArithI', 'LUI', (5, 20)), ('ArithI', 'ORI', (5, 5, 12)), ('ArithI', 'SLTI', (5, 5, 12)), ('ArithI', 'SLTIU', (5, 5, 12)), ('ArithI', 'XORI', (5, 5, 12)), ('ArithR', 'ADD', (5, 5, 5)), ('ArithR', 'ADDW', (5, 5, 5)), ('ArithR', 'AND', (5, 5, 5)), ('ArithR', 'OR', (5, 5, 5)), ('ArithR', 'SLT', (5, 5, 5)), ('ArithR', 'SLTU', (5, 5, 5)), ('ArithR', 'SUB', (5, 5, 5)), ('ArithR', 'SUBW', (5, 5, 5)), ('ArithR', 'XOR', (5, 5, 5)), ('Branch', 'BEQ', (5, 5, 12)), ('Branch', 'BGE', (5, 5, 12)), ('Branch', 'BGEU', (5, 5, 12)), ('Branch', 'BLT', (5, 5, 12)), ('Branch', 'BLTU', (5, 5, 12)), ('Branch', 'BNE', (5, 5, 12)), ('Branch', 'JAL', (5, 20)), ('Branch', 'JALR', (5, 5, 12)), ('FArith', 'FADD_D', (5, 5, 5, 3)), ('FArith', 'FADD_S', (5, 5, 5, 3)), ('FArith', 'FDIV_D', (5, 5, 5, 3)), ('FArith', 'FDIV_S', (5, 5, 5, 3)), ('FArith', 'FEQ_D', (5, 5, 5)), ('FArith', 'FEQ_S', (5, 5, 5)), ('FArith', 'FLE_D', (5, 5, 5)), ('FArith', 'FLE_S', (5, 5, 5)), ('FArith', 'FLT_D', (5, 5, 5)), ('FArith', 'FLT_S', (5, 5, 5)), ('FArith', 'FMADD_D', (5, 5, 5, 5, 3)), ('FArith', 'FMADD_S', (5, 5, 5, 5, 3)), ('FArith', 'FMAX_D', (5, 5, 5)), ('FArith', 'FMAX_S', (5, 5, 5)), ('FArith', 'FMIN_D', (5, 5, 5)), ('FArith', 'FMIN_S', (5, 5, 5)), ('FArith', 'FMSUB_D', (5, 5, 5, 5, 3)), ('FArith', 'FMSUB_S', (5, 5, 5, 5, 3)), ('FArith', 'FMUL_D', (5, 5, 5, 3)), ('FArith', 'FMUL_S', (5, 5, 5, 3)), ('FArith', 'FNMADD_D', (5, 5, 5, 5, 3)), ('FArith', 'FNMADD_S', (5, 5, 5, 5, 3)), ('FArith', 'FNMSUB_D', (5, 5, 5, 5, 3)), ('FArith', 'FNMSUB_S', (5, 5, 5, 5, 3)), ('FArith', 'FSQRT_D', (5, 5, 3)), ('FArith', 'FSQRT_S', (5, 5, 3)), ('FArith', 'FSUB_D', (5, 5, 5, 3)), ('FArith', 'FSUB_S', (5, 5, 5, 3)), ('FConv', 'FCLASS_D', (5, 5)), ('FConv', 'FCLASS_S', (5, 5)), ('FConv', 'FCVT_D_L', (5, 5, 3)), ('FConv', 'FCVT_D_LU', (5, 5, 3)), ('FConv', 'FCVT_D_S', (5, 5, 3)), ('FConv', 'FCVT_D_W', (5, 5, 3)), ('FConv', 'FCVT_D_WU', (5, 5, 3)), ('FConv', 'FCVT_LU_D', (5, 5, 3)), ('FConv', 'FCVT_LU_S', (5, 5, 3)), ('FConv', 'FCVT_L_D', (5, 5, 3)), ('FConv', 'FCVT_L_S', (5, 5, 3)), ('FConv', 'FCVT_S_D', (5, 5, 3)), ('FConv', 'FCVT_S_L', (5, 5, 3)), ('FConv', 'FCVT_S_LU', (5, 5, 3)), ('FConv', 'FCVT_S_W', (5, 5, 3)), ('FConv', 'FCVT_S_WU', (5, 5, 3)), ('FConv', 'FCVT_WU_D', (5, 5, 3)), ('FConv', 'FCVT_WU_S', (5, 5, 3)), ('FConv', 'FCVT_W_D', (5, 5, 3)), ('FConv', 'FCVT_W_S', (5, 5, 3)), ('FConv', 'FMV_D_X', (5, 5)), ('FConv', 'FMV_S_X', (5, 5)), ('FConv', 'FMV_X_D', (5, 5)), ('FConv', 'FMV_X_S', (5, 5)), ('FConv', 'FSGNJN_D', (5, 5, 5)), ('FConv', 'FSGNJN_S', (5, 5, 5)), ('FConv', 'FSGNJX_D', (5, 5, 5)), ('FConv', 'FSGNJX_S', (5, 5, 5)), ('FConv', 'FSGNJ_D', (5, 5, 5)), ('FConv', 'FSGNJ_S', (5, 5, 5)), ('FENCE', None, (5, 5, 4, 4)), ('FENCE_I', None, (5, 5, 12)), ('FPLoad', 'FLD', (5, 5, 12)), ('FPLoad', 'FLW', (5, 5, 12)), ('FPStore', 'FSD', (5, 5, 12)), ('FPStore', 'FSW', (5, 5, 12)), ('Internal', 'FETCH_FAULT', (64,)), ('Internal', 'FETCH_MISALIGNED', (64,)), ('Load', 'LB', (5, 5, 12)), ('Load', 'LBU', (5, 5, 12)), ('Load', 'LD', (5, 5, 12)), ('Load', 'LH', (5, 5, 12)), ('Load', 'LHU', (5, 5, 12)), ('Load', 'LW', (5, 5, 12)), ('Load', 'LWU', (5, 5, 12)), ('MulDiv', 'DIV', (5, 5, 5)), ('MulDiv', 'DIVU', (5, 5, 5)), ('MulDiv', 'DIVUW', (5, 5, 5)), ('MulDiv', 'DIVW', (5, 5, 5)), ('MulDiv', 'MUL', (5, 5, 5)), ('MulDiv', 'MULH', (5, 5, 5)), ('MulDiv', 'MULHSU', (5, 5, 5)), ('MulDiv', 'MULHU', (5, 5, 5)), ('MulDiv', 'MULW', (5, 5, 5)), ('MulDiv', 'REM', (5, 5, 5)), ('MulDiv', 'REMU', (5, 5, 5)), ('MulDiv', 'REMUW', (5, 5, 5)), ('MulDiv', 'REMW', (5, 5, 5)), ('Shift', 'SLL', (5, 5, 5)), ('Shift', 'SLLI', (5, 5, 6)), ('Shift', 'SLLIW', (5, 5, 5)), ('Shift', 'SLLW', (5, 5, 5)), ('Shift', 'SRA', (5, 5, 5)), ('Shift', 'SRAI', (5, 5, 6)), ('Shift', 'SRAIW', (5, 5, 5)), ('Shift', 'SRAW', (5, 5, 5)), ('Shift', 'SRL', (5, 5, 5)), ('Shift', 'SRLI', (5, 5, 6)), ('Shift', 'SRLIW', (5, 5, 5)), ('Shift', 'SRLW', (5, 5, 5)), ('Store', 'SB', (5, 5, 12)), ('Store', 'SD', (5, 5, 12)), ('Store', 'SH', (5, 5, 12)), ('Store', 'SW', (5, 5, 12)), ('System', 'CSRRC', (5, 5, 12)), ('System', 'CSRRCI', (5, 5, 12)), ('System', 'CSRRS', (5, 5, 12)), ('System', 'CSRRSI', (5, 5, 12)), ('System', 'CSRRW', (5, 5, 12)), ('System', 'CSRRWI', (5, 5, 12)), ('System', 'EBREAK', ()), ('System', 'ECALL', ()), ('System', 'ERET', ()), ('System', 'MRTS', ()), ('System', 'SFENCE_VM', (5,)), ('System', 'WFI', ()), ('UnknownInstruction', None, ()))

# riscv-mi restricts the native instruction AST to the riscv-zkvm integer
# subset. These original clauses are deliberately absent; the capture still
# observes them, so the excluded set is exact and fail-closed.
EXCLUDED_OUTER = ('AMO', 'FArith', 'FConv', 'FPLoad', 'FPStore')
EXCLUDED_CLAUSES = (('FENCE_I', None), ('System', 'CSRRC'), ('System', 'CSRRCI'),
    ('System', 'CSRRS'), ('System', 'CSRRSI'), ('System', 'CSRRW'), ('System', 'CSRRWI'),
    ('System', 'ERET'), ('System', 'MRTS'), ('System', 'SFENCE_VM'), ('System', 'WFI'))

def excluded(outer, inner):
    return outer in EXCLUDED_OUTER or (outer, inner) in EXCLUDED_CLAUSES

def retained_clauses():
    return tuple(c for c in CLAUSES if not excluded(c[0], c[1]))

def check_inventory(source):
    owners={}
    for name,body in re.findall(r"inductive (\w+) where\n(.*?)(?=\n(?:deriving|/--|@\[|inductive|structure|end)|\Z)",source,re.S):
        owners[name]={ctor:tuple(map(int,re.findall(r"BitVec (\d+)",rest)))
                      for ctor,rest in re.findall(r"^  \| (\w+)([^\n]*)",body,re.M)}
    expected=[]
    for outer,widths in owners['instruction'].items():
        if outer in owners:
            expected.extend((outer,inner,payload) for inner,payload in owners[outer].items())
        else:expected.append((outer,None,widths))
    retained=retained_clauses()
    if any(not any(c[:2]==e for c in CLAUSES) for e in EXCLUDED_CLAUSES):
        raise ValueError("stale riscv-mi Encode exclusion")
    if set(expected)!=set(retained) or len(expected)!=len(retained):
        raise ValueError("whole accepted AST constructor/payload coverage drift")

def cases():
    for n,(outer,inner,widths) in enumerate(CLAUSES):
        for profile in range(4 if widths else 1):
            values=[]
            for k,width in enumerate(widths):
                value=(0 if profile==0 else (2**width-1 if profile==1 else
                       ((n+1)*19+(k+1)*73+width*17 if profile==2 else
                        2**(width-1)+(k+1)*3+n))) % 2**width
                values.append(value)
            yield outer,inner,widths,profile,tuple(values)

def lean_instruction(outer,inner,widths,values):
    args=[f"{v}#{w}" for w,v in zip(widths,values)]
    if args:
        arg=args[-1]
        for value in reversed(args[:-1]):arg=f"({value}, {arg})"
        leaf=f".{inner or outer} ({arg})"
    else:leaf=f".{inner or outer}"
    return f".{outer} ({leaf})" if inner else leaf

def parse(text):
    lines=text.splitlines()
    headers=[s for s in lines if '_type=' in s or '_hypotheses=' in s]
    if headers != HEADERS:raise ValueError("original encoder type/hypothesis drift")
    data={}
    expected=[f"Encode_{inner or outer}_{profile}" for outer,inner,_,profile,_ in cases()]
    numeric=[s for s in lines if s not in headers]
    if len(numeric)!=len(expected):raise ValueError("missing/extra whole encoder observation")
    for label,row in zip(expected,numeric):
        match=re.fullmatch(re.escape(label)+r"=([0-9]+)",row)
        if match is None:raise ValueError("unreduced, reordered or duplicate original encoder observation")
        value=int(match[1])
        if value>=2**32:raise ValueError("original Encode result is not word32")
        data[label]=value
    return data

def fixture(text):
    values=parse(text)
    source="import Flapjack.RiscV.L3.Defs.Encode\n\n/-! Original HOL numeric Encode observations over every retained riscv-mi constructor,\nincluding zero/max/nonuniform/sign-bit payloads. Finite fixtures are not universal equivalence. -/\nnamespace Flapjack.Test.L3EncodeParity\nopen Flapjack.RiscV.L3\n\n"
    for outer,inner,widths,profile,payload in cases():
        if excluded(outer,inner):continue
        label=f"Encode_{inner or outer}_{profile}"
        source+=f"-- Oracle {label}\nexample : Encode ({lean_instruction(outer,inner,widths,payload)}) = {values[label]}#32 := by decide\n"
    return source+"\nend Flapjack.Test.L3EncodeParity\n"

HEADERS = ['Encode_type=:instruction -> word32', 'Encode_hypotheses=0', 'opc_type=:word8 -> word7', 'opc_hypotheses=0', 'Itype_type=:word7 # word3 # word5 # word5 # word12 -> word32', 'Itype_hypotheses=0', 'Stype_type=:word7 # word3 # word5 # word5 # word12 -> word32', 'Stype_hypotheses=0', 'Rtype_type=:word7 # word3 # word5 # word5 # word5 # word7 -> word32', 'Rtype_hypotheses=0', 'R4type_type=:word7 # word3 # word5 # word5 # word5 # word5 # word2 -> word32', 'R4type_hypotheses=0', 'SBtype_type=:word7 # word3 # word5 # word5 # word12 -> word32', 'SBtype_hypotheses=0', 'Utype_type=:word7 # word5 # word20 -> word32', 'Utype_hypotheses=0', 'UJtype_type=:word7 # word5 # word20 -> word32', 'UJtype_hypotheses=0', 'amofunc_type=:word5 # word1 # word1 -> word7', 'amofunc_hypotheses=0']
if __name__=="__main__":
    check_inventory((ROOT / "Flapjack/RiscV/L3/Types.lean").read_text())
    text=(ROOT / "scripts/hol-probes/l3_encode_probe.out").read_text()
    result=fixture(text)
    path=ROOT / "Flapjack/Test/L3EncodeParity.lean"
    if sys.argv[1:]==["--update"]:path.write_text(result)
    elif sys.argv[1:]:raise SystemExit("usage: check-encode-fixtures.py [--update]")
    elif path.read_text()!=result:raise SystemExit("Lean encoder fixtures differ from original capture")
    print(f"PASS {sum(not excluded(o,i) for o,i,*_ in cases())} original whole Encode numeric observations/{len(retained_clauses())} retained of {len(CLAUSES)} constructors and matching kernel fixtures")
