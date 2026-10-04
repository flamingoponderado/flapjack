#!/usr/bin/env python3
"""Original complete native target AST/byte observations and kernel replay.
Finite cases are regression evidence, not universal cross-language equivalence.
"""
import re,runpy,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
DECODE=runpy.run_path(str(ROOT/'scripts/l3/check-decode-fixtures.py'))
m=DECODE['m']; C,A,L,V=[m[x] for x in ['Const','Comb','Lam','Var']]

def samples():
    rows=[]
    def add(group,hol,lean):rows.append(dict(label=f'Target_{group}_{len(rows)}',hol=hol,lean=lean,group=group))
    def w(n):return f'({n%2**64}w:word64)'
    def l(n):return f'{n%2**64}#64'
    add('Skip','Inst Skip','.inst .skip')
    for r in [0,37]:
        for n in [0,2047,2048,-2048,-2049,-1,0x7fffffff,0x80000000,0xffffffff,0x100000000,0x123456787fffffff,0x1234567880000000,-2**63,2**63-1]:
            add('Const',f'Inst (Const {r} {w(n)})',f'.inst (.const {r} ({l(n)}))')
    for h,lean in [('Add','add'),('Sub','sub'),('And','and'),('Or','or'),('Xor','xor')]:
        add('BinopReg',f'Inst (Arith (Binop {h} 37 34 (Reg 35)))',f'.inst (.arith (.binop .{lean} 37 34 (.reg 35)))')
        for n in [0,2048,-1]:add('BinopImm',f'Inst (Arith (Binop {h} 37 34 (Imm {w(n)})))',f'.inst (.arith (.binop .{lean} 37 34 (.imm ({l(n)}))))')
    for h,lean in [('Lsl','lsl'),('Lsr','lsr'),('Asr','asr'),('Ror','ror')]:
        add('ShiftReg',f'Inst (Arith (Shift {h} 37 34 (Reg 35)))',f'.inst (.arith (.shift .{lean} 37 34 (.reg 35)))')
        for n in [0,1,63,64,65,-1]:add('ShiftImm',f'Inst (Arith (Shift {h} 37 34 (Imm {w(n)})))',f'.inst (.arith (.shift .{lean} 37 34 (.imm ({l(n)}))))')
    for h,lean,count in [('Div','div',3),('LongMul','longMul',4),('LongDiv','longDiv',5),('AddCarry','addCarry',4),('AddOverflow','addOverflow',4),('SubOverflow','subOverflow',4)]:
        args=' '.join(str(33+i) for i in range(count));add(h,f'Inst (Arith ({h} {args}))',f'.inst (.arith (.{lean} {args}))')
    for h,lean in [('Load','load'),('Load8','load8'),('Load16','load16'),('Load32','load32'),('Store','store'),('Store8','store8'),('Store16','store16'),('Store32','store32')]:
        for n in [0,2047,2048,-2048,-2049]:add('Mem',f'Inst (Mem {h} 37 (Addr 34 {w(n)}))',f'.inst (.mem .{lean} 37 (.addr 34 ({l(n)})))')
    fps=[('FPLess','fpLess',3),('FPLessEqual','fpLessEqual',3),('FPEqual','fpEqual',3),('FPAbs','fpAbs',2),('FPNeg','fpNeg',2),('FPSqrt','fpSqrt',2),('FPAdd','fpAdd',3),('FPSub','fpSub',3),('FPMul','fpMul',3),('FPDiv','fpDiv',3),('FPFma','fpFma',3),('FPMov','fpMov',2),('FPMovToReg','fpMovToReg',3),('FPMovFromReg','fpMovFromReg',3),('FPToInt','fpToInt',2),('FPFromInt','fpFromInt',2)]
    for h,lean,count in fps:
        args=' '.join(str(37+i) for i in range(count));add('FP',f'Inst (FP ({h} {args}))',f'.inst (.fp (.{lean} {args}))')
    for h,lean in [('Jump','jump'),('Call','call')]:
        for n in [-1048577,-1048576,-1,0,1048575,1048576,-2**63,2**63-1]:add(h,f'{h} {w(n)}',f'.{lean} ({l(n)})')
    cmps=[('Equal','equal'),('Less','less'),('Lower','lower'),('Test','test'),('NotEqual','notEqual'),('NotLess','notLess'),('NotLower','notLower'),('NotTest','notTest')]
    for h,lean in cmps:
        for kind in ['Reg','Imm']:
            for n in [-4093,-4092,-1,0,4095,4096,-2**63,2**63-1]:
                right='Reg 34' if kind=='Reg' else 'Imm '+w(-2049)
                lr='.reg 34' if kind=='Reg' else '.imm ('+l(-2049)+')'
                add('JumpCmp'+kind,f'JumpCmp {h} 37 ({right}) {w(n)}',f'.jumpCmp .{lean} 37 ({lr}) ({l(n)})')
    for r in [0,31,37]:add('JumpReg',f'JumpReg {r}',f'.jumpReg {r}')
    for r in [0,37]:
        for n in [0,2047,2048,-2048,-2049,-2**63,2**63-1]:add('Loc',f'Loc {r} {w(n)}',f'.loc {r} ({l(n)})')
    return rows


# Source inventory, not a universal correctness proof. Match the actual reviewed
# carriers (including aliases), and require every constructor in both sample
# terms. Nested Reg/Imm modes must be represented for each operator.
CARRIER_SOURCES = {
    "asm": ("HolAsm", "Flapjack/Compiler/Encoders/Asm.lean"),
    "inst": ("HolInst", "Flapjack/Compiler/Encoders/Asm.lean"),
    "arith": ("HolArith", "Flapjack/Compiler/Encoders/Asm.lean"),
    "addr": ("HolAddr", "Flapjack/Compiler/Encoders/Asm.lean"),
    "reg_imm": ("HolRegImm", "Flapjack/Compiler/Encoders/Asm.lean"),
    "binop": ("BinOp", "Flapjack/Pancake/PanLang.lean"),
    "cmp": ("Cmp", "Flapjack/Pancake/PanLang.lean"),
    "memop": ("WordMemOp", "Flapjack/MemOp.lean"),
    "shift": ("Shift", "Flapjack/AstHOL.lean"),
}
ALIASES = {"HolBinop": "Flapjack.BinOp", "HolCmp": "Flapjack.Cmp",
           "HolMemop": "Flapjack.WordMemOp"}
# riscv-mi restricts the native assembler to the riscv-zkvm integer subset:
# the original `inst` constructor `FP` and its whole `fp` datatype are absent
# from the Lean carriers. The original capture still observes the FP samples;
# they are validated but not replayed. Each exclusion is exact and fail-closed.
EXCLUDED_HOL_CONSTRUCTORS = {"inst": ("FP",)}
EXCLUDED_FAMILIES = ("fp",)
EXCLUDED_ALIASES = ("HolFp",)
EXCLUDED_GROUPS = ("FP",)
CONTRACTS = runpy.run_path(str(ROOT / "scripts/l3/lean_contracts.py"))

def hol_without_comments(text):
    # The inventories are datatype blocks and sample terms, not SML programs.
    # Preserve newlines and token separation while ignoring nested comments.
    result = []
    depth = 0
    index = 0
    while index < len(text):
        if text.startswith("(*", index):
            depth += 1
            result.append("  ")
            index += 2
        elif depth and text.startswith("*)", index):
            depth -= 1
            result.append("  ")
            index += 2
        else:
            result.append(text[index] if not depth or text[index] == "\n" else " ")
            index += 1
    if depth:
        raise ValueError("unterminated HOL inventory comment")
    return "".join(result)

def lean_constructor(name):
    return "fp" + name[2:] if name.startswith("FP") else name[0].lower() + name[1:]

def source_inventory(root=ROOT):
    asm = CONTRACTS["strip_comments"]((root / "Flapjack/Compiler/Encoders/Asm.lean").read_text())
    for alias, owner in ALIASES.items():
        declarations = re.findall(r"(?m)^abbrev\s+" + alias + r"\s*:=\s*(\S+)", asm)
        if declarations != [owner]:
            raise ValueError("native assembler alias drift: " + alias)
    for alias in EXCLUDED_ALIASES:
        if re.search(r"(?m)^abbrev\s+" + alias + r"\b", asm):
            raise ValueError("excluded riscv-mi assembler alias restored: " + alias)
    result = {}
    for family in EXCLUDED_FAMILIES:
        source = hol_without_comments((root / "cakeml/compiler/encoders/asm/asmScript.sml").read_text())
        if len(re.findall(r"(?ms)^Datatype:\s*" + family + r"\s*=(.*?)^End\b", source)) != 1:
            raise ValueError("missing/duplicate excluded original datatype: " + family)
    for family, (owner, path) in CARRIER_SOURCES.items():
        original = root / ("cakeml/semantics/astScript.sml" if family == "shift"
                           else "cakeml/compiler/encoders/asm/asmScript.sml")
        source = hol_without_comments(original.read_text())
        blocks = re.findall(r"(?ms)^Datatype:\s*" + family + r"\s*=(.*?)^End\b", source)
        if len(blocks) != 1:
            raise ValueError("missing/duplicate original datatype: " + family)
        hol = [part.strip().split()[0] for part in blocks[0].split("|")]
        excluded = EXCLUDED_HOL_CONSTRUCTORS.get(family, ())
        if not set(excluded) <= set(hol):
            raise ValueError("stale riscv-mi constructor exclusion: " + family)
        hol = [name for name in hol if name not in excluded]
        lean = CONTRACTS["strip_comments"]((root / path).read_text())
        blocks = re.findall(r"(?ms)^inductive\s+" + owner + r"\b[^\n]*\n(.*?)^\s*deriving\b", lean)
        if len(blocks) != 1:
            raise ValueError("missing/duplicate Lean carrier: " + owner)
        constructors = re.findall(r"(?m)^\s*\|\s*([A-Za-z_]\w*)", blocks[0])
        expected = [lean_constructor(name) for name in hol]
        if not hol or len(set(hol)) != len(hol) or constructors != expected:
            raise ValueError("HOL/Lean constructor inventory drift: " + family)
        result[family] = hol
    return result

def retained(rows):
    return [row for row in rows if row["group"] not in EXCLUDED_GROUPS]

def check_constructor_inventory(rows=None, root=ROOT):
    rows = retained(samples() if rows is None else rows)
    inventory = source_inventory(root)
    all_hol = {name for names in inventory.values() for name in names}
    all_lean = {lean_constructor(name) for name in all_hol}
    observed_hol, observed_lean = set(), set()
    row_tokens = []
    for row in rows:
        hol = set(re.findall(r"\b[A-Z][A-Za-z_0-9]*\b", hol_without_comments(row["hol"]))) & all_hol
        lean = set(re.findall(r"(?<!\w)\.([A-Za-z_]\w*)", CONTRACTS["strip_comments"](row["lean"]))) & all_lean
        if {lean_constructor(name) for name in hol} != lean:
            raise ValueError("HOL/Lean sample constructors disagree: " + row["label"])
        observed_hol.update(hol)
        observed_lean.update(lean)
        row_tokens.append(hol)
    if observed_hol != all_hol or observed_lean != all_lean:
        raise ValueError("missing native constructor observations: " + repr(sorted(all_hol - observed_hol)))
    for constructor, family in [("Binop", "binop"), ("Shift", "shift"), ("JumpCmp", "cmp")]:
        for operator in inventory[family]:
            for mode in inventory["reg_imm"]:
                if not any({constructor, operator, mode} <= terms for terms in row_tokens):
                    raise ValueError("missing native operand mode: " + constructor + "/" + operator + "/" + mode)
    return inventory

def check_probe_samples(rows=None, root=ROOT):
    rows = samples() if rows is None else rows
    probe = (root / "scripts/hol-probes/l3_target_encoder_probeScript.sml").read_text()
    observed = [line.strip() for line in probe.splitlines()
                if re.match(r'\s*val _ = (?:ast|bytes) "Target_', line)]
    expected = []
    quote = chr(96) * 2
    for row in rows:
        label, term = row["label"], row["hol"]
        expected.extend([
            f'val _ = ast "{label}_ast" {quote}riscv_ast ({term}){quote};',
            f'val _ = bytes "{label}_bytes" {quote}MAP w2n (riscv_enc ({term})){quote};'])
    if observed != expected:
        raise ValueError("original native target probe/sample input drift")

HEADERS=['riscv_encode_fail_type=:instruction list', 'riscv_encode_fail_hypotheses=0', 'riscv_encode_type=:instruction -> word8 list', 'riscv_encode_hypotheses=0', 'riscv_bop_r_type=:binop -> word5 # word5 # word5 -> ArithR', 'riscv_bop_r_hypotheses=0', 'riscv_bop_i_type=:binop -> word5 # word5 # word12 -> ArithI', 'riscv_bop_i_hypotheses=0', 'riscv_sh_type=:shift -> word5 # word5 # word6 -> Shift', 'riscv_sh_hypotheses=0', 'riscv_shv_type=:shift -> word5 # word5 # word5 -> Shift', 'riscv_shv_hypotheses=0', 'riscv_memop_type=:memop -> (word5 # word5 # word12 -> Load) + (word5 # word5 # word12 -> Store)', 'riscv_memop_hypotheses=0', 'riscv_const32_type=:word5 -> word32 -> instruction list', 'riscv_const32_hypotheses=0', 'riscv_ast_type=:64 asm -> instruction list', 'riscv_ast_hypotheses=0', 'riscv_enc_type=:64 asm -> word8 list', 'riscv_enc_hypotheses=0', 'riscv_bop_i_clauses=riscv_bop_i Add = ADDI ∧ riscv_bop_i And = ANDI ∧ riscv_bop_i Or = ORI ∧ riscv_bop_i Xor = XORI', 'riscv_sh_clauses=riscv_sh Lsl = SLLI ∧ riscv_sh Lsr = SRLI ∧ riscv_sh Asr = SRAI', 'riscv_shv_clauses=riscv_shv Lsl = SLL ∧ riscv_shv Lsr = SRL ∧ riscv_shv Asr = SRA', 'bop_i_undefined=riscv_bop_i Sub', 'sh_undefined=riscv_sh Ror', 'shv_undefined=riscv_shv Ror']
def capture(text):
    check_constructor_inventory()
    check_probe_samples()
    lines=text.splitlines()
    if lines[:len(HEADERS)]!=HEADERS:raise ValueError('original target types/hypotheses/unspecified clauses drift')
    rows={}
    expected=[x['label']+suffix for x in samples() for suffix in ['_ast','_bytes']]
    observed=lines[len(HEADERS):]
    if len(observed)!=len(expected):raise ValueError('missing/extra complete target observation')
    for label,line in zip(expected,observed):
        if not line.startswith(label+'='):raise ValueError('reordered/duplicate target oracle')
        rows[label]=line[len(label)+1:]
    return rows

def ast_term(value):
    terms=m['read_sexps'](value)
    if len(terms)!=1:raise ValueError('expected one original AST list')
    term=m['parse_tm'](terms[0])
    if m['type_of'](term)!=m['Ty']('list','list',(m['Ty']('riscv','instruction',()),)):raise ValueError('original AST carrier drift')
    allowed={('list','CONS'),('list','NIL'),('pair',','),('words','n2w'),('arithmetic','BIT1'),('arithmetic','BIT2'),('arithmetic','NUMERAL'),('arithmetic','ZERO'),('num','0')}
    for c in m['constants_of'](term):
        if (c.thy,c.name) not in allowed and not(c.thy=='riscv' and c.name in DECODE['constructor_names']()):raise ValueError('unreduced original target AST')
    todo=[term]
    while todo:
        t=todo.pop()
        if isinstance(t,(V,L)):raise ValueError('nonconcrete original target AST')
        if isinstance(t,A):todo.extend([t.f,t.x])
    return term

def byte_values(value):
    if not re.fullmatch(r'\[(?:[0-9]+(?:;[0-9]+)*)?\]',value):raise ValueError('unreduced or malformed original bytes')
    values=[int(x) for x in value[1:-1].split(';') if x]
    if any(x>=256 for x in values):raise ValueError('original byte not word8')
    return values

def fixture(text):
    rows=capture(text)
    renderer=m['Renderer']({},m['parse_types']((ROOT/'Flapjack/RiscV/L3/Types.lean').read_text()))
    out='import Flapjack.Compiler.Encoders.RiscV.Target\n\n/-! Original complete native target AST lists and byte lists. Finite regression\nevidence, not universal HOL-to-Lean equivalence. -/\nnamespace Flapjack.Test.RiscVNativeTargetParity\nopen Flapjack.Compiler.Encoders.RiscV.Target Flapjack.RiscV.L3\n\n'
    for row in retained(samples()):
        label=row['label'];ast=renderer.tm(ast_term(rows[label+'_ast']),{});bs=byte_values(rows[label+'_bytes']);encoded='['+', '.join(f'{v}#8' for v in bs)+']'
        out+=f'-- Oracle {label}: complete original AST and byte result.\nexample : riscvAst ({row["lean"]}) = {ast} := by decide\nexample : riscvEnc ({row["lean"]}) = {encoded} := by decide\n\n'
    return out+'end Flapjack.Test.RiscVNativeTargetParity\n'

if __name__=='__main__':
    result=fixture((ROOT/'scripts/hol-probes/l3_target_encoder_probe.out').read_text())
    p=ROOT/'Flapjack/Test/RiscVNativeTargetParity.lean'
    if sys.argv[1:]==['--update']:p.write_text(result)
    elif sys.argv[1:] or p.read_text()!=result:raise SystemExit('native target fixture drift')
    print(f'PASS {len(retained(samples()))} retained of {len(samples())} complete original target AST/byte fixtures; all source constructors and operand modes inventoried')
