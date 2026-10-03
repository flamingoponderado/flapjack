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

HEADERS=['riscv_encode_fail_type=:instruction list', 'riscv_encode_fail_hypotheses=0', 'riscv_encode_type=:instruction -> word8 list', 'riscv_encode_hypotheses=0', 'riscv_bop_r_type=:binop -> word5 # word5 # word5 -> ArithR', 'riscv_bop_r_hypotheses=0', 'riscv_bop_i_type=:binop -> word5 # word5 # word12 -> ArithI', 'riscv_bop_i_hypotheses=0', 'riscv_sh_type=:shift -> word5 # word5 # word6 -> Shift', 'riscv_sh_hypotheses=0', 'riscv_shv_type=:shift -> word5 # word5 # word5 -> Shift', 'riscv_shv_hypotheses=0', 'riscv_memop_type=:memop -> (word5 # word5 # word12 -> Load) + (word5 # word5 # word12 -> Store)', 'riscv_memop_hypotheses=0', 'riscv_const32_type=:word5 -> word32 -> instruction list', 'riscv_const32_hypotheses=0', 'riscv_ast_type=:64 asm -> instruction list', 'riscv_ast_hypotheses=0', 'riscv_enc_type=:64 asm -> word8 list', 'riscv_enc_hypotheses=0', 'riscv_bop_i_clauses=riscv_bop_i Add = ADDI ∧ riscv_bop_i And = ANDI ∧ riscv_bop_i Or = ORI ∧ riscv_bop_i Xor = XORI', 'riscv_sh_clauses=riscv_sh Lsl = SLLI ∧ riscv_sh Lsr = SRLI ∧ riscv_sh Asr = SRAI', 'riscv_shv_clauses=riscv_shv Lsl = SLL ∧ riscv_shv Lsr = SRL ∧ riscv_shv Asr = SRA', 'bop_i_undefined=riscv_bop_i Sub', 'sh_undefined=riscv_sh Ror', 'shv_undefined=riscv_shv Ror']
def capture(text):
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
    for row in samples():
        label=row['label'];ast=renderer.tm(ast_term(rows[label+'_ast']),{});bs=byte_values(rows[label+'_bytes']);encoded='['+', '.join(f'{v}#8' for v in bs)+']'
        out+=f'-- Oracle {label}: complete original AST and byte result.\nexample : riscvAst ({row["lean"]}) = {ast} := by decide\nexample : riscvEnc ({row["lean"]}) = {encoded} := by decide\n\n'
    return out+'end Flapjack.Test.RiscVNativeTargetParity\n'

if __name__=='__main__':
    result=fixture((ROOT/'scripts/hol-probes/l3_target_encoder_probe.out').read_text())
    p=ROOT/'Flapjack/Test/RiscVNativeTargetParity.lean'
    if sys.argv[1:]==['--update']:p.write_text(result)
    elif sys.argv[1:] or p.read_text()!=result:raise SystemExit('native target fixture drift')
    print(f'PASS {len(samples())} complete original target AST lists and byte lists/kernel replay fixtures')
