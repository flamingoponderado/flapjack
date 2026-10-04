import Flapjack.Compiler.Encoders.Asm
import Flapjack.RiscV.L3.Defs.Encode

/-! Native encoder section of `riscv_targetScript.sml`. The complete source
ASM carrier is retained at width64. Unspecified opcode helper cases use the
canonical HOL arbitrary value; their tagged results state only HOL's actual
clauses. The complete executable AST lowering splits the defined helper cases
explicitly, so it never executes those unspecified values. Configuration and
compiler route replacement remain tracked separately. -/
namespace Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack Compiler.Encoders.Asm RiscV.L3

def riscvEncodeFail : List instruction := [.ArithI (.ADDI (0,0,0))]

def riscvEncode (i : instruction) : List (BitVec 8) :=
  let w := Encode i
  [holWordExtract 8 7 0 w, holWordExtract 8 15 8 w,
   holWordExtract 8 23 16 w, holWordExtract 8 31 24 w]

def riscvBopR : BinOp → (BitVec 5 × BitVec 5 × BitVec 5 → ArithR)
  | .add => ArithR.ADD
  | .sub => ArithR.SUB
  | .and => ArithR.AND
  | .or => ArithR.OR
  | .xor => ArithR.XOR

/-- Flapjack's total representation of the source partial table. HOL states
four clauses and leaves Sub unspecified (original EVAL remains unreduced).
This extension is not tagged as a whole source definition; the exact four
function equalities are tagged below. No chosen opcode fills the missing case. -/
noncomputable def riscvBopI : BinOp → (BitVec 5 × BitVec 5 × BitVec 12 → ArithI)
  | .add => ArithI.ADDI
  | .and => ArithI.ANDI
  | .or => ArithI.ORI
  | .xor => ArithI.XORI
  | .sub => Flapjack.holArb _

theorem riscvBopIClauses :
    riscvBopI .add = ArithI.ADDI ∧ riscvBopI .and = ArithI.ANDI ∧
    riscvBopI .or = ArithI.ORI ∧ riscvBopI .xor = ArithI.XORI := by
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Flapjack total extension of the three source immediate-shift clauses.
The source leaves Ror unspecified; only its three original equalities are tagged. -/
noncomputable def riscvSh : Flapjack.Shift →
    (BitVec 5 × BitVec 5 × BitVec 6 → RiscV.L3.Shift)
  | .lsl => RiscV.L3.Shift.SLLI
  | .lsr => RiscV.L3.Shift.SRLI
  | .asr => RiscV.L3.Shift.SRAI
  | .ror => Flapjack.holArb _

theorem riscvShClauses :
    riscvSh .lsl = RiscV.L3.Shift.SLLI ∧
    riscvSh .lsr = RiscV.L3.Shift.SRLI ∧
    riscvSh .asr = RiscV.L3.Shift.SRAI := by exact ⟨rfl,rfl,rfl⟩

/-- Flapjack total extension of the three source register-shift clauses.
Ror remains unspecified and is handled separately by the full AST lowering. -/
noncomputable def riscvShv : Flapjack.Shift →
    (BitVec 5 × BitVec 5 × BitVec 5 → RiscV.L3.Shift)
  | .lsl => RiscV.L3.Shift.SLL
  | .lsr => RiscV.L3.Shift.SRL
  | .asr => RiscV.L3.Shift.SRA
  | .ror => Flapjack.holArb _

theorem riscvShvClauses :
    riscvShv .lsl = RiscV.L3.Shift.SLL ∧
    riscvShv .lsr = RiscV.L3.Shift.SRL ∧
    riscvShv .asr = RiscV.L3.Shift.SRA := by exact ⟨rfl,rfl,rfl⟩

def riscvMemop : HolMemop →
    Sum (BitVec 5 × BitVec 5 × BitVec 12 → Load)
        (BitVec 5 × BitVec 5 × BitVec 12 → Store)
  | .load => .inl Load.LD
  | .load32 => .inl Load.LWU
  | .load16 => .inl Load.LHU
  | .load8 => .inl Load.LBU
  | .store => .inr Store.SD
  | .store32 => .inr Store.SW
  | .store16 => .inr Store.SH
  | .store8 => .inr Store.SB

def riscvConst32 (r : BitVec 5) (i : BitVec 32) : List instruction :=
  if i.getLsbD 11 then
    [.ArithI (.LUI (r, ~~~(holWordExtract 20 31 12 i))),
     .ArithI (.XORI (r,r,holWordExtract 12 11 0 i))]
  else
    [.ArithI (.LUI (r,holWordExtract 20 31 12 i)),
     .ArithI (.ADDI (r,r,holWordExtract 12 11 0 i))]

/-- Pure infrastructure spelling the original signed word range comparison.
It has no separately declared HOL original. -/
def inSignedRange (lo hi a : BitVec 64) : Bool := lo.sle a && a.sle hi

/-- Full native source lowering. Splitting finite operator cases preserves
all original inputs and avoids running the undefined partial-table cases.
Register n2w truncation, signed range tests, sign extension and all instruction
sequences follow the source. No validity or target-evaluation premise. -/
def riscvAst : HolAsm 64 → List instruction
  | .inst .skip => riscvEncodeFail
  | .inst (.const r i) =>
    let rd : BitVec 5 := BitVec.ofNat 5 r
    let imm12 := holWordExtract 12 11 0 i
    if i == imm12.signExtend 64 then [.ArithI (.ORI (rd,0,imm12))]
    else if (holWordExtract 32 63 32 i == 0 && !i.getLsbD 31) ||
            (holWordExtract 32 63 32 i == -1 && i.getLsbD 31) then
      riscvConst32 rd (holWordExtract 32 31 0 i)
    else if i.getLsbD 31 then
      riscvConst32 31 (holWordExtract 32 31 0 i) ++
      riscvConst32 rd (~~~(holWordExtract 32 63 32 i)) ++
      [.Shift (.SLLI (rd,rd,32)),.ArithR (.XOR (rd,rd,31))]
    else
      riscvConst32 31 (holWordExtract 32 31 0 i) ++
      riscvConst32 rd (holWordExtract 32 63 32 i) ++
      [.Shift (.SLLI (rd,rd,32)),.ArithR (.OR (rd,rd,31))]
  | .inst (.arith (.binop bop r1 r2 (.reg r3))) =>
    [.ArithR (riscvBopR bop (BitVec.ofNat 5 r1,BitVec.ofNat 5 r2,BitVec.ofNat 5 r3))]
  | .inst (.arith (.binop bop r1 r2 (.imm i))) =>
    let rd := BitVec.ofNat 5 r1
    let rs := BitVec.ofNat 5 r2
    let imm := i.setWidth 12
    match bop with
    | .sub => [.ArithI (.ADDI (rd,rs,-imm))]
    | .add => [.ArithI (.ADDI (rd,rs,imm))]
    | .and => [.ArithI (.ANDI (rd,rs,imm))]
    | .or => [.ArithI (.ORI (rd,rs,imm))]
    | .xor => [.ArithI (.XORI (rd,rs,imm))]
  | .inst (.arith (.shift sh r1 r2 (.imm i))) =>
    let rd := BitVec.ofNat 5 r1
    let rs := BitVec.ofNat 5 r2
    let n := i.toNat
    match sh with
    | .ror => [.Shift (.SRLI (31,rs,BitVec.ofNat 6 n)),
               .Shift (.SLLI (rd,rs,BitVec.ofNat 6 (64-n))),.ArithR (.OR (rd,rd,31))]
    | .lsl => [.Shift (.SLLI (rd,rs,BitVec.ofNat 6 n))]
    | .lsr => [.Shift (.SRLI (rd,rs,BitVec.ofNat 6 n))]
    | .asr => [.Shift (.SRAI (rd,rs,BitVec.ofNat 6 n))]
  | .inst (.arith (.shift sh r1 r2 (.reg r))) =>
    let rd := BitVec.ofNat 5 r1
    let rs := BitVec.ofNat 5 r2
    let rr := BitVec.ofNat 5 r
    match sh with
    | .ror => [.ArithI (.ORI (31,0,64)),.ArithR (.SUB (31,31,rr)),
               .Shift (.SLL (31,rs,31)),.Shift (.SRL (rd,rs,rr)),.ArithR (.OR (rd,rd,31))]
    | .lsl => [.Shift (.SLL (rd,rs,rr))]
    | .lsr => [.Shift (.SRL (rd,rs,rr))]
    | .asr => [.Shift (.SRA (rd,rs,rr))]
  | .inst (.arith (.div r1 r2 r3)) =>
    [.MulDiv (.DIV (BitVec.ofNat 5 r1,BitVec.ofNat 5 r2,BitVec.ofNat 5 r3))]
  | .inst (.arith (.longMul r1 r2 r3 r4)) =>
    [.MulDiv (.MULHU (BitVec.ofNat 5 r1,BitVec.ofNat 5 r3,BitVec.ofNat 5 r4)),
     .MulDiv (.MUL (BitVec.ofNat 5 r2,BitVec.ofNat 5 r3,BitVec.ofNat 5 r4))]
  | .inst (.arith (.longDiv _ _ _ _ _)) => riscvEncodeFail
  | .inst (.arith (.addCarry r1 r2 r3 r4)) =>
    let a := BitVec.ofNat 5 r1; let b := BitVec.ofNat 5 r2
    let c := BitVec.ofNat 5 r3; let d := BitVec.ofNat 5 r4
    [.ArithR (.SLTU (31,0,d)),.ArithR (.ADD (a,b,c)),.ArithR (.SLTU (d,a,c)),
     .ArithR (.ADD (a,a,31)),.ArithR (.SLTU (31,a,31)),.ArithR (.OR (d,d,31))]
  | .inst (.arith (.addOverflow r1 r2 r3 r4)) =>
    let a := BitVec.ofNat 5 r1; let b := BitVec.ofNat 5 r2
    let c := BitVec.ofNat 5 r3; let d := BitVec.ofNat 5 r4
    [.ArithR (.XOR (31,b,c)),.ArithI (.XORI (31,31,-1)),.ArithR (.ADD (a,b,c)),
     .ArithR (.XOR (d,c,a)),.ArithR (.AND (d,31,d)),.Shift (.SRLI (d,d,63))]
  | .inst (.arith (.subOverflow r1 r2 r3 r4)) =>
    let a := BitVec.ofNat 5 r1; let b := BitVec.ofNat 5 r2
    let c := BitVec.ofNat 5 r3; let d := BitVec.ofNat 5 r4
    [.ArithR (.XOR (31,b,c)),.ArithR (.SUB (a,b,c)),.ArithR (.XOR (d,c,a)),
     .ArithI (.XORI (d,d,-1)),.ArithR (.AND (d,31,d)),.Shift (.SRLI (d,d,63))]
  | .inst (.mem mop r1 (.addr r2 a)) =>
    match riscvMemop mop with
    | .inl f => [.Load (f (BitVec.ofNat 5 r1,BitVec.ofNat 5 r2,a.setWidth 12))]
    | .inr f => [.Store (f (BitVec.ofNat 5 r2,BitVec.ofNat 5 r1,a.setWidth 12))]
  | .jump a =>
    if inSignedRange (-1048576) 1048575 a then [.Branch (.JAL (0,(a.sshiftRight 1).setWidth 20))]
    else let imm12 := holWordExtract 12 11 0 a
         [.ArithI (.AUIPC (31,holWordExtract 20 31 12 (a-imm12.signExtend 64))),
          .Branch (.JALR (0,31,imm12))]
  | .jumpCmp c r1 right a =>
    let r := BitVec.ofNat 5 r1
    match right with
    | .reg r2 =>
      let s := BitVec.ofNat 5 r2
      if inSignedRange (-4092) 4095 a then
        let off : BitVec 12 := (a.sshiftRight 1).setWidth 12
        match c with
        | .equal => [.Branch (.BEQ (r,s,off))]
        | .less => [.Branch (.BLT (r,s,off))]
        | .lower => [.Branch (.BLTU (r,s,off))]
        | .test => [.ArithR (.AND (31,r,s)),.Branch (.BEQ (31,0,off-2))]
        | .notEqual => [.Branch (.BNE (r,s,off))]
        | .notLess => [.Branch (.BGE (r,s,off))]
        | .notLower => [.Branch (.BGEU (r,s,off))]
        | .notTest => [.ArithR (.AND (31,r,s)),.Branch (.BNE (31,0,off-2))]
      else
        let off : BitVec 20 := (a.sshiftRight 1).setWidth 20 - 2
        match c with
        | .equal => [.Branch (.BNE (r,s,4)),.Branch (.JAL (0,off))]
        | .less => [.Branch (.BGE (r,s,4)),.Branch (.JAL (0,off))]
        | .lower => [.Branch (.BGEU (r,s,4)),.Branch (.JAL (0,off))]
        | .test => [.ArithR (.AND (31,r,s)),.Branch (.BNE (31,0,4)),.Branch (.JAL (0,off-2))]
        | .notEqual => [.Branch (.BEQ (r,s,4)),.Branch (.JAL (0,off))]
        | .notLess => [.Branch (.BLT (r,s,4)),.Branch (.JAL (0,off))]
        | .notLower => [.Branch (.BLTU (r,s,4)),.Branch (.JAL (0,off))]
        | .notTest => [.ArithR (.AND (31,r,s)),.Branch (.BEQ (31,0,4)),.Branch (.JAL (0,off-2))]
    | .imm i =>
      let imm := i.setWidth 12
      if inSignedRange (-4092) 4095 a then
        let off : BitVec 12 := (a.sshiftRight 1).setWidth 12 - 2
        match c with
        | .equal => [.ArithI (.ORI (31,0,imm)),.Branch (.BEQ (r,31,off))]
        | .less => [.ArithI (.ORI (31,0,imm)),.Branch (.BLT (r,31,off))]
        | .lower => [.ArithI (.ORI (31,0,imm)),.Branch (.BLTU (r,31,off))]
        | .test => [.ArithI (.ANDI (31,r,imm)),.Branch (.BEQ (31,0,off))]
        | .notEqual => [.ArithI (.ORI (31,0,imm)),.Branch (.BNE (r,31,off))]
        | .notLess => [.ArithI (.ORI (31,0,imm)),.Branch (.BGE (r,31,off))]
        | .notLower => [.ArithI (.ORI (31,0,imm)),.Branch (.BGEU (r,31,off))]
        | .notTest => [.ArithI (.ANDI (31,r,imm)),.Branch (.BNE (31,0,off))]
      else
        let off : BitVec 20 := (a.sshiftRight 1).setWidth 20 - 4
        match c with
        | .equal => [.ArithI (.ORI (31,0,imm)),.Branch (.BNE (r,31,4)),.Branch (.JAL (0,off))]
        | .less => [.ArithI (.ORI (31,0,imm)),.Branch (.BGE (r,31,4)),.Branch (.JAL (0,off))]
        | .lower => [.ArithI (.ORI (31,0,imm)),.Branch (.BGEU (r,31,4)),.Branch (.JAL (0,off))]
        | .test => [.ArithI (.ANDI (31,r,imm)),.Branch (.BNE (31,0,4)),.Branch (.JAL (0,off))]
        | .notEqual => [.ArithI (.ORI (31,0,imm)),.Branch (.BEQ (r,31,4)),.Branch (.JAL (0,off))]
        | .notLess => [.ArithI (.ORI (31,0,imm)),.Branch (.BLT (r,31,4)),.Branch (.JAL (0,off))]
        | .notLower => [.ArithI (.ORI (31,0,imm)),.Branch (.BLTU (r,31,4)),.Branch (.JAL (0,off))]
        | .notTest => [.ArithI (.ANDI (31,r,imm)),.Branch (.BEQ (31,0,4)),.Branch (.JAL (0,off))]
  | .call a =>
    if inSignedRange (-1048576) 1048575 a then [.Branch (.JAL (1,(a.sshiftRight 1).setWidth 20))]
    else let imm12 := holWordExtract 12 11 0 a
         [.ArithI (.AUIPC (1,holWordExtract 20 31 12 (a-imm12.signExtend 64))),
          .Branch (.JALR (1,1,imm12))]
  | .jumpReg r => [.Branch (.JALR (0,BitVec.ofNat 5 r,0))]
  | .loc r i =>
    let rd := BitVec.ofNat 5 r
    let imm12 := holWordExtract 12 11 0 i
    [.ArithI (.AUIPC (rd,holWordExtract 20 31 12 (i-imm12.signExtend 64))),
     .ArithI (.ADDI (rd,rd,imm12))]

def riscvEnc (a : HolAsm 64) : List (BitVec 8) := (riscvAst a).flatMap riscvEncode
end Flapjack.Compiler.Encoders.RiscV.Target
