import Flapjack.RiscV.Encoding
import Flapjack.Compiler.Encoders.RiscV.Target

/-! Complete conversion of the executed RV64 instruction carrier into the native
L3 carrier. This is Flapjack infrastructure, not a HOL datatype port: the
production carrier has fewer constructors than the full native instruction.
The conversion is total over every production constructor. Universal encoding
agreement and actual route replacement remain separate prerequisites. -/
namespace Flapjack.RiscV

/-- Register codec preserving all 32 production registers. No HOL original
uses this Fin-based carrier, so this infrastructure is deliberately untagged. -/
def nativeRegister (r : Fin 32) : BitVec 5 := BitVec.ofNat 5 r.val

theorem nativeRegister_toNat (r : Fin 32) : (nativeRegister r).toNat = r.val := by
  simp [nativeRegister]

/-- Full production RV64 instruction conversion, with the exact encoded operand
widths. Branch/JAL fields omit bit0 because both encoders encode halfword offsets.
The production divU encoding intentionally selects native DIV, matching the
existing CakeML convention; this does not claim equality of execution semantics.
No constructor fails or falls back to a fabricated native opcode. -/
def nativeInstruction : Instruction 64 → L3.instruction
  | .add d a b => .ArithR (.ADD (nativeRegister d, nativeRegister a, nativeRegister b))
  | .sub d a b => .ArithR (.SUB (nativeRegister d, nativeRegister a, nativeRegister b))
  | .addW d a b => .ArithR (.ADDW (nativeRegister d, nativeRegister a, nativeRegister b))
  | .subW d a b => .ArithR (.SUBW (nativeRegister d, nativeRegister a, nativeRegister b))
  | .and d a b => .ArithR (.AND (nativeRegister d, nativeRegister a, nativeRegister b))
  | .or d a b => .ArithR (.OR (nativeRegister d, nativeRegister a, nativeRegister b))
  | .xor d a b => .ArithR (.XOR (nativeRegister d, nativeRegister a, nativeRegister b))
  | .addi d a i => .ArithI (.ADDI (nativeRegister d, nativeRegister a, i.setWidth 12))
  | .addiW d a i => .ArithI (.ADDIW (nativeRegister d, nativeRegister a, i.setWidth 12))
  | .andi d a i => .ArithI (.ANDI (nativeRegister d, nativeRegister a, i.setWidth 12))
  | .ori d a i => .ArithI (.ORI (nativeRegister d, nativeRegister a, i.setWidth 12))
  | .xori d a i => .ArithI (.XORI (nativeRegister d, nativeRegister a, i.setWidth 12))
  | .mul d a b => .MulDiv (.MUL (nativeRegister d, nativeRegister a, nativeRegister b))
  | .mulW d a b => .MulDiv (.MULW (nativeRegister d, nativeRegister a, nativeRegister b))
  | .mulHU d a b => .MulDiv (.MULHU (nativeRegister d, nativeRegister a, nativeRegister b))
  | .sll d a b => .Shift (.SLL (nativeRegister d, nativeRegister a, nativeRegister b))
  | .srl d a b => .Shift (.SRL (nativeRegister d, nativeRegister a, nativeRegister b))
  | .sra d a b => .Shift (.SRA (nativeRegister d, nativeRegister a, nativeRegister b))
  | .sllW d a b => .Shift (.SLLW (nativeRegister d, nativeRegister a, nativeRegister b))
  | .srlW d a b => .Shift (.SRLW (nativeRegister d, nativeRegister a, nativeRegister b))
  | .sraW d a b => .Shift (.SRAW (nativeRegister d, nativeRegister a, nativeRegister b))
  | .slli d a i => .Shift (.SLLI (nativeRegister d, nativeRegister a, i.setWidth 6))
  | .srli d a i => .Shift (.SRLI (nativeRegister d, nativeRegister a, i.setWidth 6))
  | .srai d a i => .Shift (.SRAI (nativeRegister d, nativeRegister a, i.setWidth 6))
  | .slliW d a i => .Shift (.SLLIW (nativeRegister d, nativeRegister a, i.setWidth 5))
  | .srliW d a i => .Shift (.SRLIW (nativeRegister d, nativeRegister a, i.setWidth 5))
  | .sraiW d a i => .Shift (.SRAIW (nativeRegister d, nativeRegister a, i.setWidth 5))
  | .slt d a b => .ArithR (.SLT (nativeRegister d, nativeRegister a, nativeRegister b))
  | .slti d a i => .ArithI (.SLTI (nativeRegister d, nativeRegister a, i.setWidth 12))
  | .sltu d a b => .ArithR (.SLTU (nativeRegister d, nativeRegister a, nativeRegister b))
  | .sltiu d a i => .ArithI (.SLTIU (nativeRegister d, nativeRegister a, i.setWidth 12))
  | .lui d i => .ArithI (.LUI (nativeRegister d, i.setWidth 20))
  | .auipc d i => .ArithI (.AUIPC (nativeRegister d, i.setWidth 20))
  | .divU d a b => .MulDiv (.DIV (nativeRegister d, nativeRegister a, nativeRegister b))
  | .remU d a b => .MulDiv (.REMU (nativeRegister d, nativeRegister a, nativeRegister b))
  | .branchEq a b i => .Branch (.BEQ (nativeRegister a, nativeRegister b, (i >>> 1).setWidth 12))
  | .branchNe a b i => .Branch (.BNE (nativeRegister a, nativeRegister b, (i >>> 1).setWidth 12))
  | .branchLt a b i => .Branch (.BLT (nativeRegister a, nativeRegister b, (i >>> 1).setWidth 12))
  | .branchGe a b i => .Branch (.BGE (nativeRegister a, nativeRegister b, (i >>> 1).setWidth 12))
  | .branchLtU a b i => .Branch (.BLTU (nativeRegister a, nativeRegister b, (i >>> 1).setWidth 12))
  | .branchGeU a b i => .Branch (.BGEU (nativeRegister a, nativeRegister b, (i >>> 1).setWidth 12))
  | .jal d i => .Branch (.JAL (nativeRegister d, (i >>> 1).setWidth 20))
  | .jalr d a i => .Branch (.JALR (nativeRegister d, nativeRegister a, i.setWidth 12))
  | .ecall  => .System .ECALL
  | .loadByte d a => .Load (.LBU (nativeRegister d, nativeRegister a, 0))
  | .loadByteSigned d a => .Load (.LB (nativeRegister d, nativeRegister a, 0))
  | .storeByte d a => .Store (.SB (nativeRegister a, nativeRegister d, 0))
  | .loadHalf d a => .Load (.LHU (nativeRegister d, nativeRegister a, 0))
  | .loadHalfSigned d a => .Load (.LH (nativeRegister d, nativeRegister a, 0))
  | .storeHalf d a => .Store (.SH (nativeRegister a, nativeRegister d, 0))
  | .load32 d a => .Load (.LWU (nativeRegister d, nativeRegister a, 0))
  | .store32 d a => .Store (.SW (nativeRegister a, nativeRegister d, 0))
  | .loadWord d a => .Load (.LD (nativeRegister d, nativeRegister a, 0))
  | .storeWord d a => .Store (.SD (nativeRegister a, nativeRegister d, 0))
  | .loadWordOffset d a i => .Load (.LD (nativeRegister d, nativeRegister a, i.setWidth 12))
  | .storeWordOffset d a i => .Store (.SD (nativeRegister a, nativeRegister d, i.setWidth 12))
  | .loadByteOffset d a i => .Load (.LBU (nativeRegister d, nativeRegister a, i.setWidth 12))
  | .storeByteOffset d a i => .Store (.SB (nativeRegister a, nativeRegister d, i.setWidth 12))
  | .loadHalfOffset d a i => .Load (.LHU (nativeRegister d, nativeRegister a, i.setWidth 12))
  | .storeHalfOffset d a i => .Store (.SH (nativeRegister a, nativeRegister d, i.setWidth 12))
  | .load32Offset d a i => .Load (.LWU (nativeRegister d, nativeRegister a, i.setWidth 12))
  | .store32Offset d a i => .Store (.SW (nativeRegister a, nativeRegister d, i.setWidth 12))

/-- Universal byte-order agreement for the full native instruction carrier.
This follows the existing Flapjack byte-slice theorem; it makes no claim about
production word encoding or cross-language equivalence. No HOL original names
this relation between the two Lean byte emitters, so it stays untagged. -/
theorem nativeEncodeBytes (i : L3.instruction) :
    encodeWordBytes (L3.Encode i) =
      Compiler.Encoders.RiscV.Target.riscvEncode i := by
  rw [encodeWordBytes_eq_extracts]
  simp only [Compiler.Encoders.RiscV.Target.riscvEncode, List.cons.injEq, and_true]
  repeat' apply And.intro
  all_goals
    apply BitVec.eq_of_toNat_eq
    simp [L3.holWordExtract, BitVec.extractLsb']

end Flapjack.RiscV
