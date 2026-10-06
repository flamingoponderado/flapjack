import ZirenDet.Isa

/-!
# MIPS32 instruction encoder for Ziren's ISA model

`ZirenDet.Isa` (Ziren's executable MIPS32r2 model, `crates/fv/lean4/ZirenDet/Isa.lean`) has a
decoder but no encoder. `encodeInsn` writes the standard MIPS32 instruction formats for the
instructions the MIPS32 backend emits, and the `decode_encode_*` lemmas prove that Ziren's
`decode` reads each of them back. Instructions the backend never emits encode as the
canonical `nop` word `0`; no lemma is stated for them.

Flapjack infrastructure: CakeML has no MIPS32 target (its `mips_target` is MIPS64,
big-endian, over the L3 MIPS model), so nothing here carries a `@[hol]` tag.
-/

namespace Flapjack.Mips32
open ZirenDet.Isa

/-- R-type word: `SPECIAL rs rt rd sa funct`. -/
def rType (rs rt rd : Fin 32) (sa funct : Nat) : W :=
  BitVec.ofNat 32 (rs.val * 2 ^ 21 + rt.val * 2 ^ 16 + rd.val * 2 ^ 11 + sa * 2 ^ 6 + funct)

/-- I-type word: `op rs rt imm`. Also used for `REGIMM` with the selector in `rt`. -/
def iType (op : Nat) (rs rt : Fin 32) (imm : BitVec 16) : W :=
  BitVec.ofNat 32 (op * 2 ^ 26 + rs.val * 2 ^ 21 + rt.val * 2 ^ 16 + imm.toNat)

/-- Little-endian bytes of an instruction word (Ziren's guest is `mipsel`). -/
def wordBytes (w : W) : List (BitVec 8) :=
  [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-- The instruction word of every instruction the backend emits. -/
def encodeInsn : Insn → W
  | .addu rd rs rt => rType rs rt rd 0 0x21
  | .subu rd rs rt => rType rs rt rd 0 0x23
  | .and rd rs rt => rType rs rt rd 0 0x24
  | .or rd rs rt => rType rs rt rd 0 0x25
  | .xor rd rs rt => rType rs rt rd 0 0x26
  | .nor rd rs rt => rType rs rt rd 0 0x27
  | .slt rd rs rt => rType rs rt rd 0 0x2a
  | .sltu rd rs rt => rType rs rt rd 0 0x2b
  | .sll rd rt sa => rType 0 rt rd sa.toNat 0x00
  | .srl rd rt sa => rType 0 rt rd sa.toNat 0x02
  | .sra rd rt sa => rType 0 rt rd sa.toNat 0x03
  | .rotr rd rt sa => rType 1 rt rd sa.toNat 0x02
  | .sllv rd rt rs => rType rs rt rd 0 0x04
  | .srlv rd rt rs => rType rs rt rd 0 0x06
  | .srav rd rt rs => rType rs rt rd 0 0x07
  | .rotrv rd rt rs => rType rs rt rd 1 0x06
  | .jr rs => rType rs 0 0 0 0x08
  | .jalr rd rs => rType rs 0 rd 0 0x09
  | .mfhi rd => rType 0 0 rd 0 0x10
  | .mflo rd => rType 0 0 rd 0 0x12
  | .multu rs rt => rType rs rt 0 0 0x19
  | .div rs rt => rType rs rt 0 0 0x1a
  | .bal off => iType 1 0 0x11 off
  | .beq rs rt off => iType 4 rs rt off
  | .bne rs rt off => iType 5 rs rt off
  | .addiu rt rs imm => iType 9 rs rt imm
  | .slti rt rs imm => iType 0xa rs rt imm
  | .sltiu rt rs imm => iType 0xb rs rt imm
  | .andi rt rs imm => iType 0xc rs rt imm
  | .ori rt rs imm => iType 0xd rs rt imm
  | .xori rt rs imm => iType 0xe rs rt imm
  | .lui rt imm => iType 0xf 0 rt imm
  | .lbu rt base off => iType 0x24 base rt off
  | .lhu rt base off => iType 0x25 base rt off
  | .lw rt base off => iType 0x23 base rt off
  | .sb rt base off => iType 0x28 base rt off
  | .sh rt base off => iType 0x29 base rt off
  | .sw rt base off => iType 0x2b base rt off
  | _ => 0

/-- The canonical MIPS `nop` (`sll $0, $0, 0`), which Ziren decodes as a shift into `$zero`. -/
def nop : Insn := .sll 0 0 0

theorem encodeInsn_nop : encodeInsn nop = 0 := by decide

/-! ## Ziren's `decode` reads every emitted word back -/

theorem field_eq (w : W) (lo len : Nat) : field w lo len = w.toNat / 2 ^ lo % 2 ^ len := by
  simp [field, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem rType_toNat (rs rt rd : Fin 32) (sa funct : Nat) (hsa : sa < 32) (hf : funct < 64) :
    (rType rs rt rd sa funct).toNat =
      rs.val * 2 ^ 21 + rt.val * 2 ^ 16 + rd.val * 2 ^ 11 + sa * 2 ^ 6 + funct := by
  have := rs.isLt; have := rt.isLt; have := rd.isLt
  simp only [rType, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt; omega

theorem iType_toNat (op : Nat) (rs rt : Fin 32) (imm : BitVec 16) (hop : op < 64) :
    (iType op rs rt imm).toNat = op * 2 ^ 26 + rs.val * 2 ^ 21 + rt.val * 2 ^ 16 + imm.toNat := by
  have := rs.isLt; have := rt.isLt; have := imm.isLt
  simp only [iType, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt; omega

/-- The fields Ziren's decoder reads from a word with R-type contents. -/
theorem rFields {w : W} {rs rt rd : Fin 32} {sa funct : Nat}
    (h : w.toNat = rs.val * 2 ^ 21 + rt.val * 2 ^ 16 + rd.val * 2 ^ 11 + sa * 2 ^ 6 + funct)
    (hsa : sa < 32) (hf : funct < 64) :
    field w 26 6 = 0 ∧ field w 0 6 = funct ∧ field w 21 5 = rs.val ∧ field w 6 5 = sa ∧
      reg w 21 = rs ∧ reg w 16 = rt ∧ reg w 11 = rd ∧
      (w.extractLsb' 6 5 : BitVec 5) = BitVec.ofNat 5 sa := by
  have := rs.isLt; have := rt.isLt; have := rd.isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [field_eq, h]; omega)
    | (apply Fin.ext; show field w _ 5 = _; rw [field_eq, h]; omega)
    | (apply BitVec.eq_of_toNat_eq
       rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, h]; omega)

/-- The fields Ziren's decoder reads from a word with I-type contents. -/
theorem iFields {w : W} {op : Nat} {rs rt : Fin 32} {imm : BitVec 16}
    (h : w.toNat = op * 2 ^ 26 + rs.val * 2 ^ 21 + rt.val * 2 ^ 16 + imm.toNat) (_hop : op < 64) :
    field w 26 6 = op ∧ field w 16 5 = rt.val ∧ reg w 21 = rs ∧ reg w 16 = rt ∧
      (w.extractLsb' 0 16 : BitVec 16) = imm := by
  have := rs.isLt; have := rt.isLt; have := imm.isLt
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [field_eq, h]; omega)
    | (apply Fin.ext; show field w _ 5 = _; rw [field_eq, h]; omega)
    | (apply BitVec.eq_of_toNat_eq
       rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, h]; omega)

macro "decode_rtype" rs:term:max rt:term:max rd:term:max sa:term:max funct:term:max : tactic => `(tactic| (
  have hw := rType_toNat $rs $rt $rd $sa $funct (by omega) (by omega)
  simp only [encodeInsn]
  generalize rType $rs $rt $rd $sa $funct = w at hw
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := rFields hw (by omega) (by omega)
  simp only [decode, h1, h2, h3, h4, h5, h6, h7, h8]
  try simp
  try rfl))

macro "decode_itype" op:term:max rs:term:max rt:term:max imm:term:max : tactic => `(tactic| (
  have hw := iType_toNat $op $rs $rt $imm (by omega)
  simp only [encodeInsn]
  generalize iType $op $rs $rt $imm = w at hw
  obtain ⟨h1, h2, h3, h4, h5⟩ := iFields hw (by omega)
  simp only [decode, h1, h2, h3, h4, h5]
  try simp
  try rfl))

@[simp] theorem decode_addu (rd rs rt : Fin 32) :
    decode (encodeInsn (.addu rd rs rt)) = some (.addu rd rs rt) := by
  decode_rtype rs rt rd (0) 0x21
@[simp] theorem decode_subu (rd rs rt : Fin 32) :
    decode (encodeInsn (.subu rd rs rt)) = some (.subu rd rs rt) := by
  decode_rtype rs rt rd (0) 0x23
@[simp] theorem decode_and (rd rs rt : Fin 32) :
    decode (encodeInsn (.and rd rs rt)) = some (.and rd rs rt) := by
  decode_rtype rs rt rd (0) 0x24
@[simp] theorem decode_or (rd rs rt : Fin 32) :
    decode (encodeInsn (.or rd rs rt)) = some (.or rd rs rt) := by
  decode_rtype rs rt rd (0) 0x25
@[simp] theorem decode_xor (rd rs rt : Fin 32) :
    decode (encodeInsn (.xor rd rs rt)) = some (.xor rd rs rt) := by
  decode_rtype rs rt rd (0) 0x26
@[simp] theorem decode_nor (rd rs rt : Fin 32) :
    decode (encodeInsn (.nor rd rs rt)) = some (.nor rd rs rt) := by
  decode_rtype rs rt rd (0) 0x27
@[simp] theorem decode_slt (rd rs rt : Fin 32) :
    decode (encodeInsn (.slt rd rs rt)) = some (.slt rd rs rt) := by
  decode_rtype rs rt rd (0) 0x2a
@[simp] theorem decode_sltu (rd rs rt : Fin 32) :
    decode (encodeInsn (.sltu rd rs rt)) = some (.sltu rd rs rt) := by
  decode_rtype rs rt rd (0) 0x2b
@[simp] theorem decode_sllv (rd rt rs : Fin 32) :
    decode (encodeInsn (.sllv rd rt rs)) = some (.sllv rd rt rs) := by
  decode_rtype rs rt rd (0) 0x04
@[simp] theorem decode_srlv (rd rt rs : Fin 32) :
    decode (encodeInsn (.srlv rd rt rs)) = some (.srlv rd rt rs) := by
  decode_rtype rs rt rd (0) 0x06
@[simp] theorem decode_srav (rd rt rs : Fin 32) :
    decode (encodeInsn (.srav rd rt rs)) = some (.srav rd rt rs) := by
  decode_rtype rs rt rd (0) 0x07
@[simp] theorem decode_rotrv (rd rt rs : Fin 32) :
    decode (encodeInsn (.rotrv rd rt rs)) = some (.rotrv rd rt rs) := by
  decode_rtype rs rt rd (1) 0x06
@[simp] theorem decode_jr (rs : Fin 32) :
    decode (encodeInsn (.jr rs)) = some (.jr rs) := by
  decode_rtype rs 0 0 (0) 0x08
@[simp] theorem decode_jalr (rd rs : Fin 32) :
    decode (encodeInsn (.jalr rd rs)) = some (.jalr rd rs) := by
  decode_rtype rs 0 rd (0) 0x09
@[simp] theorem decode_mfhi (rd : Fin 32) :
    decode (encodeInsn (.mfhi rd)) = some (.mfhi rd) := by
  decode_rtype 0 0 rd (0) 0x10
@[simp] theorem decode_mflo (rd : Fin 32) :
    decode (encodeInsn (.mflo rd)) = some (.mflo rd) := by
  decode_rtype 0 0 rd (0) 0x12
@[simp] theorem decode_multu (rs rt : Fin 32) :
    decode (encodeInsn (.multu rs rt)) = some (.multu rs rt) := by
  decode_rtype rs rt 0 (0) 0x19
@[simp] theorem decode_div (rs rt : Fin 32) :
    decode (encodeInsn (.div rs rt)) = some (.div rs rt) := by
  decode_rtype rs rt 0 (0) 0x1a
@[simp] theorem decode_sll (rd rt : Fin 32) (sa : BitVec 5) :
    decode (encodeInsn (.sll rd rt sa)) = some (.sll rd rt sa) := by
  have := sa.isLt; decode_rtype 0 rt rd (sa.toNat) 0x00
@[simp] theorem decode_srl (rd rt : Fin 32) (sa : BitVec 5) :
    decode (encodeInsn (.srl rd rt sa)) = some (.srl rd rt sa) := by
  have := sa.isLt; decode_rtype 0 rt rd (sa.toNat) 0x02
@[simp] theorem decode_sra (rd rt : Fin 32) (sa : BitVec 5) :
    decode (encodeInsn (.sra rd rt sa)) = some (.sra rd rt sa) := by
  have := sa.isLt; decode_rtype 0 rt rd (sa.toNat) 0x03
@[simp] theorem decode_rotr (rd rt : Fin 32) (sa : BitVec 5) :
    decode (encodeInsn (.rotr rd rt sa)) = some (.rotr rd rt sa) := by
  have := sa.isLt; decode_rtype 1 rt rd (sa.toNat) 0x02
@[simp] theorem decode_bal (off : BitVec 16) :
    decode (encodeInsn (.bal off)) = some (.bal off) := by
  decode_itype 1 0 0x11 off
@[simp] theorem decode_beq (rs rt : Fin 32) (off : BitVec 16) :
    decode (encodeInsn (.beq rs rt off)) = some (.beq rs rt off) := by
  decode_itype 4 rs rt off
@[simp] theorem decode_bne (rs rt : Fin 32) (off : BitVec 16) :
    decode (encodeInsn (.bne rs rt off)) = some (.bne rs rt off) := by
  decode_itype 5 rs rt off
@[simp] theorem decode_addiu (rt rs : Fin 32) (imm : BitVec 16) :
    decode (encodeInsn (.addiu rt rs imm)) = some (.addiu rt rs imm) := by
  decode_itype 9 rs rt imm
@[simp] theorem decode_slti (rt rs : Fin 32) (imm : BitVec 16) :
    decode (encodeInsn (.slti rt rs imm)) = some (.slti rt rs imm) := by
  decode_itype 0xa rs rt imm
@[simp] theorem decode_sltiu (rt rs : Fin 32) (imm : BitVec 16) :
    decode (encodeInsn (.sltiu rt rs imm)) = some (.sltiu rt rs imm) := by
  decode_itype 0xb rs rt imm
@[simp] theorem decode_andi (rt rs : Fin 32) (imm : BitVec 16) :
    decode (encodeInsn (.andi rt rs imm)) = some (.andi rt rs imm) := by
  decode_itype 0xc rs rt imm
@[simp] theorem decode_ori (rt rs : Fin 32) (imm : BitVec 16) :
    decode (encodeInsn (.ori rt rs imm)) = some (.ori rt rs imm) := by
  decode_itype 0xd rs rt imm
@[simp] theorem decode_xori (rt rs : Fin 32) (imm : BitVec 16) :
    decode (encodeInsn (.xori rt rs imm)) = some (.xori rt rs imm) := by
  decode_itype 0xe rs rt imm
@[simp] theorem decode_lui (rt : Fin 32) (imm : BitVec 16) :
    decode (encodeInsn (.lui rt imm)) = some (.lui rt imm) := by
  decode_itype 0xf 0 rt imm
@[simp] theorem decode_lbu (rt base : Fin 32) (off : BitVec 16) :
    decode (encodeInsn (.lbu rt base off)) = some (.lbu rt base off) := by
  decode_itype 0x24 base rt off
@[simp] theorem decode_lhu (rt base : Fin 32) (off : BitVec 16) :
    decode (encodeInsn (.lhu rt base off)) = some (.lhu rt base off) := by
  decode_itype 0x25 base rt off
@[simp] theorem decode_lw (rt base : Fin 32) (off : BitVec 16) :
    decode (encodeInsn (.lw rt base off)) = some (.lw rt base off) := by
  decode_itype 0x23 base rt off
@[simp] theorem decode_sb (rt base : Fin 32) (off : BitVec 16) :
    decode (encodeInsn (.sb rt base off)) = some (.sb rt base off) := by
  decode_itype 0x28 base rt off
@[simp] theorem decode_sh (rt base : Fin 32) (off : BitVec 16) :
    decode (encodeInsn (.sh rt base off)) = some (.sh rt base off) := by
  decode_itype 0x29 base rt off
@[simp] theorem decode_sw (rt base : Fin 32) (off : BitVec 16) :
    decode (encodeInsn (.sw rt base off)) = some (.sw rt base off) := by
  decode_itype 0x2b base rt off

end Flapjack.Mips32
