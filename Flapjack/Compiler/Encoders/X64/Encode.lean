module

public import Flapjack.Compiler.Encoders.Asm
public import Flapjack.HolRef

@[expose] public section

/-!
# x86-64 instruction encodings

This module ports the parts of the L3-generated `x64$encode`
(`HOL/examples/l3-machine-code/x64/model/x64Script.sml`) that the CakeML x86-64
target (`cakeml/compiler/encoders/x64/x64_targetScript.sml`) emits, together
with the encoding helpers `e_imm8`, `e_imm16`, `e_imm32`, `e_imm64`,
`e_imm_8_32`, `e_ModRM`, `rex_prefix`, `e_opsize`, `e_opsize_imm`, `e_opc`,
`e_gen_rm_reg`, `e_rm_imm`, `e_rm_imm8` and `e_rax_imm`.

The L3 encoder ranges over the full `x64$instruction` datatype.  Flapjack
models only the instruction forms the backend produces, in a structured
`X64Insn` carrier, so these declarations are not exact carrier-level ports and
are not tagged `@[hol]`.  Byte-for-byte agreement with the original compiler is
established by the parity fixtures instead (see `docs/X64.md`).

The helper functions follow the L3 definitions clause for clause.  Register
numbers are `Nat`s: L3's `Zreg` has sixteen nullary constructors numbered
0 (RAX) through 15 (R15); `num2Zreg n = n MOD 16`.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack

/-- L3 `Zsize = Z16 | Z32 | Z64 | Z8 of bool` (`x64Script.sml:28-31`).
The `bool` payload is `have_rex`: it forces a REX prefix so that byte
registers 4..7 name SPL/BPL/SIL/DIL rather than AH/CH/DH/BH. -/
inductive ZSize where
  | z16
  | z32
  | z64
  | z8 (haveRex : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- L3 `Zbase = ZnoBase | ZregBase of Zreg | ZripBase`
(`x64Script.sml:36-39`). -/
inductive ZBase where
  | noBase
  | regBase (reg : Nat)
  | ripBase
  deriving DecidableEq, Repr, Inhabited

/-- L3 `Zrm = Zm of (word2 × Zreg) option × Zbase × word64 | Zr of Zreg`
(`x64Script.sml:40-44`).  The optional pair is `(scale, index)`; the scale is a
two-bit value. -/
inductive ZRM where
  | zm (index : Option (Nat × Nat)) (base : ZBase) (disp : BitVec 64)
  | zr (reg : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- L3 `Zdest_src = Zr_rm of Zreg × Zrm | Zrm_i of Zrm × word64 |
Zrm_r of Zrm × Zreg` (`x64Script.sml:46-50`). -/
inductive ZDestSrc where
  | zr_rm (reg : Nat) (rm : ZRM)
  | zrm_i (rm : ZRM) (imm : BitVec 64)
  | zrm_r (rm : ZRM) (reg : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- L3 `Zmonop_name = Zdec | Zinc | Znot | Zneg` (`x64Script.sml:55-58`). -/
inductive ZMonopName where
  | zdec
  | zinc
  | znot
  | zneg
  deriving DecidableEq, Repr, Inhabited

/-- L3 `Zbinop_name` (`x64Script.sml:59-65`), in source order, so the numeric
value of constructor `n` is `n` as a four-bit word. -/
inductive ZBinopName where
  | zadd
  | zor
  | zadc
  | zsbb
  | zand
  | zsub
  | zxor
  | zcmp
  | zrol
  | zror
  | zrcl
  | zrcr
  | zshl
  | zshr
  | ztest
  | zsar
  deriving DecidableEq, Repr, Inhabited

/-- The numeric code of `Zbinop_name`, matching L3's constructor numbering. -/
def ZBinopName.code : ZBinopName → Nat
  | .zadd => 0
  | .zor => 1
  | .zadc => 2
  | .zsbb => 3
  | .zand => 4
  | .zsub => 5
  | .zxor => 6
  | .zcmp => 7
  | .zrol => 8
  | .zror => 9
  | .zrcl => 10
  | .zrcr => 11
  | .zshl => 12
  | .zshr => 13
  | .ztest => 14
  | .zsar => 15

/-- L3 `Zcond` (`x64Script.sml:71-77`), in source order. -/
inductive ZCond where
  | zO
  | zNO
  | zB
  | zNB
  | zE
  | zNE
  | zNA
  | zA
  | zS
  | zNS
  | zP
  | zNP
  | zL
  | zNL
  | zNG
  | zG
  | zAlways
  deriving DecidableEq, Repr, Inhabited

/-- The numeric code of `Zcond`. -/
def ZCond.code : ZCond → Nat
  | .zO => 0
  | .zNO => 1
  | .zB => 2
  | .zNB => 3
  | .zE => 4
  | .zNE => 5
  | .zNA => 6
  | .zA => 7
  | .zS => 8
  | .zNS => 9
  | .zP => 10
  | .zNP => 11
  | .zL => 12
  | .zNL => 13
  | .zNG => 14
  | .zG => 15
  | .zAlways => 16

/-- L3 `sse_binop` (`x64Script.sml:84-88`). -/
inductive SSEBinop where
  | sseAdd
  | sseSub
  | sseMul
  | sseDiv
  | sseMax
  | sseMin
  deriving DecidableEq, Repr, Inhabited

/-- L3 `sse_logic` (`x64Script.sml:90-94`). -/
inductive SSELogic where
  | sseAnd
  | sseAndn
  | sseOr
  | sseXor
  deriving DecidableEq, Repr, Inhabited

/-- The SSE instruction forms the x86-64 backend emits, mirroring the L3
`SSE` constructors used by `x64_ast`. -/
inductive X64SSE where
  | comisd (dst src : Nat)
  | movsd (dst src : Nat)
  | pcmpeqq (dst src : Nat)
  | psrlqImm (dst : Nat) (imm : BitVec 8)
  | psllqImm (dst : Nat) (imm : BitVec 8)
  | logicPD (op : SSELogic) (dst src : Nat)
  | sqrtsd (dst src : Nat)
  | binSD (op : SSEBinop) (dst src : Nat)
  | movDQ (toXmm quad : Bool) (xmm : Nat) (rm : ZRM)
  | cvtpd2dq (truncate : Bool) (dst src : Nat)
  | pslldq (dst : Nat) (imm : BitVec 8)
  | psrldq (dst : Nat) (imm : BitVec 8)
  | cvtdq2pd (dst src : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The instruction forms the x86-64 backend emits.  This is a subset of L3's
`instruction` datatype (`x64Script.sml:130-166`); the constructors mirror the
L3 forms produced by `x64_ast`. -/
inductive X64Insn where
  | nop (n : Nat)
  | movRR (sz : ZSize) (dst src : Nat)
  | movRI (sz : ZSize) (dst : Nat) (imm : BitVec 64)
  | movRM (sz : ZSize) (dst base : Nat) (disp : BitVec 64)
  | movMR (sz : ZSize) (src base : Nat) (disp : BitVec 64)
  | movzxRM (sz1 sz2 : ZSize) (dst base : Nat) (disp : BitVec 64)
  | binopRI (op : ZBinopName) (sz : ZSize) (dst : Nat) (imm : BitVec 64)
  | binopRR (op : ZBinopName) (sz : ZSize) (dst src : Nat)
  | monop (op : ZMonopName) (sz : ZSize) (dst : Nat)
  | mul (sz : ZSize) (src : Nat)
  | div (sz : ZSize) (src : Nat)
  | cmc
  | setcc (cond : ZCond) (haveRex : Bool) (dst : Nat)
  | jcc (cond : ZCond) (imm : BitVec 64)
  | jmp (dst : Nat)
  | lea (sz : ZSize) (dst : Nat) (disp : BitVec 64)
  | sse (op : X64SSE)
  deriving DecidableEq, Repr, Inhabited

/-- L3 `num2Zreg`: registers are numbered 0..15. -/
def num2Zreg (n : Nat) : Nat := n % 16

/-- L3 `total_num2Zreg`: out-of-range registers encode as RAX (0). -/
def totalNum2Zreg (n : Nat) : Nat := if n < 16 then num2Zreg n else 0

/-- A byte literal from a natural number (truncating to 8 bits). -/
def byte (n : Nat) : BitVec 8 := BitVec.ofNat 8 n

/-- L3 `rex_prefix`: a four-bit REX value becomes `0x40 + rex`, or no bytes. -/
def rexPrefix (rex : BitVec 4) : List (BitVec 8) :=
  if rex = 0 then [] else [byte (0x40 + rex.toNat)]

/-- Build a four-bit REX value from its four flags (W, R, X, B). -/
def mkRex (w r x b : Bool) : BitVec 4 :=
  BitVec.ofNat 4 ((if w then 8 else 0) + (if r then 4 else 0) +
    (if x then 2 else 0) + (if b then 1 else 0))

/-- L3 `e_imm8`: a sign-extended eight-bit immediate, little-endian. -/
def eImm8 (imm : BitVec 64) : Option (List (BitVec 8)) :=
  if -128 ≤ imm.toInt ∧ imm.toInt ≤ 127 then
    some [byte imm.toNat]
  else none

/-- L3 `e_imm16`: a sign-extended sixteen-bit immediate, little-endian. -/
def eImm16 (imm : BitVec 64) : Option (List (BitVec 8)) :=
  if -32768 ≤ imm.toInt ∧ imm.toInt ≤ 32767 then
    some [byte imm.toNat, byte (imm.toNat / 2 ^ 8)]
  else none

/-- L3 `e_imm32`: a sign-extended thirty-two-bit immediate, little-endian. -/
def eImm32 (imm : BitVec 64) : Option (List (BitVec 8)) :=
  if -(2 ^ 31 : Int) ≤ imm.toInt ∧ imm.toInt ≤ 2 ^ 31 - 1 then
    some [byte imm.toNat, byte (imm.toNat / 2 ^ 8), byte (imm.toNat / 2 ^ 16),
      byte (imm.toNat / 2 ^ 24)]
  else none

/-- L3 `e_imm64`: eight little-endian bytes; always defined. -/
def eImm64 (imm : BitVec 64) : List (BitVec 8) :=
  (List.range 8).map fun k => byte (imm.toNat / 2 ^ (8 * k))

/-- L3 `e_imm_8_32`: one byte, else four bytes, else nothing. -/
def eImm8_32 (imm : BitVec 64) : Option (Nat × List (BitVec 8)) :=
  match eImm8 imm with
  | some l => some (1, l)
  | none =>
      match eImm32 imm with
      | some l => some (4, l)
      | none => none

/-- L3 `e_opsize`: the operand-size prefixes and the `v` bit added to the
opcode (1 for 16/32/64-bit forms, 0 for byte forms). -/
def eOpsize (sz : ZSize) (rex : BitVec 4) : List (BitVec 8) × BitVec 8 :=
  match sz with
  | .z8 haveRex =>
      let p := rexPrefix rex
      (if haveRex && p = [] then [byte 0x40] else p, 0)
  | .z16 => ([byte 0x66] ++ rexPrefix (rex &&& BitVec.ofNat 4 7), 1)
  | .z32 => (rexPrefix (rex &&& BitVec.ofNat 4 7), 1)
  | .z64 => (rexPrefix (rex ||| BitVec.ofNat 4 8), 1)

/-- L3 `e_opsize_imm`: the operand-size prefixes, the `v` bit, and the
immediate bytes.  `normal` is `true` for `e_rm_imm` and `e_rax_imm`, where a
64-bit operation takes a 32-bit sign-extended immediate. -/
def eOpsizeImm (sz : ZSize) (rex : BitVec 4) (imm : BitVec 64) (normal : Bool) :
    Option (List (BitVec 8) × BitVec 8 × List (BitVec 8)) :=
  let (prefixes, v) := eOpsize sz rex
  let sz' := if sz = .z64 && normal then ZSize.z32 else sz
  match sz' with
  | .z8 _ =>
      match eImm8 imm with
      | some l => if v = 0 then some (prefixes, v, l) else none
      | none => none
  | .z16 =>
      match eImm16 imm with
      | some l => if v = 1 then some (prefixes, v, l) else none
      | none => none
  | .z32 =>
      match eImm32 imm with
      | some l => if v = 1 then some (prefixes, v, l) else none
      | none => none
  | .z64 => if v = 1 then some (prefixes, v, eImm64 imm) else none

/-- The L3 `s` field of a `ModRM` byte: 0 = no displacement, 1 = disp8,
4 = disp32. -/
def modField (s : Nat) : Nat := if s = 1 then 1 else if s = 4 then 2 else 0

/-- L3 `e_ModRM`: the REX bits and the ModRM/SIB/displacement bytes. -/
def eModRM (r : BitVec 4) (rm : ZRM) : Option (BitVec 4 × List (BitVec 8)) :=
  let r3 := r.toNat / 8
  let r20 := r.toNat % 8
  match rm with
  | .zr reg =>
      let rm4 := reg % 16
      some (mkRex false (r3 = 1) false (rm4 / 8 = 1),
        [byte (0xC0 ||| (r20 <<< 3) ||| (rm4 % 8))])
  | .zm index base disp =>
      match index, base with
      | none, .ripBase =>
          match eImm32 disp with
          | some l =>
              some (mkRex false (r3 = 1) false false,
                [byte (0x05 ||| (r20 <<< 3))] ++ l)
          | none => none
      | none, .noBase =>
          match eImm32 disp with
          | some l =>
              some (mkRex false (r3 = 1) false false,
                [byte (0x04 ||| (r20 <<< 3)), byte 0x25] ++ l)
          | none => none
      | some (ss, idx), .noBase =>
          match eImm32 disp with
          | some l =>
              let i := idx % 16
              some (mkRex false (r3 = 1) (i / 8 = 1) false,
                [byte (0x04 ||| (r20 <<< 3)),
                  byte (((ss % 4) * 64) ||| (((i % 8) <<< 3) ||| 5))] ++ l)
          | none => none
      | none, .regBase b =>
          let b20 := (b % 16) % 8
          let pick :=
            if disp = 0 && b20 ≠ 5 then some (0, ([] : List (BitVec 8)))
            else eImm8_32 disp
          match pick with
          | some (s, l) =>
              if s = 0 || s = 1 || s = 4 then
                some (mkRex false (r3 = 1) false ((b % 16) / 8 = 1),
                  [byte (((modField s) <<< 6) ||| ((r20 <<< 3) ||| b20))] ++
                    (if b20 = 4 then [byte 0x24] else []) ++ l)
              else none
          | none => none
      | some (ss, idx), .regBase b =>
          let b20 := (b % 16) % 8
          let pick :=
            if disp = 0 && b20 ≠ 5 then some (0, ([] : List (BitVec 8)))
            else eImm8_32 disp
          match pick with
          | some (s, l) =>
              if s = 0 || s = 1 || s = 4 then
                let i := idx % 16
                some (mkRex false (r3 = 1) (i / 8 = 1) ((b % 16) / 8 = 1),
                  [byte (((modField s) <<< 6) ||| ((r20 <<< 3) ||| 4)),
                    byte (((ss % 4) * 64) ||| (((i % 8) <<< 3) ||| b20))] ++ l)
              else none
          | none => none
      | some _, .ripBase => none

/-- L3 `e_opc`: a one-byte opcode followed by an opcode-extension digit and a
`ModRM` operand. -/
def eOpc (opc1 : BitVec 8) (opc2 : BitVec 3) (rm : ZRM) : List (BitVec 8) :=
  match eModRM (BitVec.ofNat 4 opc2.toNat) rm with
  | none => []
  | some (rex, strm) => rexPrefix rex ++ [opc1] ++ strm

/-- L3 `e_gen_rm_reg`: a register/memory operand with a register field. -/
def eGenRmReg (sz : ZSize) (rm : ZRM) (r : BitVec 4) (p : List (BitVec 8))
    (opc : BitVec 8) (mo : Option (BitVec 8)) : List (BitVec 8) :=
  match eModRM r rm with
  | none => []
  | some (rex, strm) =>
      let (prefixes, v) := eOpsize sz rex
      prefixes ++ p ++ [opc ||| mo.getD v] ++ strm

/-- L3 `e_rm_imm`: a register/memory operand with a sign-extended immediate. -/
def eRmImm (sz : ZSize) (rm : ZRM) (imm : BitVec 64) (opc1 : BitVec 4)
    (opc2 : BitVec 8) : List (BitVec 8) :=
  match eModRM opc1 rm with
  | none => []
  | some (rex, strm) =>
      match eOpsizeImm sz rex imm true with
      | none => []
      | some (prefixes, v, l) => prefixes ++ [opc2 ||| v] ++ strm ++ l

/-- L3 `e_rm_imm8`: a register/memory operand with a one-byte immediate. -/
def eRmImm8 (sz : ZSize) (rm : ZRM) (imm : BitVec 64) (opc1 : BitVec 4)
    (opc2 : BitVec 8) : List (BitVec 8) :=
  match eModRM opc1 rm with
  | none => []
  | some (rex, strm) =>
      let (prefixes, v) := eOpsize sz rex
      match eImm8 imm with
      | none => []
      | some l => prefixes ++ [opc2 ||| v] ++ strm ++ l

/-- L3 `e_rax_imm`: the accumulator short forms. -/
def eRaxImm (sz : ZSize) (imm : BitVec 64) (opc : BitVec 8) : List (BitVec 8) :=
  match eOpsizeImm sz 0 imm true with
  | none => []
  | some (prefixes, v, l) => prefixes ++ [opc ||| v] ++ l

/-- L3 `is_rax`: is the operand the accumulator `RAX`? -/
def isRax : ZRM → Bool
  | .zr reg => reg % 16 = 0
  | .zm _ _ _ => false

/-- L3 `not_byte`: is the size anything other than a byte? -/
def notByte : ZSize → Bool
  | .z8 _ => false
  | _ => true

/-- The SSE opcode-extension digit of `sse_binop` (`encode_sse_binop`). -/
def sseBinopCode : SSEBinop → BitVec 3
  | .sseAdd => 0
  | .sseMul => 1
  | .sseSub => 4
  | .sseMin => 5
  | .sseDiv => 6
  | .sseMax => 7

/-- The two-bit `sse_logic` selector (`encode_sse`). -/
def sseLogicCode : SSELogic → BitVec 2
  | .sseAnd => 0
  | .sseAndn => 1
  | .sseOr => 2
  | .sseXor => 3

/-- `xmm_mem_to_rm`: an XMM register becomes a `Zr` operand. -/
def xmmToRM (reg : Nat) : ZRM := .zr reg

/-- L3 `encode_sse` for the emitted SSE forms. -/
def encodeSSE : X64SSE → List (BitVec 8)
  | .comisd dst src =>
      byte 0x66 :: eGenRmReg .z32 (xmmToRM src) (BitVec.ofNat 4 dst)
        [byte 0x0F] (byte 0x2F) none
  | .movsd dst src =>
      byte 0xF2 :: eGenRmReg .z32 (xmmToRM src) (BitVec.ofNat 4 dst)
        [byte 0x0F] (byte 0x10) (some 0)
  | .pcmpeqq dst src =>
      byte 0x66 :: eGenRmReg .z32 (xmmToRM src) (BitVec.ofNat 4 dst)
        [byte 0x0F, byte 0x38] (byte 0x29) (some 0)
  | .psrlqImm dst imm =>
      byte 0x66 :: eGenRmReg .z32 (.zr dst) (BitVec.ofNat 4 2) [byte 0x0F]
        (byte 0x73) (some 0) ++ [imm]
  | .psllqImm dst imm =>
      byte 0x66 :: eGenRmReg .z32 (.zr dst) (BitVec.ofNat 4 6) [byte 0x0F]
        (byte 0x73) (some 0) ++ [imm]
  | .logicPD op dst src =>
      byte 0x66 :: eGenRmReg .z32 (xmmToRM src) (BitVec.ofNat 4 dst)
        [byte 0x0F] (byte 0x54) (some (BitVec.ofNat 8 (sseLogicCode op).toNat))
  | .sqrtsd dst src =>
      byte 0xF2 :: eGenRmReg .z32 (xmmToRM src) (BitVec.ofNat 4 dst)
        [byte 0x0F] (byte 0x51) (some 0)
  | .binSD op dst src =>
      byte 0xF2 :: eGenRmReg .z32 (xmmToRM src) (BitVec.ofNat 4 dst)
        [byte 0x0F] (byte 0x58) (some (BitVec.ofNat 8 (sseBinopCode op).toNat))
  | .movDQ toXmm quad xmm rm =>
      byte 0x66 :: eGenRmReg (if quad then .z64 else .z32) rm
        (BitVec.ofNat 4 xmm) [byte 0x0F]
        (byte (if toXmm then 0x6E else 0x7E)) (some 0)
  | .cvtpd2dq truncate dst src =>
      byte (if truncate then 0x66 else 0xF2) ::
        eGenRmReg .z32 (xmmToRM src) (BitVec.ofNat 4 dst) [byte 0x0F]
          (byte 0xE6) (some 0)
  | .pslldq dst imm =>
      byte 0x66 :: eGenRmReg .z32 (.zr dst) (BitVec.ofNat 4 7) [byte 0x0F]
        (byte 0x73) (some 0) ++ [imm]
  | .psrldq dst imm =>
      byte 0x66 :: eGenRmReg .z32 (.zr dst) (BitVec.ofNat 4 3) [byte 0x0F]
        (byte 0x73) (some 0) ++ [imm]
  | .cvtdq2pd dst src =>
      byte 0xF3 :: eGenRmReg .z32 (xmmToRM src) (BitVec.ofNat 4 dst) [byte 0x0F]
        (byte 0xE6) (some 0)

/-- L3 `encode` for the emitted `instruction` forms, with `x64_encode`'s
conditional-jump override (`x64_targetScript.sml:196-205`) folded in. -/
def encodeInsn : X64Insn → List (BitVec 8)
  | .nop n =>
      match n with
      | 1 => [byte 0x90]
      | 2 => [byte 0x66, byte 0x90]
      | 3 => [byte 0x0F, byte 0x1F, byte 0x00]
      | 4 => [byte 0x0F, byte 0x1F, byte 0x40, byte 0x00]
      | 5 => [byte 0x0F, byte 0x1F, byte 0x44, byte 0x00, byte 0x00]
      | 6 => [byte 0x66, byte 0x0F, byte 0x1F, byte 0x44, byte 0x00, byte 0x00]
      | 7 => [byte 0x0F, byte 0x1F, byte 0x80, byte 0x00, byte 0x00, byte 0x00, byte 0x00]
      | 8 => [byte 0x0F, byte 0x1F, byte 0x84, byte 0x00, byte 0x00, byte 0x00,
              byte 0x00, byte 0x00]
      | 9 => [byte 0x66, byte 0x0F, byte 0x1F, byte 0x84, byte 0x00, byte 0x00,
              byte 0x00, byte 0x00, byte 0x00]
      | _ => []
  | .movRR sz dst src =>
      eGenRmReg sz (.zr dst) (BitVec.ofNat 4 src) [] (byte 0x88) none
  | .movRI sz dst imm =>
      match eOpsizeImm sz (mkRex false false false (dst % 16 / 8 = 1)) imm false with
      | none => []
      | some (prefixes, v, l) =>
          prefixes ++ [byte (0xB0 ||| v.toNat * 8 ||| (dst % 8))] ++ l
  | .movRM sz dst base disp =>
      eGenRmReg sz (.zm none (.regBase base) disp) (BitVec.ofNat 4 dst) []
        (byte 0x8A) none
  | .movMR sz src base disp =>
      eGenRmReg sz (.zm none (.regBase base) disp) (BitVec.ofNat 4 src) []
        (byte 0x88) none
  | .movzxRM sz1 sz2 dst base disp =>
      eGenRmReg sz2 (.zm none (.regBase base) disp) (BitVec.ofNat 4 dst)
        [byte 0x0F] (byte 0xB6) (some (if sz1 = .z16 then 1 else 0))
  | .binopRI op sz dst imm =>
      let rm := ZRM.zr dst
      let opc := op.code
      if op = .ztest then
        if isRax rm then eRaxImm sz imm (byte 0xA8)
        else eRmImm sz rm imm 0 (byte 0xF6)
      else if opc / 8 = 1 then
        if imm = 1 then
          eGenRmReg sz rm (BitVec.ofNat 4 (opc % 8)) [] (byte 0xD0) none
        else
          eRmImm8 sz rm imm (BitVec.ofNat 4 (opc % 8)) (byte 0xC0)
      else if notByte sz && (eImm8 imm).isSome then
        eRmImm8 sz rm imm (BitVec.ofNat 4 opc) (byte 0x83)
      else if isRax rm then
        eRaxImm sz imm (byte (opc * 8 + 4))
      else
        eRmImm sz rm imm (BitVec.ofNat 4 opc) (byte 0x80)
  | .binopRR op sz dst src =>
      let rm := ZRM.zr dst
      if op = .ztest then
        eGenRmReg sz rm (BitVec.ofNat 4 src) [] (byte 0x84) none
      else
        let opc := op.code
        if opc / 8 = 1 then
          if src % 16 = 1 then
            eGenRmReg sz rm (BitVec.ofNat 4 (opc % 8)) [] (byte 0xD2) none
          else []
        else
          eGenRmReg sz rm (BitVec.ofNat 4 src) [] (byte (opc * 8)) none
  | .monop op sz dst =>
      let rm := ZRM.zr dst
      match op with
      | .znot => eGenRmReg sz rm (BitVec.ofNat 4 2) [] (byte 0xF6) none
      | .zneg => eGenRmReg sz rm (BitVec.ofNat 4 3) [] (byte 0xF6) none
      | .zinc => eGenRmReg sz rm 0 [] (byte 0xFF) none
      | .zdec => eGenRmReg sz rm (BitVec.ofNat 4 1) [] (byte 0xFF) none
  | .mul sz src => eGenRmReg sz (.zr src) (BitVec.ofNat 4 4) [] (byte 0xF6) none
  | .div sz src => eGenRmReg sz (.zr src) (BitVec.ofNat 4 6) [] (byte 0xF6) none
  | .cmc => [byte 0xF5]
  | .setcc cond haveRex dst =>
      if cond = .zAlways then []
      else eGenRmReg (.z8 haveRex) (.zr dst) 0 [byte 0x0F]
        (byte (0x90 + cond.code)) none
  | .jcc cond imm =>
      if cond = .zAlways then
        match eImm32 imm with
        | some l => byte 0xE9 :: l
        | none => []
      else if cond = .zP then
        match eImm8_32 imm with
        | some (s, l) =>
            if s = 1 then byte (0x70 + cond.code) :: l
            else if s = 4 then [byte 0x0F, byte (0x80 + cond.code)] ++ l
            else []
        | none => []
      else
        match eImm32 imm with
        | some l => [byte 0x0F, byte (0x80 + cond.code)] ++ l
        | none => []
  | .jmp dst => eOpc (byte 0xFF) 4 (.zr dst)
  | .lea sz dst disp =>
      eGenRmReg sz (.zm none .ripBase disp) (BitVec.ofNat 4 dst) []
        (byte 0x8D) none
  | .sse op => encodeSSE op

end Flapjack.Compiler.Encoders.X64
