import Flapjack.Compiler.Encoders.Asm
import Flapjack.Compiler.Encoders.AsmSem.Arithmetic

/-!
# ARMv8 (AArch64) instruction encoder

The subset of the ARMv8 instruction set produced by CakeML's `arm8_ast`
(`cakeml/compiler/encoders/arm8/arm8_targetScript.sml`), and the encoding of
those instructions into little-endian 32-bit words.

CakeML obtains the words from the ASL-derived `arm8$Encode` function in HOL's
L3 ARMv8 model.  That model has not been ported to Lean, so this file states
the standard AArch64 encodings of exactly the instruction forms that
`arm8_ast` emits.  `Flapjack.Test.Arm8Parity` validates the resulting words
indirectly: the whole assembly, including every emitted code byte, is compared
with the original CakeML Pancake compiler on the checked-in source corpus.

The bit layouts below are the concatenations from `arm8Theory`'s `e_data`,
`e_branch` and `e_load_store` definitions; `fields` keeps them in the same
high-to-low order as HOL's `CC[...]`.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm

/-- A 64-bit machine word (`arm8$ARM8`'s payload is a `word32`, obtained by
truncating the low 32 bits of these words). -/
abbrev W := BitVec 64

/-- Concatenate a list of `(width, value)` fields, most significant first,
exactly like HOL's `CC[...]` / `word_concat`. -/
def fields (fs : List (Nat × Nat)) : BitVec 32 :=
  fs.foldl (fun acc (width, value) =>
    (acc <<< width) ||| BitVec.ofNat 32 (value % 2 ^ width)) 0

/-- `n2w` of a Boolean field. -/
def bit (value : Bool) : Nat := if value then 1 else 0

/-- The `MoveWideOp` constructors of `arm8Script.sml`. -/
inductive MoveWideOp where
  | n
  | z
  | k
  deriving DecidableEq, Repr

/-- The `LogicalOp` constructors produced by `arm8_ast`. -/
inductive LogicalOp where
  | and
  | orr
  | eor
  deriving DecidableEq, Repr

/-- The `ShiftType` constructors of `arm8Script.sml`. -/
inductive ShiftType where
  | lsl
  | lsr
  | asr
  | ror
  deriving DecidableEq, Repr

/-- The slice of `MemOp` produced by the ARMv8 backend. -/
inductive MemOp where
  | load
  | store
  deriving DecidableEq, Repr

/-- The `BranchType` constructors used by `arm8_ast`. -/
inductive BranchKind where
  | jmp
  | call
  | ret
  deriving DecidableEq, Repr

/-- Signed value of the low `bits` bits of `value` (`bits > 0`). -/
def sextValue (bits : Nat) (value : Nat) : Int :=
  let low := value % 2 ^ bits
  if low < 2 ^ (bits - 1) then (low : Int) else (low : Int) - (2 ^ bits : Nat)

/-- `value` is the sign extension of its own low `bits` bits. -/
def fitsSigned (bits : Nat) (value : W) : Bool :=
  decide (value.toInt = sextValue bits value.toNat)

/-- Sign-extend the low `bits` bits of `value` to 64 bits. -/
def sextToWord (bits : Nat) (value : W) : W :=
  BitVec.ofInt 64 (sextValue bits value.toNat)

/-- Rotate a `Nat` right by `n` within `width` bits. -/
def rotateRightWidth (width value n : Nat) : Nat :=
  let value := value % 2 ^ width
  let n := n % width
  ((value >>> n) ||| (value <<< (width - n))) % 2 ^ width

/-- `CountTrailing b w` of `arm8Script.sml`: count the low bits of `w` that
differ from `b`, stopping at the first bit equal to `b` (and at `w = 0` when
`b` is true, `w = 2^64 - 1` when `b` is false). -/
def countTrailing (b : Bool) (w : Nat) : Nat :=
  let rec go (fuel : Nat) (w : Nat) : Nat :=
    match fuel with
    | 0 => 0
    | fuel + 1 =>
        let w := w % 2 ^ 64
        if (w % 2 == 1) = b ∨ (if b then w = 0 else w = 2 ^ 64 - 1) then
          0
        else
          1 + go fuel (w >>> 1)
  go 64 w

/-- `EncodeBitMaskAux` of `arm8Script.sml`, over natural numbers. -/
def encodeBitMaskAux (imm : Nat) : Nat × Nat × Nat :=
  let imm := imm % 2 ^ 64
  let pref0 := countTrailing true imm
  if pref0 = 0 then
    let pref1 := countTrailing false imm
    let run0 := countTrailing true (rotateRightWidth 64 imm pref1)
    let run1 := countTrailing false (rotateRightWidth 64 imm (pref1 + run0))
    (run0 + run1, run1, run1 - pref1)
  else
    let run1 := countTrailing false (rotateRightWidth 64 imm pref0)
    let run0 := countTrailing true (rotateRightWidth 64 imm (pref0 + run1))
    (run0 + run1, run1, run0 + run1 - pref0)

/-- `HighestSetBit` of `arm8Script.sml` (`-1` for zero). -/
def highestSetBit (value : Nat) : Int :=
  if value = 0 then -1 else (Nat.log2 value : Int)

/-- `Ones n` as a natural number. -/
def ones (n : Nat) : Nat := 2 ^ n - 1

/-- `DecodeBitMasks (immN, imms, immr, immediate)` of `arm8Script.sml`,
returning `(wmask, tmask)` as natural numbers. -/
def decodeBitMasks (immN : Nat) (imms immr : Nat) (immediate : Bool) :
    Option (Nat × Nat) :=
  let len := highestSetBit (((immN % 2) <<< 6) ||| (63 - imms % 64))
  if len < 1 then none
  else
    let len := len.toNat
    let esize := 2 ^ len
    let levels := ones len
    let S := imms % 64 &&& levels
    let R := immr % 64 &&& levels
    if immediate && S = levels then none
    else
      let welem := rotateRightWidth esize (ones (S + 1)) R
      -- HOL's `DecodeBitMasks` uses the wrapping six-bit `EX (S - R) (len-1) 0`;
      -- plain `Nat` subtraction truncates for `S < R` and would collapse the mask.
      let onesCount := ((S + 2 ^ len - R) % 2 ^ len) + 1
      let telem := ones onesCount
      let multiplier := (2 ^ 64 - 1) / (2 ^ esize - 1)
      some (welem * multiplier, telem * multiplier)

/-- `EncodeBitMask` of `arm8Script.sml`, returning `(N, imms, immr)`. -/
def encodeBitMask (imm : W) : Option (Nat × Nat × Nat) :=
  let (e, S, R) := encodeBitMaskAux imm.toNat
  let (immN, imms, immr) :=
    if e = 64 then
      (1, S - 1, R)
    else
      (0, (63 - ((e * 2 - 1) % 64)) ||| ((S - 1) % 64), R)
  match decodeBitMasks immN imms immr true with
  | some (imm2, _) => if imm2 = imm.toNat then some (immN, imms, immr) else none
  | none => none

/-- `arm8_enc_mov_imm`: a 16-bit chunk and its `hw` position, if `i` has a
single nonzero 16-bit chunk. -/
def encMovImm (i : W) : Option (Nat × Nat) :=
  if i &&& (~~~(0xFFFF : W)) = 0 then some (i.toNat % 2 ^ 16, 0)
  else if i &&& (~~~(0xFFFF0000 : W)) = 0 then some ((i >>> 16).toNat % 2 ^ 16, 1)
  else if i &&& (~~~(0xFFFF00000000 : W)) = 0 then some ((i >>> 32).toNat % 2 ^ 16, 2)
  else if i &&& (~~~(0xFFFF000000000000 : W)) = 0 then some ((i >>> 48).toNat % 2 ^ 16, 3)
  else none

/-- The ARMv8 instruction forms emitted by `arm8_ast`.  This is a restriction
of HOL's `arm8$instruction`; the field order follows the L3 constructors. -/
inductive Insn where
  | noOp
  | moveWide (op : MoveWideOp) (hw : Nat) (imm16 : Nat) (rd : Nat)
  | addSubImmediate (sub setFlags : Bool) (imm : W) (rn rd : Nat)
  | logicalImmediate (op : LogicalOp) (setFlags : Bool) (imm : W) (rn rd : Nat)
  | logicalShiftedRegister (op : LogicalOp) (invert setFlags : Bool)
      (shift : ShiftType) (imm : Nat) (rm rn rd : Nat)
  | addSubShiftedRegister (sub setFlags : Bool) (shift : ShiftType)
      (rm : Nat) (imm6 : Nat) (rn rd : Nat)
  | bitfieldMove (inzero extend : Bool) (immr imms : Nat) (rn rd : Nat)
  | extractRegister (imms : Nat) (rm rn rd : Nat)
  | shift (shift : ShiftType) (rm rn rd : Nat)
  | division (o1 : Bool) (rm rn rd : Nat)
  | multiplyHigh (u : Bool) (rm rn rd : Nat)
  | multiplyAddSub (o0 : Bool) (rm ra rn rd : Nat)
  | conditionalCompareImmediate (opc : Bool) (imm : W) (cd : Nat)
      (nzcv : Bool × Bool × Bool × Bool) (rn : Nat)
  | conditionalSelect (op o2 : Bool) (cd : Nat) (rm rn rd : Nat)
  | addSubCarry (sub setFlags : Bool) (rm rn rd : Nat)
  | loadStoreImmediate (size : Nat) (regsizeWord : Bool) (memop : MemOp)
      (signed unsignedOffset : Bool) (offset : W) (rn rt : Nat)
  | branchImmediate (imm : W) (call : Bool)
  | branchConditional (imm : W) (cond : Nat)
  | branchRegister (rn : Nat) (kind : BranchKind)
  | address (page : Bool) (imm : W) (rd : Nat)
  deriving DecidableEq, Repr

/-- The `opc` field of `EncodeLogicalOp`.  `none` is HOL's `LO (word2)`. -/
def encodeLogicalOp (op : LogicalOp) (setFlags : Bool) : Option Nat :=
  match op, setFlags with
  | .and, false => some 0
  | .orr, false => some 1
  | .eor, false => some 2
  | .and, true => some 3
  | _, true => none

/-- The `opc` field of `MoveWide`. -/
def moveWideOpBits : MoveWideOp → Nat
  | .n => 0
  | .z => 2
  | .k => 3

/-- The two-bit `ShiftType` encoding. -/
def shiftTypeBits : ShiftType → Nat
  | .lsl => 0
  | .lsr => 1
  | .asr => 2
  | .ror => 3

/-- The two-bit `opc` of `BitfieldMove` for `(inzero, extend)`. -/
def bitfieldOpBits (inzero extend : Bool) : Option Nat :=
  if inzero && extend then some 0
  else if !inzero && !extend then some 1
  else if inzero && !extend then some 2
  else none

/-- Encode one instruction word, following `arm8Theory`'s `Encode`.  `none`
corresponds to HOL's `BadCode` (which `arm8_encode` turns into four zero
bytes). -/
def encodeInsn32 : Insn → Option (BitVec 32)
  | .noOp => some (fields [(24, 0xD50320), (3, 0), (5, 31)])
  | .moveWide op hw imm16 rd =>
      some (fields [(1, 1), (2, moveWideOpBits op), (6, 0b100101),
        (2, hw), (16, imm16), (5, rd)])
  | .addSubImmediate sub setFlags imm rn rd =>
      if imm &&& (~~~(0xFFF : W)) = 0 then
        some (fields [(1, 1), (1, bit sub), (1, bit setFlags), (7, 0b1000100),
          (12, imm.toNat % 4096), (5, rn), (5, rd)])
      else if imm &&& (~~~(0xFFF000 : W)) = 0 then
        some (fields [(1, 1), (1, bit sub), (1, bit setFlags), (7, 0b1000101),
          (12, (imm >>> 12).toNat % 4096), (5, rn), (5, rd)])
      else none
  | .logicalImmediate op setFlags imm rn rd =>
      match encodeBitMask imm, encodeLogicalOp op setFlags with
      | some (n, imms, immr), some opc =>
          some (fields [(1, 1), (2, opc), (6, 0b100100), (1, n),
            (6, immr), (6, imms), (5, rn), (5, rd)])
      | _, _ => none
  | .logicalShiftedRegister op invert setFlags shift imm rm rn rd =>
      match encodeLogicalOp op setFlags with
      | some opc =>
          if imm < 64 then
            some (fields [(1, 1), (2, opc), (5, 0b01010),
              (2, shiftTypeBits shift), (1, bit invert), (5, rm), (6, imm),
              (5, rn), (5, rd)])
          else none
      | none => none
  | .addSubShiftedRegister sub setFlags shift rm imm6 rn rd =>
      some (fields [(1, 1), (1, bit sub), (1, bit setFlags), (5, 0b01011),
        (2, shiftTypeBits shift), (1, 0), (5, rm), (6, imm6), (5, rn), (5, rd)])
  | .bitfieldMove inzero extend immr imms rn rd =>
      match bitfieldOpBits inzero extend with
      | some opc =>
          -- L3's `Encode` casts `immr`/`imms` to `word6` and rejects a value
          -- that does not fit; it does not silently truncate.
          if immr < 64 && imms < 64 then
            some (fields [(1, 1), (2, opc), (6, 0b100110), (1, 1),
              (6, immr), (6, imms), (5, rn), (5, rd)])
          else none
      | none => none
  | .extractRegister imms rm rn rd =>
      some (fields [(11, 1182), (5, rm), (6, imms), (5, rn), (5, rd)])
  | .shift shift rm rn rd =>
      some (fields [(11, 1238), (5, rm), (4, 2), (2, shiftTypeBits shift),
        (5, rn), (5, rd)])
  | .division o1 rm rn rd =>
      some (fields [(11, 1238), (5, rm), (5, 1), (1, bit (!o1)), (5, rn), (5, rd)])
  | .multiplyHigh u rm rn rd =>
      some (fields [(8, 155), (1, bit (!u)), (2, 2), (5, rm), (6, 31), (5, rn), (5, rd)])
  | .multiplyAddSub o0 rm ra rn rd =>
      some (fields [(11, 1240), (5, rm), (1, bit o0), (5, ra), (5, rn), (5, rd)])
  | .conditionalCompareImmediate opc imm cd nzcv rn =>
      if imm.toNat < 32 then
        let (n, z, c, v) := nzcv
        some (fields [(1, 1), (1, bit opc), (9, 466), (5, imm.toNat), (4, cd),
          (2, 2), (5, rn), (1, 0), (4, bit n * 8 + bit z * 4 + bit c * 2 + bit v)])
      else none
  | .conditionalSelect op o2 cd rm rn rd =>
      some (fields [(1, 1), (1, bit op), (9, 212), (5, rm), (4, cd), (1, 0),
        (1, bit o2), (5, rn), (5, rd)])
  | .addSubCarry sub setFlags rm rn rd =>
      some (fields [(1, 1), (1, bit sub), (1, bit setFlags), (8, 208),
        (5, rm), (6, 0), (5, rn), (5, rd)])
  | .loadStoreImmediate size regsizeWord memop signed unsignedOffset offset rn rt =>
      let opc :=
        match memop with
        | .store => 0
        | .load => if !signed then 1 else 2 + bit regsizeWord
      let imm9 := offset.toNat % 512
      let imm12 := (offset >>> size).toNat % 4096
      if unsignedOffset && offset = (BitVec.ofNat 64 imm12) <<< size then
        some (fields [(2, size), (6, 57), (2, opc), (12, imm12), (5, rn), (5, rt)])
      else if fitsSigned 9 offset then
        some (fields [(2, size), (6, 56), (2, opc), (1, 0), (9, imm9), (1, 0),
          (1, 0), (5, rn), (5, rt)])
      else none
  | .branchImmediate imm call =>
      if fitsSigned 28 imm && imm.toNat % 4 = 0 then
        some (fields [(1, bit call), (5, 5), (26, (imm >>> 2).toNat % 2 ^ 26)])
      else none
  | .branchConditional imm cond =>
      if fitsSigned 21 imm && imm.toNat % 4 = 0 then
        some (fields [(8, 84), (19, (imm >>> 2).toNat % 2 ^ 19), (1, 0), (4, cond)])
      else none
  | .branchRegister rn kind =>
      let opc := match kind with | .jmp => 0 | .call => 1 | .ret => 2
      some (fields [(9, 428), (2, opc), (11, 1984), (5, rn), (5, 0)])
  | .address page imm rd =>
      if page then
        -- ADRP: immlo/immhi are bits 13:12 and 32:14 of the page-relative
        -- offset; L3 requires the immediate to be the sign extension of those
        -- 33 bits.
        let immlo := (imm >>> 12).toNat % 4
        let immhi := (imm >>> 14).toNat % 2 ^ 19
        let raw := ((immhi <<< 2) ||| immlo) <<< 12
        if BitVec.ofInt 64 (sextValue 33 raw) = imm then
          some (fields [(1, 1), (2, immlo), (5, 16), (19, immhi), (5, rd)])
        else none
      else
        -- ADR: L3 accepts a signed 21-bit byte offset.
        if fitsSigned 21 imm then
          some (fields [(1, 0), (2, imm.toNat % 4), (5, 16),
            (19, (imm >>> 2).toNat % 2 ^ 19), (5, rd)])
        else none

/-- The 64-bit carrier form used by the backend, obtained by zero-extending
the 32-bit encoding. -/
def encodeInsn (i : Insn) : Option W :=
  (encodeInsn32 i).map (fun w => w.setWidth 64)

/-- Little-endian bytes of an instruction word. -/
def wordBytes (w : W) : List (BitVec 8) :=
  [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-- `arm8_encode`: four bytes for an encodable instruction, four zero bytes
for `BadCode`. -/
def encodeBytes (i : Insn) : List (BitVec 8) :=
  match encodeInsn i with
  | some w => wordBytes w
  | none => [0, 0, 0, 0]

end Flapjack.Compiler.Encoders.Arm8
