import Flapjack.Compiler.Encoders.Arm8.Encode
import Flapjack.HolRef

/-!
# ARMv8 target lowering

This is a Lean port of `arm8_ast` and `arm8_enc` from
`cakeml/compiler/encoders/arm8/arm8_targetScript.sml`, restricted to the
instruction forms that the ARMv8 backend emits.  As with the encoder, the
result is compared byte-for-byte with the original CakeML ARMv8 compiler; it is
not claimed to be the full L3 `arm8$instruction` function.

`arm8_enc` in HOL maps each `arm8_ast` result through `arm8_encode`, whose
`BadCode` branch is four zero bytes and whose `arm8_encode_fail` (used for
unavailable operations) is a `NoOperation`.  Both behaviours are reproduced
here.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem

/-- `bop_enc`.  HOL specifies only the `And`/`Or`/`Xor` cases; this total Lean
function additionally returns `none` for the other binops, so it is not claimed
as an exact `@[hol]` port. -/
def bopEnc : BinOp → Option LogicalOp
  | .and => some .and
  | .or => some .orr
  | .xor => some .eor
  | _ => none

/-- `arm8_shv`. -/
@[hol "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_shv_def"]
def arm8Shv : Shift → ShiftType
  | .lsl => .lsl
  | .lsr => .lsr
  | .asr => .asr
  | .ror => .ror

/-- `cmp_cond`.  HOL returns a `word4`; this Lean version stores the same
four-bit value as a `Nat`, so it is not tagged as an exact `@[hol]` port. -/
def cmpCond : Cmp → Nat
  | .less => 0b1011
  | .lower => 0b0011
  | .equal => 0b0000
  | .test => 0b0000
  | .notLess => 0b1010
  | .notLower => 0b0010
  | .notEqual => 0b0001
  | .notTest => 0b0001

/-- The temporary register used by the ARMv8 lowering (`temp = 26w`). -/
def temp : Nat := 26

/-- `arm8_load_store_ast{,_32,_16}`: one scaled load/store, or an add of the
out-of-range offset into the temporary register followed by a small load/store.
-/
def loadStoreAst (size : Nat) (regsizeWord : Bool) (memop : MemOp)
    (destination base : Nat) (offset : W) : List Insn :=
  let unsigned := !offset.msb
  let scaled := (BitVec.ofNat 64 ((offset >>> size).toNat % 4096)) <<< size
  if !fitsSigned 9 offset && (!unsigned || offset ≠ scaled) then
    let b := if unsigned then offset - 0xFF else -offset - 0x100
    let c := if unsigned then (0xFF : W) else -0x100
    [.addSubImmediate (!unsigned) false b base temp,
     .loadStoreImmediate size regsizeWord memop false unsigned c temp destination]
  else
    [.loadStoreImmediate size regsizeWord memop false unsigned offset base destination]

/-- The `Inst` case of `arm8_ast`, for the subset of instructions that CakeML's
ARMv8 backend produces. -/
def arm8Inst : HolInst 64 → List Insn
  | .skip => [.noOp]
  | .const destination value =>
      match encMovImm value with
      | some (imm16, hw) => [.moveWide .z hw imm16 destination]
      | none =>
          match encMovImm (~~~value) with
          | some (imm16, hw) => [.moveWide .n hw imm16 destination]
          | none =>
              if (encodeBitMask value).isSome then
                [.logicalImmediate .orr false value 31 destination]
              else
                [.moveWide .k 0 (value.toNat % 65536) destination,
                 .moveWide .k 1 ((value >>> 16).toNat % 65536) destination,
                 .moveWide .k 2 ((value >>> 32).toNat % 65536) destination,
                 .moveWide .k 3 ((value >>> 48).toNat % 65536) destination]
  | .arith (.binop bop destination source (.reg right)) =>
      match bop with
      | .add => [.addSubShiftedRegister false false .lsl right 0 source destination]
      | .sub => [.addSubShiftedRegister true false .lsl right 0 source destination]
      | _ =>
          match bopEnc bop with
          | some op => [.logicalShiftedRegister op false false .lsl 0 right source destination]
          | none => [.noOp]
  | .arith (.binop bop destination source (.imm value)) =>
      match bop with
      | .add => [.addSubImmediate false false value source destination]
      | .sub => [.addSubImmediate true false value source destination]
      | .xor =>
          if value = -1 then
            [.logicalShiftedRegister .orr true false .lsl 0 source 31 destination]
          else
            [.logicalImmediate .eor false value source destination]
      | _ =>
          match bopEnc bop with
          | some op => [.logicalImmediate op false value source destination]
          | none => [.noOp]
  | .arith (.shift shift destination source (.imm value)) =>
      -- HOL's `n = w2n i`.  LSL truncates through the `word6` rotation fields;
      -- ROR truncates through `n2w n`; LSR/ASR pass `n` itself as `immr`, so
      -- `Encode` returns BadCode when `n >= 64`.
      let raw := value.toNat
      let n := raw % 64
      match shift with
      | .lsl =>
          let r := (64 - n) % 64
          let s := 63 - n
          match decodeBitMasks 1 s r false with
          | some _ => [.bitfieldMove true false r s source destination]
          | none => [.noOp]
      | .ror => [.extractRegister n source source destination]
      | .lsr | .asr =>
          match decodeBitMasks 1 63 n false with
          | some _ =>
              [.bitfieldMove true (shift == .asr) raw 63 source destination]
          | none => [.noOp]
  | .arith (.shift shift destination source (.reg right)) =>
      [.shift (arm8Shv shift) right source destination]
  | .arith (.div destination dividend divisor) =>
      [.division false divisor dividend destination]
  | .arith (.longMul destinationLeft destinationRight sourceLeft sourceRight) =>
      [.multiplyHigh false sourceRight sourceLeft destinationLeft,
       .multiplyAddSub false sourceRight 31 sourceLeft destinationRight]
  | .arith (.longDiv _ _ _ _ _) => [.noOp]
  | .arith (.addCarry destination resultCarry sourceLeft sourceRight) =>
      [.addSubImmediate true true 0 sourceRight 31,
       .conditionalCompareImmediate false 0 0 (false, false, true, false) resultCarry,
       .addSubCarry false true sourceLeft resultCarry destination,
       .moveWide .z 0 0 sourceRight,
       .addSubCarry false false 31 sourceRight sourceRight]
  | .arith (.addOverflow destination resultCarry sourceLeft sourceRight) =>
      [.addSubShiftedRegister false true .lsl sourceLeft 0 resultCarry destination,
       .conditionalSelect false true 7 31 31 sourceRight]
  | .arith (.subOverflow destination resultCarry sourceLeft sourceRight) =>
      [.addSubShiftedRegister true true .lsl sourceLeft 0 resultCarry destination,
       .conditionalSelect false true 7 31 31 sourceRight]
  | .mem .load destination (.addr base offset) =>
      loadStoreAst 3 false .load destination base offset
  | .mem .load32 destination (.addr base offset) =>
      loadStoreAst 2 true .load destination base offset
  | .mem .load16 destination (.addr base offset) =>
      loadStoreAst 1 true .load destination base offset
  | .mem .load8 destination (.addr base offset) =>
      [.loadStoreImmediate 0 false .load false (!offset.msb) offset base destination]
  | .mem .store source (.addr base offset) =>
      loadStoreAst 3 false .store source base offset
  | .mem .store32 source (.addr base offset) =>
      loadStoreAst 2 true .store source base offset
  | .mem .store16 source (.addr base offset) =>
      loadStoreAst 1 true .store source base offset
  | .mem .store8 source (.addr base offset) =>
      [.loadStoreImmediate 0 false .store false (!offset.msb) offset base source]
  | .fp _ => [.noOp]

/-- `arm8_ast`: lower an `asm` instruction to the ARMv8 instruction forms. -/
def arm8Ast : HolAsm 64 → List Insn
  | .inst instruction => arm8Inst instruction
  | .jump target => [.branchImmediate target false]
  | .jumpCmp operator source (.reg right) target =>
      [if isTest operator then
         .logicalShiftedRegister .and false true .lsl 0 right source 31
       else
         .addSubShiftedRegister true true .lsl right 0 source 31,
       .branchConditional (target - 4) (cmpCond operator)]
  | .jumpCmp operator source (.imm value) target =>
      [if isTest operator then
         .logicalImmediate .and true value source 31
       else
         .addSubImmediate true true value source 31,
       .branchConditional (target - 4) (cmpCond operator)]
  | .call target => [.branchImmediate target true]
  | .jumpReg register => [.branchRegister register .jmp]
  | .loc register offset =>
      if fitsSigned 20 offset then
        [.address false offset register]
      else
        [.address false 0 register,
         .moveWide .k 0 (offset.toNat % 65536) temp,
         .moveWide .k 1 ((offset >>> 16).toNat % 65536) temp,
         .moveWide .k 2 ((offset >>> 32).toNat % 65536) temp,
         .moveWide .k 3 ((offset >>> 48).toNat % 65536) temp,
         .addSubShiftedRegister false false .lsl temp 0 register register]

/-- `arm8_enc`: lower and encode, concatenating the bytes of every instruction
in the list. -/
def arm8Enc (instruction : HolAsm 64) : List (BitVec 8) :=
  (arm8Ast instruction).flatMap encodeBytes

end Flapjack.Compiler.Encoders.Arm8
