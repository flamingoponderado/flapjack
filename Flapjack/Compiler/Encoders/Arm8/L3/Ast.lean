import Flapjack.Compiler.Encoders.Arm8.L3.Defs
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Compiler.Encoders.AsmSem.Arithmetic
import Flapjack.Compiler.Encoders.Arm8.Target

/-!
# L3 ARMv8 byte encoding

The byte-level encoder from `cakeml/compiler/encoders/arm8/arm8_targetScript.sml`
that `arm8_config` uses.  `arm8_encode` turns one L3 `instruction` into four
bytes; `arm8_encode_fail` is the `NoOperation` list used by `arm8_ast` for
unavailable operations.  This file also carries the full `arm8_ast` lowering
(from `asm` instructions to L3 `instruction` values); the exact `arm8_config`
record is in `L3/Configuration.lean` and the `arm8_target` record in
`L3/Target/State.lean`.  The closed-model `arm8Ast`/`arm8Config` remain
separate.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem

/-- `arm8_encode_fail` (`arm8_targetScript.sml:30-31`): the `NoOperation`
instruction list. -/
@[hol "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_encode_fail_def"]
def arm8EncodeFail : List instruction := [NoOperation]

/-- `arm8_encode` (`arm8_targetScript.sml:34-38`): little-endian bytes of the
L3 `Encode` result, or four zero bytes for `BadCode`.  Reviewed exact: the
`ARM8` clause extracts the same four bytes (`BitVec.ofNat 8 ((w >>> 8k).toNat)`
for `(8k+7 >< 8k) w`), `BadCode` gives four zero bytes, and `MachineCode` has
exactly those two constructors.  The callee `Encode` remains a mechanically
rendered L3 definition (`pending_statement_review`). -/
@[hol "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_encode_def"]
noncomputable def arm8Encode (i : instruction) : List (BitVec 8) :=
  match Encode i with
  | .ARM8 w =>
      [BitVec.ofNat 8 ((w >>> 0).toNat),
       BitVec.ofNat 8 ((w >>> 8).toNat),
       BitVec.ofNat 8 ((w >>> 16).toNat),
       BitVec.ofNat 8 ((w >>> 24).toNat)]
  | .BadCode _ => [0, 0, 0, 0]


/-- `arm8_enc_mov_imm` (`arm8_targetScript.sml:63-74`): a 16-bit immediate and
its `MoveWide` half-word index when the value fits one shifted 16-bit slice. -/
@[hol "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_enc_mov_imm_def"]
def arm8EncMovImm (i : BitVec 64) : Option (BitVec 16 × BitVec 2) :=
  if i &&& (0xFFFFFFFFFFFF0000 : BitVec 64) = 0 then
    some (BitVec.ofNat 16 ((i >>> 0).toNat), 0)
  else if i &&& (0xFFFFFFFF0000FFFF : BitVec 64) = 0 then
    some (BitVec.ofNat 16 ((i >>> 16).toNat), 1)
  else if i &&& (0xFFFF0000FFFFFFFF : BitVec 64) = 0 then
    some (BitVec.ofNat 16 ((i >>> 32).toNat), 2)
  else if i &&& (0x0000FFFFFFFFFFFF : BitVec 64) = 0 then
    some (BitVec.ofNat 16 ((i >>> 48).toNat), 3)
  else none

/-- `bop_enc` (`arm8_targetScript.sml:41-45`).  HOL defines only `And`/`Or`/`Xor`;
`Add`/`Sub` are unspecified (`ARB`) and unreachable from `arm8_ast`, so this
total Lean function is not an exact `bop_enc` port. -/
def arm8BopEnc : BinOp → LogicalOp
  | .and => .LogicalOp_AND
  | .or => .LogicalOp_ORR
  | .xor => .LogicalOp_EOR
  | _ => .LogicalOp_AND

/-- `cmp_cond` (`arm8_targetScript.sml:47-57`), a fixed `word4`. -/
@[hol "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "cmp_cond_def"]
def arm8CmpCond : Cmp → BitVec 4
  | .less => 0b1011
  | .lower => 0b0011
  | .equal => 0b0000
  | .test => 0b0000
  | .notLess => 0b1010
  | .notLower => 0b0010
  | .notEqual => 0b0001
  | .notTest => 0b0001

/-- `arm8_load_store_ast` (`arm8_targetScript.sml:78-96`). -/
@[hol "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_load_store_ast_def"]
def arm8LoadStoreAst (ls : MemOp) (r1 r2 : Nat) (a : BitVec 64) : List instruction :=
  let unsigned := !a.msb
  let sx9 : BitVec 64 := BitVec.signExtend 64 (BitVec.ofNat 9 a.toNat)
  let scaled : BitVec 64 :=
    (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((a >>> 3).toNat))) <<< 3
  if a ≠ sx9 && (!unsigned || a ≠ scaled) then
    let b : BitVec 64 := if unsigned then a - (0xFF : BitVec 64) else -a - (0x100 : BitVec 64)
    let c : BitVec 64 := if unsigned then (0xFF : BitVec 64) else -(0x100 : BitVec 64)
    [.Data (.«AddSubImmediate@64» (1, !unsigned, false, b, r2, 26)),
     .LoadStore (.«LoadStoreImmediate@64»
       (3, false, ls, .AccType_NORMAL, false, false, false, false, false,
        unsigned, c, 26, r1))]
  else
    [.LoadStore (.«LoadStoreImmediate@64»
       (3, false, ls, .AccType_NORMAL, false, false, false, false, false,
        unsigned, a, r2, r1))]

/-- `arm8_load_store_ast32` (`arm8_targetScript.sml:98-116`). -/
@[hol "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_load_store_ast32_def"]
def arm8LoadStoreAst32 (ls : MemOp) (r1 r2 : Nat) (a : BitVec 64) : List instruction :=
  let unsigned := !a.msb
  let sx9 : BitVec 64 := BitVec.signExtend 64 (BitVec.ofNat 9 a.toNat)
  let scaled : BitVec 64 :=
    (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((a >>> 2).toNat))) <<< 2
  if a ≠ sx9 && (!unsigned || a ≠ scaled) then
    let b : BitVec 64 := if unsigned then a - (0xFF : BitVec 64) else -a - (0x100 : BitVec 64)
    let c : BitVec 64 := if unsigned then (0xFF : BitVec 64) else -(0x100 : BitVec 64)
    [.Data (.«AddSubImmediate@64» (1, !unsigned, false, b, r2, 26)),
     .LoadStore (.«LoadStoreImmediate@32»
       (2, true, ls, .AccType_NORMAL, false, false, false, false, false,
        unsigned, c, 26, r1))]
  else
    [.LoadStore (.«LoadStoreImmediate@32»
       (2, true, ls, .AccType_NORMAL, false, false, false, false, false,
        unsigned, a, r2, r1))]

/-- `arm8_load_store_ast16` (`arm8_targetScript.sml:118-136`). -/
@[hol "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_load_store_ast16_def"]
def arm8LoadStoreAst16 (ls : MemOp) (r1 r2 : Nat) (a : BitVec 64) : List instruction :=
  let unsigned := !a.msb
  let sx9 : BitVec 64 := BitVec.signExtend 64 (BitVec.ofNat 9 a.toNat)
  let scaled : BitVec 64 :=
    (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((a >>> 1).toNat))) <<< 1
  if a ≠ sx9 && (!unsigned || a ≠ scaled) then
    let b : BitVec 64 := if unsigned then a - (0xFF : BitVec 64) else -a - (0x100 : BitVec 64)
    let c : BitVec 64 := if unsigned then (0xFF : BitVec 64) else -(0x100 : BitVec 64)
    [.Data (.«AddSubImmediate@64» (1, !unsigned, false, b, r2, 26)),
     .LoadStore (.«LoadStoreImmediate@16»
       (1, true, ls, .AccType_NORMAL, false, false, false, false, false,
        unsigned, c, 26, r1))]
  else
    [.LoadStore (.«LoadStoreImmediate@16»
       (1, true, ls, .AccType_NORMAL, false, false, false, false, false,
        unsigned, a, r2, r1))]

/-- The signed 20-bit `Loc` range test used by `arm8_ast` (Flapjack
infrastructure; HOL writes the two `sle` comparisons inline). -/
def arm8LocInRange (a : BitVec 64) : Bool :=
  BitVec.sle (BitVec.signExtend 64 (BitVec.ofNat 20 0x80000)) a &&
  BitVec.sle a (BitVec.signExtend 64 (BitVec.ofNat 20 0x7FFFF))

/-- `arm8_ast` (`arm8_targetScript.sml:138-292`): lower an `asm` instruction to
the L3 ARMv8 `instruction` forms. -/
@[hol "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_ast_def"]
def arm8Ast : HolAsm 64 → List instruction
  | .inst .skip => [NoOperation]
  | .inst (.const r i) =>
      match arm8EncMovImm i with
      | some (imm16, hw) => [.Data (.«MoveWide@64» (1, .z, hw, imm16, r))]
      | none =>
          match arm8EncMovImm (~~~i) with
          | some (imm16, hw) => [.Data (.«MoveWide@64» (1, .n, hw, imm16, r))]
          | none =>
              if (EncodeBitMask i).isSome then
                [.Data (.«LogicalImmediate@64» (1, .LogicalOp_ORR, false, i, 31, r))]
              else
                [.Data (.«MoveWide@64» (1, .k, 0, BitVec.ofNat 16 ((i >>> 0).toNat), r)),
                 .Data (.«MoveWide@64» (1, .k, 1, BitVec.ofNat 16 ((i >>> 16).toNat), r)),
                 .Data (.«MoveWide@64» (1, .k, 2, BitVec.ofNat 16 ((i >>> 32).toNat), r)),
                 .Data (.«MoveWide@64» (1, .k, 3, BitVec.ofNat 16 ((i >>> 48).toNat), r))]
  | .inst (.arith (.binop bop destination source (.reg right))) =>
      [.Data (match bop with
        | .add => .«AddSubShiftedRegister@64»
            (1, false, false, .lsl, right, 0, source, destination)
        | .sub => .«AddSubShiftedRegister@64»
            (1, true, false, .lsl, right, 0, source, destination)
        | x => .«LogicalShiftedRegister@64»
            (1, arm8BopEnc x, false, false, .lsl, 0, right, source, destination))]
  | .inst (.arith (.binop bop destination source (.imm value))) =>
      [.Data (match bop with
        | .add => .«AddSubImmediate@64» (1, false, false, value, source, destination)
        | .sub => .«AddSubImmediate@64» (1, true, false, value, source, destination)
        | .xor =>
            if value = -1 then
              .«LogicalShiftedRegister@64»
                (1, .LogicalOp_ORR, true, false, .lsl, 0, source, 31, destination)
            else
              .«LogicalImmediate@64»
                (1, .LogicalOp_EOR, false, value, source, destination)
        | x => .«LogicalImmediate@64»
            (1, arm8BopEnc x, false, value, source, destination))]
  | .inst (.arith (.shift sh destination source (.imm value))) =>
      let n := value.toNat
      match sh with
      | .lsl =>
          let i6 : BitVec 6 := BitVec.ofNat 6 n
          let r6 : BitVec 6 := -i6
          let s6 : BitVec 6 := (63 : BitVec 6) - i6
          match DecodeBitMasks (TM := 64) (1, s6, r6, false) with
          | some (wmask, tmask) =>
              [.Data (.«BitfieldMove@64»
                (1, true, false, wmask, tmask, r6.toNat, s6.toNat, source, destination))]
          | none => arm8EncodeFail
      | .ror =>
          [.Data (.«ExtractRegister@64»
            (1, BitVec.ofNat 6 n, source, source, destination))]
      | _ =>
          match DecodeBitMasks (TM := 64) (1, (63 : BitVec 6), BitVec.ofNat 6 n, false) with
          | some (wmask, tmask) =>
              [.Data (.«BitfieldMove@64»
                (1, true, sh == .asr, wmask, tmask, n, 63, source, destination))]
          | none => arm8EncodeFail
  | .inst (.arith (.shift sh destination source (.reg right))) =>
      [.Data (.«Shift@64» (1, arm8Shv sh, right, source, destination))]
  | .inst (.arith (.div destination dividend divisor)) =>
      [.Data (.«Division@64» (1, false, divisor, dividend, destination))]
  | .inst (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight)) =>
      [.Data (.MultiplyHigh (false, sourceRight, sourceLeft, destinationLeft)),
       .Data (.«MultiplyAddSub@64»
         (1, false, sourceRight, 31, sourceLeft, destinationRight))]
  | .inst (.arith (.longDiv _ _ _ _ _)) => arm8EncodeFail
  | .inst (.arith (.addCarry destination resultCarry sourceLeft sourceRight)) =>
      [.Data (.«AddSubImmediate@64» (1, true, true, 0, sourceRight, 31)),
       .Data (.«ConditionalCompareImmediate@64»
         (1, false, 0, 0, (false, false, true, false), resultCarry)),
       .Data (.«AddSubCarry@64» (1, false, true, sourceLeft, resultCarry, destination)),
       .Data (.«MoveWide@64» (1, .z, 0, 0, sourceRight)),
       .Data (.«AddSubCarry@64» (1, false, false, 31, sourceRight, sourceRight))]
  | .inst (.arith (.addOverflow destination resultCarry sourceLeft sourceRight)) =>
      [.Data (.«AddSubShiftedRegister@64»
         (1, false, true, .lsl, sourceLeft, 0, resultCarry, destination)),
       .Data (.«ConditionalSelect@64»
         (1, false, true, 7, 31, 31, sourceRight))]
  | .inst (.arith (.subOverflow destination resultCarry sourceLeft sourceRight)) =>
      [.Data (.«AddSubShiftedRegister@64»
         (1, true, true, .lsl, sourceLeft, 0, resultCarry, destination)),
       .Data (.«ConditionalSelect@64»
         (1, false, true, 7, 31, 31, sourceRight))]
  | .inst (.mem .load destination (.addr base offset)) =>
      arm8LoadStoreAst .MemOp_LOAD destination base offset
  | .inst (.mem .load32 destination (.addr base offset)) =>
      arm8LoadStoreAst32 .MemOp_LOAD destination base offset
  | .inst (.mem .load16 destination (.addr base offset)) =>
      arm8LoadStoreAst16 .MemOp_LOAD destination base offset
  | .inst (.mem .load8 destination (.addr base offset)) =>
      [.LoadStore (.«LoadStoreImmediate@8»
        (0, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         !offset.msb, offset, base, destination))]
  | .inst (.mem .store destination (.addr base offset)) =>
      arm8LoadStoreAst .MemOp_STORE destination base offset
  | .inst (.mem .store32 destination (.addr base offset)) =>
      arm8LoadStoreAst32 .MemOp_STORE destination base offset
  | .inst (.mem .store16 destination (.addr base offset)) =>
      arm8LoadStoreAst16 .MemOp_STORE destination base offset
  | .inst (.mem .store8 destination (.addr base offset)) =>
      [.LoadStore (.«LoadStoreImmediate@8»
        (0, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         !offset.msb, offset, base, destination))]
  | .inst (.fp _) => arm8EncodeFail
  | .jump target => [.Branch (.BranchImmediate (target, .BranchType_JMP))]
  | .jumpCmp operator source (.reg right) target =>
      [.Data (if isTest operator then
                .«LogicalShiftedRegister@64»
                  (1, .LogicalOp_AND, false, true, .lsl, 0, right, source, 31)
              else
                .«AddSubShiftedRegister@64»
                  (1, true, true, .lsl, right, 0, source, 31)),
       .Branch (.BranchConditional (target - 4, arm8CmpCond operator))]
  | .jumpCmp operator source (.imm value) target =>
      [.Data (if isTest operator then
                .«LogicalImmediate@64» (1, .LogicalOp_AND, true, value, source, 31)
              else
                .«AddSubImmediate@64» (1, true, true, value, source, 31)),
       .Branch (.BranchConditional (target - 4, arm8CmpCond operator))]
  | .call target => [.Branch (.BranchImmediate (target, .BranchType_CALL))]
  | .jumpReg register => [.Branch (.BranchRegister (register, .BranchType_JMP))]
  | .loc register offset =>
      if arm8LocInRange offset then
        [.Address (false, offset, register)]
      else
        [.Address (false, 0, register),
         .Data (.«MoveWide@64» (1, .k, 0, BitVec.ofNat 16 ((offset >>> 0).toNat), 26)),
         .Data (.«MoveWide@64» (1, .k, 1, BitVec.ofNat 16 ((offset >>> 16).toNat), 26)),
         .Data (.«MoveWide@64» (1, .k, 2, BitVec.ofNat 16 ((offset >>> 32).toNat), 26)),
         .Data (.«MoveWide@64» (1, .k, 3, BitVec.ofNat 16 ((offset >>> 48).toNat), 26)),
         .Data (.«AddSubShiftedRegister@64»
           (1, false, false, .lsl, 26, 0, register, register))]

/-- `arm8_enc` (`arm8_targetScript.sml:290-291`): lower and concatenate the
four-byte encodings of every emitted instruction. -/
@[hol "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_enc_def"]
noncomputable def arm8Enc (instruction : HolAsm 64) : List (BitVec 8) :=
  (arm8Ast instruction).flatMap arm8Encode

end Flapjack.Compiler.Encoders.Arm8.L3
