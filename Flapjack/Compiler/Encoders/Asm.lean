import Flapjack.HolRef
import Flapjack.Pancake.WordLang
import Flapjack.Compiler.Backend.StackLang

/-!
# Faithful assembler configuration validity predicates

Counterpart of `cakeml/compiler/encoders/asm/asmScript.sml`.  This module ports
the pure Boolean validity predicates that `stackProps$stack_asm_ok_def` and
`stackProps$addr_ok_def` consume: `reg_ok`, `fp_reg_ok`, `reg_imm_ok`,
`offset_ok` and its offset overloads, `arith_ok`, `fp_ok`, `cmp_ok`, and
`inst_ok`, over the faithful `asm` carrier types already present in
`Flapjack.Pancake.WordLang` (`WordLangInst`/`WordLangArith`/
`WordLangAddr`).

The HOL `asm_config` record is represented with all of its fields so the
quantified configuration carrier is HOL-shaped: `ISA`, `encode`
(`'a asm -> word8 list`), `big_endian`, `code_alignment`, `link_reg`,
`avoid_regs`, `reg_count`, `fp_reg_count`, `two_reg_arith`, `valid_imm`, and
the six `(min, max)` offset pairs.  `encode` and `bigEndian` are carried for
carrier fidelity even though none of the validity predicates below read them.
Lean field names are
lowerCamel (`isa`, `codeAlignment`, ...) where HOL uses `ISA`,
`code_alignment`, ...; constructor arity and field types match the HOL
carriers.

`aligned p w` is ported as `asmAligned p w` (the low `p` bits of the word are
zero, matching `alignment$aligned_def`/`alignment$align_def`); the direct HOL
probe `scripts/hol-probes/asm_config_checks_probeScript.sml` checks that
correspondence together with the predicate clauses.
-/

namespace Flapjack.Compiler.Encoders.Asm

open Flapjack

/-! HOL's signed word order as a Boolean on the width-indexed Lean word.
This is the two's-complement interpretation of HOL's polymorphic word `<`;
it is kept local to the assembler counterpart rather than importing a
particular target's comparison instance. -/
def holAsmSignedLess {width : Nat} (left right : BitVec width) : Bool :=
  let sign := 2 ^ (width - 1)
  if left.toNat < sign then
    if right.toNat < sign then decide (left.toNat < right.toNat) else false
  else if right.toNat < sign then
    true
  else
    decide (left.toNat < right.toNat)

/-! Exact width-indexed source counterpart of CakeML
`asm$word_cmp_def` (`cakeml/compiler/encoders/asm/asmScript.sml:313-321`).
The result is Boolean as in HOL; the Crep evaluator separately embeds it as
a word. -/
def wordCmpHOL [NeZero width] (operator : Cmp)
    (left right : BitVec width) : Bool :=
  match operator with
  | .equal => left == right
  | .less => holAsmSignedLess left right
  | .lower => decide (left < right)
  | .test => AndOp.and left right == 0
  | .notEqual => !(left == right)
  | .notLess => !(holAsmSignedLess left right)
  | .notLower => !(decide (left < right))
  | .notTest => AndOp.and left right != 0

/-! Flapjack's word-valued encoding of the Boolean result used by
`crepSem$eval`'s `bitstring$v2w [word_cmp ...]` clause. -/
def wordCmpResultHOL [NeZero width] (operator : Cmp)
    (left right : BitVec width) : BitVec width :=
  if wordCmpHOL operator left right then 1 else 0

/-- Exact HOL `architecture` (`asmScript.sml:149-151`).  Distinct from the RISC-V
state-model `Flapjack.RiscV.Architecture`. -/
inductive AsmArchitecture where
  | armv7
  | armv8
  | mips
  | riscv
  | ag32
  | x86_64
  deriving DecidableEq, Repr

/-! ## Exact width-indexed asm payload carriers

`stackLangScript.sml:24-67` types its word-carrying constructors
(`Inst ('a inst)`, `If cmp num ('a reg_imm) ...`, `ShMemOp memop num ('a addr)`)
through the HOL assembly carriers `asm$inst`, `asm$reg_imm`, `asm$addr`.  HOL
parameterises these by the word dimension `'a` (`imm = 'a word`), so the
faithful Lean counterparts are width-indexed; the generic mirrors in
`Flapjack.Pancake.WordLang` (`WordLangInst`, `WordRegImm`, `WordLangAddr`) are
still polymorphic in the word-value type and stay untagged.  The isomorphisms
below connect the exact carriers to those production carriers.

Exact HOL `asm$binop` (`cakeml/compiler/encoders/asm/asmScript.sml:78-80`):
`binop = Add | Sub | And | Or | Xor`.  Monomorphic and width-independent, so
the Lean mirror is the existing faithful `Flapjack.BinOp`; the alias below is
the exact-tagged name. -/
abbrev HolBinop := Flapjack.BinOp

/-- Exact HOL `asm$cmp` (`cakeml/compiler/encoders/asm/asmScript.sml:82-84`):
`cmp = Equal | Lower | Less | Test | NotEqual | NotLower | NotLess | NotTest`.
Monomorphic and width-independent; the Lean mirror is the existing faithful
`Flapjack.Cmp`. -/
abbrev HolCmp := Flapjack.Cmp

/-- Exact HOL `asm$memop` (`cakeml/compiler/encoders/asm/asmScript.sml:125-128`):
`memop = Load | Load8 | Load16 | Load32 | Store | Store8 | Store16 | Store32`.
Monomorphic and width-independent; the Lean mirror is the existing faithful
`Flapjack.WordMemOp`. -/
abbrev HolMemop := Flapjack.WordMemOp

/-- Exact HOL `asm$reg_imm` (`cakeml/compiler/encoders/asm/asmScript.sml:74-76`):
`reg_imm = Reg reg | Imm ('a imm)` with `imm = 'a word`.  This is the payload
type of stackLang's `If`. -/
inductive HolRegImm (width : Nat) [NeZero width] where
  | reg (name : Nat)
  | imm (value : BitVec width)
  deriving Repr

/-- Exact HOL `asm$arith` (`cakeml/compiler/encoders/asm/asmScript.sml:86-95`):
`Binop binop reg reg ('a reg_imm) | Shift shift reg reg ('a reg_imm) | Div reg
reg reg | LongMul reg reg reg reg | LongDiv reg reg reg reg reg | AddCarry reg
reg reg reg | AddOverflow reg reg reg reg | SubOverflow reg reg reg reg`, with
`shift = ast$shift` (`cakeml/semantics/astScript.sml:21`).  This is a genuine
`arith` inductive whose `binop`/`shift` payloads are the exact `HolRegImm`
carrier (bead flapjack-4ac.6.1.2.2); the production generic mirror
`WordLangArith (BitVec width)` uses `WordRegImm` and is connected by the checked
`HolArith.toWordLangArith`/`ofWordLangArith` codecs. -/
inductive HolArith (width : Nat) [NeZero width] where
  | binop (operator : BinOp) (destination source : Nat) (right : HolRegImm width)
  | shift (operator : Shift) (destination source : Nat) (right : HolRegImm width)
  | div (destination dividend divisor : Nat)
  | longMul (destinationLeft destinationRight sourceLeft sourceRight : Nat)
  | longDiv (destinationLeft destinationRight sourceLeft sourceRight quotient : Nat)
  | addCarry (destination resultCarry sourceLeft sourceRight : Nat)
  | addOverflow (destination resultCarry sourceLeft sourceRight : Nat)
  | subOverflow (destination resultCarry sourceLeft sourceRight : Nat)
  deriving Repr

/-- Exact HOL `asm$addr` (`cakeml/compiler/encoders/asm/asmScript.sml:121-123`):
`addr = Addr reg ('a word)`.  This is the payload type of stackLang's
`ShMemOp`. -/
inductive HolAddr (width : Nat) [NeZero width] where
  | addr (base : Nat) (offset : BitVec width)
  deriving Repr

/-- Exact HOL `asm$inst` (`cakeml/compiler/encoders/asm/asmScript.sml:130-136`):
`inst = Skip | Const reg ('a word) | Arith ('a arith) | Mem memop reg ('a addr)
`.  This is the payload type of stackLang's `Inst`.  `HolArith`,
`HolRegImm` and `HolAddr` are the exact `arith`/`fp`/`reg_imm`/`addr` mirrors
(bead flapjack-4ac.6.1.2.2). -/
inductive HolInst (width : Nat) [NeZero width] where
  | skip
  | const (destination : Nat) (value : BitVec width)
  | arith (operation : HolArith width)
  | mem (operator : HolMemop) (destination : Nat) (address : HolAddr width)
  deriving Repr

namespace HolRegImm

/-- Forget the width index to the production `reg_imm` mirror. -/
def toWordRegImm {width : Nat} [NeZero width] : HolRegImm width → WordRegImm (BitVec width)
  | .reg name => .reg name
  | .imm value => .imm value

/-- Recover the exact carrier from the production `reg_imm` mirror. -/
def ofWordRegImm {width : Nat} [NeZero width] : WordRegImm (BitVec width) → HolRegImm width
  | .reg name => .reg name
  | .imm value => .imm value

@[simp] theorem of_to {width : Nat} [NeZero width] (carrier : HolRegImm width) :
    ofWordRegImm (toWordRegImm carrier) = carrier := by
  cases carrier <;> rfl

@[simp] theorem to_of {width : Nat} [NeZero width] (carrier : WordRegImm (BitVec width)) :
    toWordRegImm (ofWordRegImm carrier) = carrier := by
  cases carrier <;> rfl

end HolRegImm

namespace HolArith

/-- Forget the width index to the production `arith` mirror. -/
def toWordLangArith {width : Nat} [NeZero width] : HolArith width → WordLangArith (BitVec width)
  | .binop operator destination source right =>
      .binop operator destination source (HolRegImm.toWordRegImm right)
  | .shift operator destination source right =>
      .shift operator destination source (HolRegImm.toWordRegImm right)
  | .div destination dividend divisor => .div destination dividend divisor
  | .longMul destinationLeft destinationRight sourceLeft sourceRight =>
      .longMul destinationLeft destinationRight sourceLeft sourceRight
  | .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient =>
      .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient
  | .addCarry destination resultCarry sourceLeft sourceRight =>
      .addCarry destination resultCarry sourceLeft sourceRight
  | .addOverflow destination resultCarry sourceLeft sourceRight =>
      .addOverflow destination resultCarry sourceLeft sourceRight
  | .subOverflow destination resultCarry sourceLeft sourceRight =>
      .subOverflow destination resultCarry sourceLeft sourceRight

/-- Recover the exact carrier from the production `arith` mirror. -/
def ofWordLangArith {width : Nat} [NeZero width] : WordLangArith (BitVec width) → HolArith width
  | .binop operator destination source right =>
      .binop operator destination source (HolRegImm.ofWordRegImm right)
  | .shift operator destination source right =>
      .shift operator destination source (HolRegImm.ofWordRegImm right)
  | .div destination dividend divisor => .div destination dividend divisor
  | .longMul destinationLeft destinationRight sourceLeft sourceRight =>
      .longMul destinationLeft destinationRight sourceLeft sourceRight
  | .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient =>
      .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient
  | .addCarry destination resultCarry sourceLeft sourceRight =>
      .addCarry destination resultCarry sourceLeft sourceRight
  | .addOverflow destination resultCarry sourceLeft sourceRight =>
      .addOverflow destination resultCarry sourceLeft sourceRight
  | .subOverflow destination resultCarry sourceLeft sourceRight =>
      .subOverflow destination resultCarry sourceLeft sourceRight

@[simp] theorem of_to {width : Nat} [NeZero width] (carrier : HolArith width) :
    ofWordLangArith (toWordLangArith carrier) = carrier := by
  cases carrier <;> simp [toWordLangArith, ofWordLangArith]

@[simp] theorem to_of {width : Nat} [NeZero width] (carrier : WordLangArith (BitVec width)) :
    toWordLangArith (ofWordLangArith carrier) = carrier := by
  cases carrier <;> simp [toWordLangArith, ofWordLangArith]

end HolArith

namespace HolAddr

/-- Forget the width index to the production `addr` mirror. -/
def toWordLangAddr {width : Nat} [NeZero width] : HolAddr width → WordLangAddr (BitVec width)
  | .addr base offset => .addr base offset

/-- Recover the exact carrier from the production `addr` mirror. -/
def ofWordLangAddr {width : Nat} [NeZero width] : WordLangAddr (BitVec width) → HolAddr width
  | .addr base offset => .addr base offset

@[simp] theorem of_to {width : Nat} [NeZero width] (carrier : HolAddr width) :
    ofWordLangAddr (toWordLangAddr carrier) = carrier := by
  cases carrier <;> rfl

@[simp] theorem to_of {width : Nat} [NeZero width] (carrier : WordLangAddr (BitVec width)) :
    toWordLangAddr (ofWordLangAddr carrier) = carrier := by
  cases carrier <;> rfl

end HolAddr

namespace HolInst

/-- Forget the width index to the production `inst` mirror. -/
def toWordLangInst {width : Nat} [NeZero width] : HolInst width → WordLangInst (BitVec width)
  | .skip => .skip
  | .const destination value => .const destination value
  | .arith operation => .arith (HolArith.toWordLangArith operation)
  | .mem operator destination address => .mem operator destination address.toWordLangAddr
/-- Recover the exact carrier from the production `inst` mirror. -/
def ofWordLangInst {width : Nat} [NeZero width] : WordLangInst (BitVec width) → HolInst width
  | .skip => .skip
  | .const destination value => .const destination value
  | .arith operation => .arith (HolArith.ofWordLangArith operation)
  | .mem operator destination address => .mem operator destination (HolAddr.ofWordLangAddr address)
set_option linter.unusedSimpArgs false in
@[simp] theorem of_to {width : Nat} [NeZero width] (carrier : HolInst width) :
    ofWordLangInst (toWordLangInst carrier) = carrier := by
  cases carrier with
  | skip => rfl
  | const destination value => rfl
  | arith operation => cases operation <;> simp [toWordLangInst, ofWordLangInst]
  | mem operator destination address => simp [toWordLangInst, ofWordLangInst]
set_option linter.unusedSimpArgs false in
@[simp] theorem to_of {width : Nat} [NeZero width] (carrier : WordLangInst (BitVec width)) :
    toWordLangInst (ofWordLangInst carrier) = carrier := by
  cases carrier with
  | skip => rfl
  | const destination value => rfl
  | arith operation => cases operation <;> simp [toWordLangInst, ofWordLangInst]
  | mem operator destination address => simp [toWordLangInst, ofWordLangInst]
end HolInst

/-- Exact HOL `asm$asm` (`cakeml/compiler/encoders/asm/asmScript.sml:138-145`):
`asm = Inst ('a inst) | Jump ('a word) | JumpCmp cmp reg ('a reg_imm) ('a word)
| Call ('a word) | JumpReg reg | Loc reg ('a word)`.  The width-indexed Lean
mirror uses the exact `HolInst`/`HolRegImm`/`HolCmp` carriers; the production
`AsmData` below is the generic-field carrier consumed by the assembler's
`encode` field. -/
inductive HolAsm (width : Nat) [NeZero width] where
  | inst (value : HolInst width)
  | jump (target : BitVec width)
  | jumpCmp (operator : HolCmp) (source : Nat) (right : HolRegImm width)
      (target : BitVec width)
  | call (target : BitVec width)
  | jumpReg (target : Nat)
  | loc (register : Nat) (offset : BitVec width)
  deriving Repr


/-- HOL `asmScript.sml:139-146`:
`asm = Inst ('a inst) | Jump ('a word) | JumpCmp cmp reg ('a reg_imm) ('a word)
       | Call ('a word) | JumpReg reg | Loc reg ('a word)`.
The assembler's `encode` field consumes this full datatype, not just the
`Inst` payload.  This is the production generic-field rendering of the exact
`HolAsm` above (same constructor arity; fields instantiated at the generic
`WordLangInst`/`WordRegImm`/`Cmp` carriers rather than the exact `Hol*` ones). -/
inductive AsmData (width : Nat) where
  | inst (value : WordLangInst (BitVec width))
  | jump (target : BitVec width)
  | jumpCmp (operator : Cmp) (source : Nat) (right : WordRegImm (BitVec width))
      (target : BitVec width)
  | call (target : BitVec width)
  | jumpReg (target : Nat)
  | loc (register : Nat) (offset : BitVec width)
  deriving Repr

/-- The `asm_config` projections read by the HOL validity predicates
(`asmScript.sml:153-172`). -/
structure AsmConfig (width : Nat) where
  isa : AsmArchitecture
  encode : AsmData width → List UInt8
  bigEndian : Bool
  codeAlignment : Nat
  linkReg : Option Nat
  avoidRegs : List Nat
  regCount : Nat
  /-- Compatibility metadata; the restricted instruction type has no FP operations. -/
  fpRegCount : Nat
  twoRegArith : Bool
  validImm : Sum BinOp Cmp → BitVec width → Bool
  addrOffset : BitVec width × BitVec width
  hwOffset : BitVec width × BitVec width
  byteOffset : BitVec width × BitVec width
  jumpOffset : BitVec width × BitVec width
  cjumpOffset : BitVec width × BitVec width
  locOffset : BitVec width × BitVec width

/-- HOL `alignment$aligned_def`: `aligned p w` clears the low `p` bits. -/
def asmAligned {width : Nat} (alignment : Nat) (value : BitVec width) : Bool :=
  value.toNat % 2 ^ alignment = 0

/-- Exact HOL `asm$asm_config` (`cakeml/compiler/encoders/asm/asmScript.sml:153-172`):
the assembler configuration record, polymorphic in the word dimension in HOL.
Unlike the production `AsmConfig` below, whose `encode` field consumes the
generic `AsmData`, this carrier's `encode` takes the exact `HolAsm` and produces
HOL `word8` lists, matching the HOL field type `'a asm -> word8 list`.  Every
other field coincides with `AsmConfig`.  This is the prerequisite carrier for
restating the `AsmConfig`-taking validity predicates over exact carriers (bead
flapjack-4ac.6.1.2.1). -/
structure AsmConfigExact (width : Nat) [NeZero width] where
  isa : AsmArchitecture
  encode : HolAsm width → List (BitVec 8)
  bigEndian : Bool
  codeAlignment : Nat
  linkReg : Option Nat
  avoidRegs : List Nat
  regCount : Nat
  /-- Compatibility metadata; the restricted instruction type has no FP operations. -/
  fpRegCount : Nat
  twoRegArith : Bool
  validImm : Sum BinOp Cmp → BitVec width → Bool
  addrOffset : BitVec width × BitVec width
  hwOffset : BitVec width × BitVec width
  byteOffset : BitVec width × BitVec width
  jumpOffset : BitVec width × BitVec width
  cjumpOffset : BitVec width × BitVec width
  locOffset : BitVec width × BitVec width

/-- HOL `asmScript.sml:174-176`:
`reg_ok r c <=> r < c.reg_count /\ ~MEM r c.avoid_regs`.
Exact port over the exact `AsmConfigExact` carrier (`encode : HolAsm width → word8 list`)
with the HOL argument order `reg_ok r c`; the width-general executed `asmRegOk`
remains the untagged production form.  Bead flapjack-4ac.6.1.2. -/
def asmRegOkExact {width : Nat} [NeZero width] (register : Nat)
    (config : AsmConfigExact width) : Bool :=
  register < config.regCount && !config.avoidRegs.contains register

/-- HOL `asmScript.sml:182-187`:
`reg_imm_ok b (Reg r) c = reg_ok r c` /
`reg_imm_ok b (Imm w) c = ((b = INL Xor) /\ (w = -1w) \/ c.valid_imm b w)`.
Exact port over the exact `AsmConfigExact` carrier and the exact `HolRegImm`
(`'a reg_imm`); the `Sum BinOp Cmp` (`binop + cmp`) immediate policy is the
`validImm` field, and `w = -1w` is `value == -1`.  Bead flapjack-4ac.6.1.2. -/
def asmRegImmOkExact {width : Nat} [NeZero width] (operator : Sum BinOp Cmp)
    (right : HolRegImm width) (config : AsmConfigExact width) : Bool :=
  match right with
  | .reg register => asmRegOkExact register config
  | .imm value =>
      (operator == .inl .xor && value == -1) || config.validImm operator value

/-- HOL `asmScript$cmp_ok_def` (`asmScript.sml:270-272`):
`cmp_ok cmp r ri c <=> reg_ok r c /\ reg_imm_ok (INR cmp) ri c`.
Exact port over the exact `AsmConfigExact` carrier and the exact `HolRegImm`
(`'a reg_imm`); `reg_ok`/`reg_imm_ok` become `asmRegOkExact`/`asmRegImmOkExact`
and `INR cmp` is `Sum.inr operator`.  The width-general executed `asmCmpOk`
remains the untagged production form.  Bead flapjack-4ac.6.1.2. -/
def asmCmpOkExact {width : Nat} [NeZero width] (operator : Cmp) (register : Nat)
    (right : HolRegImm width) (config : AsmConfigExact width) : Bool :=
  asmRegOkExact register config && asmRegImmOkExact (.inr operator) right config

/-- HOL `asmScript$arith_ok_def` (`asmScript.sml:191-229`), exact port over the
exact `AsmConfigExact` carrier and the exact `HolArith`/`HolRegImm` (`'a arith`/
`'a reg_imm`).  `reg_ok`/`reg_imm_ok` become `asmRegOkExact`/`asmRegImmOkExact`,
`INL b` is `Sum.inl operator`, `dimindex(:'a)` is `width`, and `c.ISA = x86_64`
is `config.isa == .x86_64`.  The width-general executed `asmArithOk` remains the
untagged production form.  Bead flapjack-4ac.6.1.2. -/
def asmArithOkExact {width : Nat} [NeZero width] (operation : HolArith width)
    (config : AsmConfigExact width) : Bool :=
  match operation with
  | .binop operator destination source right =>
      (!config.twoRegArith || destination == source ||
          (operator == .or && (match right with
            | .reg register => register == source
            | .imm _ => false))) &&
        asmRegOkExact destination config && asmRegOkExact source config &&
        asmRegImmOkExact (.inl operator) right config
  | .shift operator destination source right =>
      (!config.twoRegArith || destination == source) &&
        asmRegOkExact destination config && asmRegOkExact source config &&
        (match right with
         | .imm value => (!(value == 0) || operator == .lsl) && value.toNat < width
         | .reg register =>
             asmRegOkExact register config && (!(config.isa == .x86_64) || register == 1))
  | .div destination dividend divisor =>
      asmRegOkExact destination config && asmRegOkExact dividend config &&
        asmRegOkExact divisor config &&
        (config.isa == .armv8 || config.isa == .mips || config.isa == .riscv)
  | .longMul destinationLeft destinationRight sourceLeft sourceRight =>
      asmRegOkExact destinationLeft config && asmRegOkExact destinationRight config &&
        asmRegOkExact sourceLeft config && asmRegOkExact sourceRight config &&
        (!(config.isa == .x86_64) ||
          (destinationLeft == 2 && destinationRight == 0 && sourceLeft == 0)) &&
        (!(config.isa == .armv7) || !(destinationLeft == destinationRight)) &&
        (!(config.isa == .armv8 || config.isa == .riscv || config.isa == .ag32) ||
          (!(destinationLeft == sourceLeft) && !(destinationLeft == sourceRight)))
  | .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient =>
      (config.isa == .x86_64) && destinationLeft == 0 && destinationRight == 2 &&
        sourceLeft == 2 && sourceRight == 0 && asmRegOkExact quotient config
  | .addCarry destination result sourceLeft sourceRight =>
      (!config.twoRegArith || destination == result) &&
        asmRegOkExact destination config && asmRegOkExact result config &&
        asmRegOkExact sourceLeft config && asmRegOkExact sourceRight config &&
        (!(config.isa == .mips || config.isa == .riscv) ||
          (!(destination == sourceLeft) && !(destination == sourceRight)))
  | .addOverflow destination result sourceLeft sourceRight =>
      (!config.twoRegArith || destination == result) &&
        asmRegOkExact destination config && asmRegOkExact result config &&
        asmRegOkExact sourceLeft config && asmRegOkExact sourceRight config &&
        (!(config.isa == .mips || config.isa == .riscv) || !(destination == sourceLeft))
  | .subOverflow destination result sourceLeft sourceRight =>
      (!config.twoRegArith || destination == result) &&
        asmRegOkExact destination config && asmRegOkExact result config &&
        asmRegOkExact sourceLeft config && asmRegOkExact sourceRight config &&
        (!(config.isa == .mips || config.isa == .riscv) || !(destination == sourceLeft))

/--
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    The HOL tag was withdrawn. -/
def asmRegOk {width : Nat} (config : AsmConfig width) (register : Nat) : Bool :=
  register < config.regCount && !config.avoidRegs.contains register

/--
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    The HOL tag was withdrawn. -/
def asmRegImmOk {width : Nat} (config : AsmConfig width) (operator : Sum BinOp Cmp) :
    WordRegImm (BitVec width) → Bool
  | .reg register => asmRegOk config register
  | .imm value =>
      (operator == .inl .xor && value == -1) || config.validImm operator value

/-- HOL `offset_ok_def` uses the signed word comparison `<=` (HOL's `<=` on
words is signed, unlike `word_ls`), so the bounds are compared as integers.
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    -/
def asmOffsetOk {width : Nat} (alignment : Nat)
    (bounds : BitVec width × BitVec width) (offset : BitVec width) : Bool :=
  bounds.1.toInt ≤ offset.toInt && offset.toInt ≤ bounds.2.toInt &&
    asmAligned alignment offset

def asmAddrOffsetOk {width : Nat} (config : AsmConfig width) (offset : BitVec width) : Bool :=
  asmOffsetOk 0 config.addrOffset offset

def asmHwOffsetOk {width : Nat} (config : AsmConfig width) (offset : BitVec width) : Bool :=
  asmOffsetOk 0 config.hwOffset offset

def asmByteOffsetOk {width : Nat} (config : AsmConfig width) (offset : BitVec width) : Bool :=
  asmOffsetOk 0 config.byteOffset offset

def asmJumpOffsetOk {width : Nat} (config : AsmConfig width) (offset : BitVec width) : Bool :=
  asmOffsetOk config.codeAlignment config.jumpOffset offset

def asmCjumpOffsetOk {width : Nat} (config : AsmConfig width) (offset : BitVec width) : Bool :=
  asmOffsetOk config.codeAlignment config.cjumpOffset offset

def asmLocOffsetOk {width : Nat} (config : AsmConfig width) (offset : BitVec width) : Bool :=
  asmOffsetOk config.codeAlignment config.locOffset offset

/-- HOL `asmScript$arith_ok_def` (`asmScript.sml:191-229`).
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    -/
def asmArithOk {width : Nat} (config : AsmConfig width) :
    WordLangArith (BitVec width) → Bool
  | .binop operator destination source right =>
      (!config.twoRegArith || destination == source ||
          (operator == .or && right == .reg source)) &&
        asmRegOk config destination && asmRegOk config source &&
        asmRegImmOk config (.inl operator) right
  | .shift operator destination source right =>
      (!config.twoRegArith || destination == source) &&
        asmRegOk config destination && asmRegOk config source &&
        (match right with
         | .imm value => (!(value == 0) || operator == .lsl) && value.toNat < width
         | .reg register =>
             asmRegOk config register && (!(config.isa == .x86_64) || register == 1))
  | .div destination dividend divisor =>
      asmRegOk config destination && asmRegOk config dividend &&
        asmRegOk config divisor &&
        (config.isa == .armv8 || config.isa == .mips || config.isa == .riscv)
  | .longMul destinationLeft destinationRight sourceLeft sourceRight =>
      asmRegOk config destinationLeft && asmRegOk config destinationRight &&
        asmRegOk config sourceLeft && asmRegOk config sourceRight &&
        (!(config.isa == .x86_64) ||
          (destinationLeft == 2 && destinationRight == 0 && sourceLeft == 0)) &&
        (!(config.isa == .armv7) || !(destinationLeft == destinationRight)) &&
        (!(config.isa == .armv8 || config.isa == .riscv || config.isa == .ag32) ||
          (!(destinationLeft == sourceLeft) && !(destinationLeft == sourceRight)))
  | .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient =>
      (config.isa == .x86_64) && destinationLeft == 0 && destinationRight == 2 &&
        sourceLeft == 2 && sourceRight == 0 && asmRegOk config quotient
  | .addCarry destination result sourceLeft sourceRight =>
      (!config.twoRegArith || destination == result) &&
        asmRegOk config destination && asmRegOk config result &&
        asmRegOk config sourceLeft && asmRegOk config sourceRight &&
        (!(config.isa == .mips || config.isa == .riscv) ||
          (!(destination == sourceLeft) && !(destination == sourceRight)))
  | .addOverflow destination result sourceLeft sourceRight =>
      (!config.twoRegArith || destination == result) &&
        asmRegOk config destination && asmRegOk config result &&
        asmRegOk config sourceLeft && asmRegOk config sourceRight &&
        (!(config.isa == .mips || config.isa == .riscv) || !(destination == sourceLeft))
  | .subOverflow destination result sourceLeft sourceRight =>
      (!config.twoRegArith || destination == result) &&
        asmRegOk config destination && asmRegOk config result &&
        asmRegOk config sourceLeft && asmRegOk config sourceRight &&
        (!(config.isa == .mips || config.isa == .riscv) || !(destination == sourceLeft))

/-- HOL `asmScript$cmp_ok_def` (`asmScript.sml:270-272`).
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    -/
def asmCmpOk {width : Nat} (config : AsmConfig width) (operator : Cmp)
    (register : Nat) (right : WordRegImm (BitVec width)) : Bool :=
  asmRegOk config register && asmRegImmOk config (.inr operator) right

/-- HOL `asmScript$inst_ok_def` (`asmScript.sml:286-299`).
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    -/
def asmInstOk {width : Nat} (config : AsmConfig width) : WordLangInst (BitVec width) → Bool
  | .skip => true
  | .const destination _ => asmRegOk config destination
  | .arith operation => asmArithOk config operation
  | .mem operator destination (.addr base offset) =>
      asmRegOk config destination && asmRegOk config base &&
        (if operator == .load || operator == .store || operator == .load32 ||
            operator == .store32 then
          asmAddrOffsetOk config offset
         else if operator == .load16 || operator == .store16 then
          asmHwOffsetOk config offset && !(config.isa == .ag32)
         else
          asmByteOffsetOk config offset)

/-- HOL `asmScript$asm_ok_def` (`asmScript.sml:301-313`).
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    -/
def asmOk {width : Nat} (config : AsmConfig width) : AsmData width → Bool
  | .inst inner => asmInstOk config inner
  | .jump target => asmJumpOffsetOk config target
  | .jumpCmp operator source right target =>
      asmCjumpOffsetOk config target && asmCmpOk config operator source right
  | .call target =>
      (match config.linkReg with
        | some register => asmRegOk config register
        | none => false) &&
        asmJumpOffsetOk config target
  | .jumpReg target => asmRegOk config target
  | .loc register offset => asmRegOk config register && asmLocOffsetOk config offset


/-! ## RISC-V configuration

Exact 64-bit field values of HOL `riscv_config_def`
(`cakeml/compiler/encoders/riscv/riscv_targetScript.sml:277-304`).

`encode` uses the legacy production AsmData/UInt8 carriers and is a placeholder, so the
definition is named `riscvConfigForChecks`: the HOL value is
`riscv_enc = LIST_BIND riscv_encode ∘ riscv_ast`, whose full native instruction encoder now lives in
`Flapjack/Compiler/Encoders/RiscV/Target.lean`. A caller that read this legacy
record's `encode` would still emit empty code. No validity predicate in this module (or in `stackProps$stack_asm_ok`)
reads `encode`, so every check-relevant projection is exact, but the record as
a whole is NOT a complete port and no `@[hol]` tag is attached. The complete native configuration lives in
`RiscV/Target/Configuration.lean`; the remaining actual production encoder
route is tracked by bead `flapjack-pxn.18.5.15.9.11.1.3.2`. -/

/-- HOL `min12` (`sw2sw (INT_MINw : word12) : word64`). -/
def riscvMin12 : BitVec 64 := BitVec.ofInt 64 (-2048)

/-- HOL `max12` (`sw2sw (INT_MAXw : word12) : word64`). -/
def riscvMax12 : BitVec 64 := BitVec.ofInt 64 2047

/-- HOL `min21` (`sw2sw (INT_MINw : 21 word) : word64`). -/
def riscvMin21 : BitVec 64 := BitVec.ofInt 64 (-1048576)

/-- HOL `max21` (`sw2sw (INT_MAXw : 21 word) : word64`). -/
def riscvMax21 : BitVec 64 := BitVec.ofInt 64 1048575

/-- HOL `min32` (`sw2sw (INT_MINw : word32) : word64`). -/
def riscvMin32 : BitVec 64 := BitVec.ofInt 64 (-2147483648)

/-- The `jump_offset`/`loc_offset` maximum `0x7FFFF7FFw`. -/
def riscvJumpMax : BitVec 64 := BitVec.ofNat 64 0x7FFFF7FF

/-- HOL `riscv_config.valid_imm`: `Sub` uses a strict lower bound, everything
else a non-strict one, both signed word comparisons. -/
def riscvValidImm : Sum BinOp Cmp → BitVec 64 → Bool := fun operator value =>
  (match operator with
    | .inl .sub => decide (riscvMin12.toInt < value.toInt)
    | _ => decide (riscvMin12.toInt ≤ value.toInt)) &&
  decide (value.toInt ≤ riscvMax12.toInt)

/-- The RISC-V assembler configuration at 64-bit, for the check predicates
only. Check fields match HOL `riscv_config` exactly (see
`scripts/hol-probes/riscv_config_probe.out`); `encode` is the documented
placeholder, so this record is not a complete HOL `riscv_config` port and
carries no `@[hol]` tag. -/
def riscvConfigForChecks : AsmConfig 64 where
  isa := .riscv
  encode := fun _ => []
  bigEndian := false
  codeAlignment := 2
  linkReg := some 1
  avoidRegs := [0, 2, 3, 4, 31]
  regCount := 32
  fpRegCount := 0
  twoRegArith := false
  validImm := riscvValidImm
  addrOffset := (riscvMin12, riscvMax12)
  hwOffset := (riscvMin12, riscvMax12)
  byteOffset := (riscvMin12, riscvMax12)
  jumpOffset := (riscvMin32, riscvJumpMax)
  cjumpOffset := (riscvMin21 + 8, riscvMax21 + 4)
  locOffset := (riscvMin32, riscvJumpMax)

/-- HOL `asmScript$offset_ok_def` (`asmScript.sml:274-276`): exact positive-width
    port.  HOL `offset_ok a offset w = let (min,max) = offset in min <= w /\ w <= max /\ aligned a w`
    where HOL word `<=` is the signed comparison rendered here as `toInt`, and
    `aligned` (lean `asmAligned`) matches `alignmentScript$aligned`.  This
    declaration takes no `AsmConfig`, so it carries no production-carrier
    mismatch and is tagged exact (coordinator source review, bead
    flapjack-4ac.6.1.2.1). -/
def asmOffsetOkExact {width : Nat} [NeZero width] (alignment : Nat)
    (bounds : BitVec width × BitVec width) (offset : BitVec width) : Bool :=
  bounds.1.toInt ≤ offset.toInt && offset.toInt ≤ bounds.2.toInt &&
    asmAligned alignment offset

/-! ## Exact `inst_ok_def` port over `AsmConfigExact`/`HolInst`

The offset helpers are the HOL overloads `addr_offset_ok`/`hw_offset_ok`/
`byte_offset_ok` (`asmScript.sml:279-281`) built on the exact `offset_ok`
(`asmOffsetOkExact`).  They are placed here because they reference
`asmOffsetOkExact`, which is declared above; the rest of the exact predicate
in `inst_ok_def` reads the exact `HolInst`/`HolArith`/`HolRegImm`
carriers (bead flapjack-4ac.6.1.2). -/

def asmAddrOffsetOkExact {width : Nat} [NeZero width] (config : AsmConfigExact width)
    (offset : BitVec width) : Bool :=
  asmOffsetOkExact 0 config.addrOffset offset

def asmHwOffsetOkExact {width : Nat} [NeZero width] (config : AsmConfigExact width)
    (offset : BitVec width) : Bool :=
  asmOffsetOkExact 0 config.hwOffset offset

def asmByteOffsetOkExact {width : Nat} [NeZero width] (config : AsmConfigExact width)
    (offset : BitVec width) : Bool :=
  asmOffsetOkExact 0 config.byteOffset offset

/-- HOL `asmScript$inst_ok_def` (`asmScript.sml:286-299`): exact positive-width
    port over the exact `HolInst` carrier and the exact `AsmConfigExact`; the
    `arith_ok`/`fp_ok`/`reg_ok` calls read the exact reference resolutions.  The
    production `asmInstOk` differs in its generic `WordLangInst`/`AsmConfig`
    carriers. -/
def asmInstOkExact {width : Nat} [NeZero width] (instruction : HolInst width)
    (config : AsmConfigExact width) : Bool :=
  match instruction with
  | .skip => true
  | .const destination _ => asmRegOkExact destination config
  | .arith operation => asmArithOkExact operation config
  | .mem operator destination (.addr base offset) =>
      asmRegOkExact destination config && asmRegOkExact base config &&
        (if operator == .load || operator == .store || operator == .load32 ||
            operator == .store32 then
          asmAddrOffsetOkExact config offset
         else if operator == .load16 || operator == .store16 then
          asmHwOffsetOkExact config offset && !(config.isa == .ag32)
         else
          asmByteOffsetOkExact config offset)

/-! ## Exact `asm_ok_def` port over `AsmConfigExact`/`HolAsm`

The `jump_offset_ok`/`cjump_offset_ok`/`loc_offset_ok` overloads
(`asmScript.sml:282-284`) use the configuration's `code_alignment`; they are
built on the exact `asmOffsetOkExact` (`offset_ok_def`).  The instruction
payload is checked by the exact `asmInstOkExact`, and `cmp_ok` by the exact
`asmCmpOkExact` over `HolRegImm` (bead flapjack-4ac.6.1.2). -/

def asmJumpOffsetOkExact {width : Nat} [NeZero width] (config : AsmConfigExact width)
    (offset : BitVec width) : Bool :=
  asmOffsetOkExact config.codeAlignment config.jumpOffset offset

def asmCjumpOffsetOkExact {width : Nat} [NeZero width] (config : AsmConfigExact width)
    (offset : BitVec width) : Bool :=
  asmOffsetOkExact config.codeAlignment config.cjumpOffset offset

def asmLocOffsetOkExact {width : Nat} [NeZero width] (config : AsmConfigExact width)
    (offset : BitVec width) : Bool :=
  asmOffsetOkExact config.codeAlignment config.locOffset offset

/-- HOL `asmScript$asm_ok_def` (`asmScript.sml:301-313`): exact positive-width
    port over the exact `HolAsm` carrier and the exact `AsmConfigExact`.  The
    production `asmOk` differs in its generic `AsmData`/`AsmConfig` carriers. -/
def asmOkExact {width : Nat} [NeZero width] (instruction : HolAsm width)
    (config : AsmConfigExact width) : Bool :=
  match instruction with
  | .inst inner => asmInstOkExact inner config
  | .jump target => asmJumpOffsetOkExact config target
  | .jumpCmp operator source right target =>
      asmCjumpOffsetOkExact config target && asmCmpOkExact operator source right config
  | .call target =>
      (match config.linkReg with
        | some register => asmRegOkExact register config
        | none => false) &&
        asmJumpOffsetOkExact config target
  | .jumpReg register => asmRegOkExact register config
  | .loc register offset => asmRegOkExact register config && asmLocOffsetOkExact config offset

/-- Exact port of HOL `asmScript$is_load_def` (`asmScript.sml:324-330`):
    `is_load` is true for the four load memory operations.  The carrier
    `HolMemop` is the reviewed exact alias of the eight-constructor
    `Flapjack.WordMemOp` (`memop`), so the clause-for-clause equations match. -/
def asmIsLoad (operator : HolMemop) : Bool :=
  match operator with
  | .load | .load8 | .load16 | .load32 => true
  | _ => false

end Flapjack.Compiler.Encoders.Asm
