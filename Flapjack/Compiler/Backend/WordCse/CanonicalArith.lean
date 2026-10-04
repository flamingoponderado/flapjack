import Flapjack.Compiler.Backend.WordCse.ProductionRegisterData

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack RiscV Compiler.Encoders.Asm Compiler.Backend.StackToLab

@[hol "cakeml/compiler/backend/word_cseScript.sml" "canonicalImmReg_def"
  (words_as_type_indexed_bitvec)]
def canonicalImmReg {width : Nat} [NeZero width] (data : Knowledge) : HolRegImm width → HolRegImm width
  | .reg register => .reg (canonicalRegs data register)
  | .imm word => .imm word

@[hol "cakeml/compiler/backend/word_cseScript.sml" "canonicalImmReg'_def"
  (words_as_type_indexed_bitvec)]
def canonicalImmReg' {width : Nat} [NeZero width] (avoid : Nat) (data : Knowledge) :
    HolRegImm width → HolRegImm width
  | .reg register => .reg (canonicalRegs' avoid data register)
  | .imm word => .imm word

/-- All eight original arithmetic equations. Destinations and fourth
carry/overflow fields are retained; the original avoid-destination guards
apply only to Binop, Shift and the three carry/overflow constructors. -/
-- riscv-mi: declaration over the reduced integer carrier.
def canonicalArith {width : Nat} [NeZero width] (data : Knowledge) : HolArith width → HolArith width
  | .binop operator destination left right =>
      .binop operator destination (canonicalRegs' destination data left)
        (canonicalImmReg' destination data right)
  | .shift operator destination left right =>
      .shift operator destination (canonicalRegs' destination data left)
        (canonicalImmReg' destination data right)
  | .div destination left right => .div destination (canonicalRegs data left) (canonicalRegs data right)
  | .longMul first second left right =>
      .longMul first second (canonicalRegs data left) (canonicalRegs data right)
  | .longDiv first second left right quotient =>
      .longDiv first second (canonicalRegs data left) (canonicalRegs data right) (canonicalRegs data quotient)
  | .addCarry destination left right carry =>
      .addCarry destination (canonicalRegs' destination data left) (canonicalRegs' destination data right) carry
  | .addOverflow destination left right flag =>
      .addOverflow destination (canonicalRegs' destination data left) (canonicalRegs' destination data right) flag
  | .subOverflow destination left right flag =>
      .subOverflow destination (canonicalRegs' destination data left) (canonicalRegs' destination data right) flag

/-- Actual immediate canonicalization commutes with the reviewed constructor
codec on related input knowledge. Flapjack API infrastructure, no HOL original. -/
theorem canonicalImmReg_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge) (related : KnowledgeRel width native executed)
    (right : WordRegImm (BitVec width)) :
    HolRegImm.ofWordRegImm (wordCseCanonicalImmReg executed right) =
      canonicalImmReg native (HolRegImm.ofWordRegImm right) := by
  cases right <;> simp [wordCseCanonicalImmReg, HolRegImm.ofWordRegImm, canonicalImmReg,
    canonicalRegs_transport native executed related]

/-- Both original avoid-register immediate branches commute with the codec. -/
theorem canonicalImmRegAvoid_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge) (related : KnowledgeRel width native executed)
    (avoid : Nat) (right : WordRegImm (BitVec width)) :
    HolRegImm.ofWordRegImm (wordCseCanonicalImmReg' avoid executed right) =
      canonicalImmReg' avoid native (HolRegImm.ofWordRegImm right) := by
  cases right <;> simp [wordCseCanonicalImmReg', HolRegImm.ofWordRegImm, canonicalImmReg',
    canonicalRegsAvoid_transport native executed related]

/-- Complete executed/native arithmetic boundary, including the rejected
five-register diagnostic AddCarry. No output encoding success or target run is
assumed. Flapjack API transport, not full CSE correctness or production routing. -/
theorem canonicalArith_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge) (related : KnowledgeRel width native executed)
    (operation : WordArith (BitVec width)) :
    ExecutedCodec.arithFromExecuted? (wordCseCanonicalArith executed operation) =
      (ExecutedCodec.arithFromExecuted? operation).map (canonicalArith native) := by
  cases operation <;> simp [wordCseCanonicalArith, ExecutedCodec.arithFromExecuted?, canonicalArith,
    canonicalRegs_transport native executed related, canonicalRegsAvoid_transport native executed related,
    canonicalImmRegAvoid_transport native executed related]

end Flapjack.Compiler.Backend.WordCse
