import Flapjack.Compiler.Encoders.AsmProps.Target
import Flapjack.Misc.BytesInMemory

namespace Flapjack
open Flapjack.Compiler.Encoders.Asm

/-- Literal mapped-read instruction template check. HOL leaves the unused
return-PC parameter polymorphic; it is retained without a word-type restriction. -/
@[hol "cakeml/compiler/backend/semantics/targetSemScript.sml" "is_valid_mapped_read_def"
  (words_as_type_indexed_bitvec)]
def isValidMappedRead {width : Nat} [NeZero width] {state projection returnPc : Type}
    (pc : BitVec width) (size : BitVec 8) (address : HolAddr width) (register : Nat)
    (_returnPc : returnPc) (target : HolAsmTarget width state projection) (ms : state)
    (domain : BitVec width → Prop) : Prop :=
  if size = 1 then
    bytesInMemoryHOL pc (target.config.encode (.inst (.mem .load8 register address)))
      (target.getByte ms) domain
  else if size = 0 then
    bytesInMemoryHOL pc (target.config.encode (.inst (.mem .load register address)))
      (target.getByte ms) domain
  else if size = 2 then
    bytesInMemoryHOL pc (target.config.encode (.inst (.mem .load16 register address)))
      (target.getByte ms) domain
  else if size = 4 then
    bytesInMemoryHOL pc (target.config.encode (.inst (.mem .load32 register address)))
      (target.getByte ms) domain
  else False

/-- Literal mapped-write instruction template check, including the invalid-size
False clause and the same unused polymorphic return-PC argument. -/
@[hol "cakeml/compiler/backend/semantics/targetSemScript.sml" "is_valid_mapped_write_def"
  (words_as_type_indexed_bitvec)]
def isValidMappedWrite {width : Nat} [NeZero width] {state projection returnPc : Type}
    (pc : BitVec width) (size : BitVec 8) (address : HolAddr width) (register : Nat)
    (_returnPc : returnPc) (target : HolAsmTarget width state projection) (ms : state)
    (domain : BitVec width → Prop) : Prop :=
  if size = 1 then
    bytesInMemoryHOL pc (target.config.encode (.inst (.mem .store8 register address)))
      (target.getByte ms) domain
  else if size = 0 then
    bytesInMemoryHOL pc (target.config.encode (.inst (.mem .store register address)))
      (target.getByte ms) domain
  else if size = 2 then
    bytesInMemoryHOL pc (target.config.encode (.inst (.mem .store16 register address)))
      (target.getByte ms) domain
  else if size = 4 then
    bytesInMemoryHOL pc (target.config.encode (.inst (.mem .store32 register address)))
      (target.getByte ms) domain
  else False

end Flapjack
