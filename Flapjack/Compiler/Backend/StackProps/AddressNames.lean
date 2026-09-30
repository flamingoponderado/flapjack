import Flapjack.Compiler.Backend.StackProps.RegisterNames

namespace Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Pre-naming memory-address admissibility. The base uses the logical register
bound, while offsets retain HOL's signed word comparisons and ISA restriction. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "addr_name_def"
  (words_as_type_indexed_bitvec)]
def addrName {width : Nat} [NeZero width] (operator : HolMemop)
    (address : HolAddr width) (config : AsmConfigExact width) : Prop :=
  match address with
  | .addr base offset =>
      regName base config ∧
        (if operator = .load ∨ operator = .store ∨ operator = .load32 ∨
            operator = .store32 then
          asmAddrOffsetOkExact config offset = true
         else if operator = .load16 ∨ operator = .store16 then
          asmHwOffsetOkExact config offset = true ∧ config.isa ≠ .ag32
         else
          asmByteOffsetOkExact config offset = true)

end Flapjack.Compiler.Backend.StackProps
