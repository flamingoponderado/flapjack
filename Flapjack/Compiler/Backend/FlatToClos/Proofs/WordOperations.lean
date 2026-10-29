import Flapjack.Compiler.Backend.FlatToClos.Proofs.ValueRelation
import Flapjack.Compiler.Backend.Semantics.ClosSem.Word

/-! Word-operation facts over the preliminary flat-to-closure relation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL

/-- Byte arithmetic consumes the integer encodings of its byte operands and
returns the integer encoding of the word result. -/
theorem word8Op_related (op : BackendCommon.Opw) (a b : BitVec 8) :
    ClosSem.doWordAppIntegral (.wordOpw .w8 op) [.number a.toNat, .number b.toNat] =
        some (.number (ClosSem.applyWordOp op a b).toNat) ∧
      ValueRel (.litv (.word8 (ClosSem.applyWordOp op a b)))
        (.number (ClosSem.applyWordOp op a b).toNat) := by
  constructor
  · simp [ClosSem.doWordAppIntegral, ClosSem.intToByte_toNat]
  · exact .word8 _

/-- Word64 arithmetic preserves the fixed-width value representation. -/
theorem word64Op_related (op : BackendCommon.Opw) (a b : BitVec 64) :
    ClosSem.doWordAppIntegral (.wordOpw .w64 op) [.word64 a, .word64 b] =
        some (.word64 (ClosSem.applyWordOp op a b)) ∧
      ValueRel (.litv (.word64 (ClosSem.applyWordOp op a b)))
        (.word64 (ClosSem.applyWordOp op a b)) := ⟨rfl, .word64 _⟩

/-- Byte and word64 shifts retain the related value representations. -/
theorem wordShift_related (shift : Flapjack.Shift) (amount : Nat) (byte : BitVec 8) (word : BitVec 64) :
    ClosSem.doWordAppIntegral (.wordShift .w8 shift amount) [.number byte.toNat] =
        some (.number (shift8Lookup shift byte amount).toNat) ∧
    ValueRel (.litv (.word8 (shift8Lookup shift byte amount))) (.number (shift8Lookup shift byte amount).toNat) ∧
    ClosSem.doWordAppIntegral (.wordShift .w64 shift amount) [.word64 word] =
        some (.word64 (shift64Lookup shift word amount)) ∧
    ValueRel (.litv (.word64 (shift64Lookup shift word amount))) (.word64 (shift64Lookup shift word amount)) := by
  refine ⟨?_, .word8 _, rfl, .word64 _⟩
  simp [ClosSem.doWordAppIntegral, ClosSem.intToByte_toNat]

end Flapjack.Compiler.Backend.FlatToClos
