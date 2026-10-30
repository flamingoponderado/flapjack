import Flapjack.Compiler.Backend.Semantics.BvlSem.Word

/-! Agreement of closure and BVL fixed-width word primitives. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Flapjack simulation for all 64-bit binary word operations. The remaining
word and floating-point cases are separate proof obligations. -/
theorem wordOp64_agree (op : BackendCommon.Opw) (a b : BitVec 64) :
    ClosSem.doWordApp (.wordOpw .w64 op) [.word64 a, .word64 b] =
      some (.word64 (ClosSem.applyWordOp op a b)) ∧
    BvlSem.doWordApp (.wordOpw .w64 op) [.word64 a, .word64 b] =
      some (.word64 (ClosSem.applyWordOp op a b)) := by
  simp [ClosSem.doWordApp, ClosSem.doWordAppIntegral, BvlSem.doWordApp, BvlSem.doWordAppIntegral]

/-- Flapjack simulation for all 64-bit word shifts. -/
theorem wordShift64_agree (shift : Flapjack.Shift) (amount : Nat) (a : BitVec 64) :
    ClosSem.doWordApp (.wordShift .w64 shift amount) [.word64 a] =
      some (.word64 (SemanticPrimitivesHOL.shift64Lookup shift a amount)) ∧
    BvlSem.doWordApp (.wordShift .w64 shift amount) [.word64 a] =
      some (.word64 (SemanticPrimitivesHOL.shift64Lookup shift a amount)) := by
  simp [ClosSem.doWordApp, ClosSem.doWordAppIntegral, BvlSem.doWordApp, BvlSem.doWordAppIntegral]

end Flapjack.Compiler.Backend.ClosToBvl
