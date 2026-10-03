import Flapjack.Compiler.Backend.WordToStack.ProductionFlatCodec
import Flapjack.Compiler.Backend.WordInst
import Flapjack.Compiler.Backend.WordToStack.ProductionThreeToTwoDomain

namespace Flapjack.WordAlloc
open RiscV WordProgCarrierCodec Compiler.Backend.WordInst

/-- RISC-V disables the original two-register pass. The historical executed
helper only transforms Assign expressions, which the original native flat
convention excludes. Complete structural identity includes both Call bodies.
This is Flapjack API infrastructure, not a separate HOL theorem port. -/
theorem wordThreeToTwoReg_flat_identity {α : Type} (program : WordProg α)
    (flat : productionFlat program = true) : wordThreeToTwoReg program = program := by
  fun_induction wordThreeToTwoReg program <;>
    simp_all [productionFlat]

/-- Actual executed conversion agrees literally with the original disabled
pass on the encoded flat input. Input flatness is the genuine preceding-phase
obligation, not an output-success or target-run assumption. RISC-V's reviewed
configuration has twoRegArith=false; the preceding CSE/copy phase composition
must establish this original input convention. No independent HOL API original. -/
theorem wordThreeToTwoReg_nativeDisabled {width : Nat} [NeZero width]
    (source : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (flat : flatExpConventions native = true) :
    wordLangProgToHOL (wordThreeToTwoReg source) = some (threeToTwoRegProg false native) := by
  rw [productionFlat_codec source native encoded] at flat
  rw [wordThreeToTwoReg_flat_identity source flat, encoded]
  rfl

end Flapjack.WordAlloc
