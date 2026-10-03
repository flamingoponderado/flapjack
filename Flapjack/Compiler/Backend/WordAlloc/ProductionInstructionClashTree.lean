import Flapjack.Compiler.Backend.WordAlloc.ProductionExpressionClashTree

namespace Flapjack.WordAlloc
open Flapjack.Compiler.Encoders.Asm

/-! Actual/native producer infrastructure without independent HOL originals.
Encoder acceptance excludes the separate five-operand AddCarry primitive;
every accepted arithmetic/memory instruction retains its complete source delta.
The original 16-bit memory catchall deliberately produces an empty delta. -/

theorem instructionClashTree_production {width : Nat} [NeZero width]
    (instruction : WordInst (BitVec width)) (native : WordLangInst (BitVec width))
    (encoded : wordLangInstToHOL instruction = some native) :
    RegAlloc.productionClashTreeToNative (wordClashTreeDeltaInst instruction) =
      getDeltaInst (HolInst.ofWordLangInst native) := by
  cases instruction with
  | arith arithmetic =>
      cases arithmetic <;> simp [wordLangInstToHOL, wordLangArithToHOL] at encoded
      all_goals subst native
      all_goals simp [wordClashTreeDeltaInst, RegAlloc.productionClashTreeToNative,
        getDeltaInst, HolInst.ofWordLangInst, HolArith.ofWordLangArith, HolRegImm.ofWordRegImm]
      all_goals split <;> rfl
  | const destination value =>
      simp only [wordLangInstToHOL, Option.some.injEq] at encoded
      subst native
      rfl
  | mem operator destination address =>
      simp only [wordLangInstToHOL, Option.some.injEq] at encoded
      subst native
      cases operator <;> rfl
  | memOffset operator destination address offset =>
      simp only [wordLangInstToHOL, Option.some.injEq] at encoded
      subst native
      cases operator <;> rfl

end Flapjack.WordAlloc
