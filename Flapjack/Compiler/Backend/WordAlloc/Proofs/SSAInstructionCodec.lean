import Flapjack.Compiler.Backend.WordAlloc.SSATransInst
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack production-carrier prerequisite: an instruction accepted by the
existing partial decoder remains decodable after the complete native SSA
instruction transform. Width, map and counter are unrestricted. The input
codec premise describes the actual carrier boundary; output success is proved,
not assumed. There is no independent HOL declaration for this cross-carrier
property, so it is untagged. This alone does not route the full production pass.
-/
theorem ssaCcTransInst_decoderClosure {width : Nat} [NeZero width]
    (instruction : WordLangInst (BitVec width)) (ssa : Spt Nat) (next : Nat)
    (accepted : (wordLangInstFromHOL instruction).isSome = true) :
    (wordLangProgFromHOL (ssaCcTransInst instruction ssa next).1).isSome = true := by
  cases instruction with
  | skip => simp [wordLangInstFromHOL] at accepted
  | const destination value =>
    simp [ssaCcTransInst, nextVarRename, wordLangProgFromHOL, wordLangInstFromHOL]
  | arith operation =>
    cases operation with
    | binop operator destination source right =>
      cases right <;> simp [ssaCcTransInst, nextVarRename,
        wordLangProgFromHOL, wordLangInstFromHOL, wordLangArithFromHOL]
    | shift operator destination source right =>
      cases right <;> simp [ssaCcTransInst, nextVarRename,
        wordLangProgFromHOL, wordLangInstFromHOL, wordLangArithFromHOL]
    | div destination left right =>
      simp [ssaCcTransInst, nextVarRename,
        wordLangProgFromHOL, wordLangInstFromHOL, wordLangArithFromHOL]
    | longMul destinationLeft destinationRight left right =>
      simp [ssaCcTransInst, nextVarRename,
        wordLangProgFromHOL, wordLangInstFromHOL, wordLangArithFromHOL]
    | longDiv destinationLeft destinationRight left right quotient =>
      simp [ssaCcTransInst, nextVarRename,
        wordLangProgFromHOL, wordLangInstFromHOL, wordLangArithFromHOL]
    | addCarry destination left right carry =>
      simp [ssaCcTransInst, nextVarRename,
        wordLangProgFromHOL, wordLangInstFromHOL, wordLangArithFromHOL]
    | addOverflow destination left right flag =>
      simp [ssaCcTransInst, nextVarRename,
        wordLangProgFromHOL, wordLangInstFromHOL, wordLangArithFromHOL]
    | subOverflow destination left right flag =>
      simp [ssaCcTransInst, nextVarRename,
        wordLangProgFromHOL, wordLangInstFromHOL, wordLangArithFromHOL]
  | mem operation destination address =>
    cases address with
    | addr register offset =>
      cases operation <;>
        simp [ssaCcTransInst, nextVarRename, wordLangProgFromHOL, wordLangInstFromHOL]
      all_goals split <;> rfl
  | fp operation => simp [wordLangInstFromHOL] at accepted

end Flapjack.Compiler.Backend.WordAlloc
