import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.InstAssign
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.InstArith
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.InstMemory
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.InstFp

namespace Flapjack.WordAlloc

namespace InstWitnesses

/-- Canonical imported state-carrier roundtrip for the assembled Inst case. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end InstWitnesses

/-- Complete HOL evaluate_apply_colour Inst case (1225-1391). All five
instruction families, all eight arithmetic and memory variants, and all sixteen
FP operations are covered by the accepted literal constructor proofs. The
statement has exactly the original three premises and full existential
postcondition. Instructions contain no sub-programs, so no induction hypothesis
is needed. Full program correctness assembly remains separate work. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_Inst {width : Nat} [NeZero width] {C F : Type}
    (instruction : WordLangInst (BitVec width)) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.inst instruction) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.inst instruction) live lt))
          st.locals cst.locals →
      applyColourPost f (.inst instruction) live lt st cst := by
  intro st cst f live lt h
  cases instruction with
  | skip => exact evaluateApplyColour_InstSkip st cst f live lt h
  | const r w => exact evaluateApplyColour_InstConst r w st cst f live lt h
  | fp op => exact evaluateApplyColour_InstFp op st cst f live lt h
  | arith op =>
      cases op with
      | binop op d r ri => exact evaluateApplyColour_InstBinop op d r ri st cst f live lt h
      | shift op d r ri => exact evaluateApplyColour_InstShift op d r ri st cst f live lt h
      | div a b c => exact evaluateApplyColour_InstDiv a b c st cst f live lt h
      | addCarry a b c d => exact evaluateApplyColour_InstAddCarry a b c d st cst f live lt h
      | addOverflow a b c d => exact evaluateApplyColour_InstAddOverflow a b c d st cst f live lt h
      | subOverflow a b c d => exact evaluateApplyColour_InstSubOverflow a b c d st cst f live lt h
      | longMul a b c d => exact evaluateApplyColour_InstLongMul a b c d st cst f live lt h
      | longDiv a b c d e => exact evaluateApplyColour_InstLongDiv a b c d e st cst f live lt h
  | mem op r address =>
      cases address with
      | addr base offset =>
          cases op with
          | load => exact evaluateApplyColour_InstLoad r base offset st cst f live lt h
          | load8 => exact evaluateApplyColour_InstLoad8 r base offset st cst f live lt h
          | load16 => exact evaluateApplyColour_InstLoad16 r base offset st cst f live lt h
          | load32 => exact evaluateApplyColour_InstLoad32 r base offset st cst f live lt h
          | store => exact evaluateApplyColour_InstStore r base offset st cst f live lt h
          | store8 => exact evaluateApplyColour_InstStore8 r base offset st cst f live lt h
          | store16 => exact evaluateApplyColour_InstStore16 r base offset st cst f live lt h
          | store32 => exact evaluateApplyColour_InstStore32 r base offset st cst f live lt h

end Flapjack.WordAlloc
