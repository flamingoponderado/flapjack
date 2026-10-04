import Flapjack.Compiler.Backend.WordCopy
import Flapjack.Compiler.Backend.WordUnreach.ProductionDecoderDomain

namespace Flapjack.Compiler.Backend.WordCopy
open Flapjack WordUnreach

/-! Actual decoder-image infrastructure for native copy propagation. These
have no separate HOL original. The instruction/program clauses are those of
the reviewed pass; decoder acceptance is preserved rather than assumed for its
output. Whole production caller adoption remains open. -/

theorem copyPropInst_decoderDomain {width : Nat} [NeZero width]
    (instruction : WordLangInst (BitVec width)) (state : CopyState)
    (accepted : (wordLangInstFromHOL instruction).isSome = true) :
    decoderDomain (copyPropInst instruction state).1 = true := by
  cases instruction <;> simp_all [wordLangInstFromHOL, copyPropInst, decoderDomain]
  case arith operation =>
    cases operation <;> simp_all [wordLangArithFromHOL, decoderDomain,
      wordLangInstFromHOL]
  case mem operator destination address =>
    cases address
    cases operator <;> simp [decoderDomain, wordLangInstFromHOL]
    all_goals split <;> rfl

theorem copyPropProg_decoderDomain {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (state : CopyState)
    (accepted : decoderDomain program = true) :
    decoderDomain (copyPropProg program state).1 = true := by
  fun_induction copyPropProg program state
  all_goals simp_all only [decoderDomain, Bool.and_eq_true]
  all_goals try exact copyPropInst_decoderDomain _ _ accepted
  all_goals try simp_all

/-- Whole reviewed copyProp preserves success of the real partial decoder. -/
theorem copyProp_decoderDomain {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width))
    (accepted : (wordLangProgFromHOL program).isSome = true) :
    (wordLangProgFromHOL (copyProp program)).isSome = true := by
  rw [decoderDomain_eq] at accepted ⊢
  exact copyPropProg_decoderDomain program emptyEq accepted

end Flapjack.Compiler.Backend.WordCopy
