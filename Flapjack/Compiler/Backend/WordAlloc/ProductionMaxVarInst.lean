import Flapjack.RiscV.Allocator
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
import Flapjack.Pancake.WordLang.MaxVarInst

namespace Flapjack.RiscV

private theorem max3Corresponds (a b c : Nat) :
    max a (max b c) = max3HOL a b c := by
  unfold max3HOL
  split <;> split <;> omega

/-- The accepted arithmetic codec preserves the actual production maximum.
The separate five-register AddCarry has no HOL instruction encoding and remains
rejected. This carrier correspondence is Flapjack infrastructure, not a HOL port. -/
theorem wordArithCakeMaxVar_corresponds {width : Nat} [NeZero width]
    (operation : WordArith (BitVec width)) (native : WordLangArith (BitVec width))
    (encoded : wordLangArithToHOL operation = some native) :
    wordArithCakeMaxVar operation = maxVarInstHOL (.arith native) := by
  cases operation <;> simp only [wordLangArithToHOL, Option.some.injEq] at encoded
  all_goals try contradiction
  all_goals subst native
  all_goals simp only [wordArithCakeMaxVar, maxVarInstHOL]
  all_goals try rw [← max3Corresponds]
  all_goals try omega
  all_goals split
  all_goals dsimp only
  all_goals try rw [← max3Corresponds]
  all_goals omega

/-- Accepted instruction encoding preserves the executed maximum, including
both production zero-offset memory forms and arbitrary explicit offsets. The
only premise is the real partial codec equation; no evaluation, well-formedness,
or assumed maximum relation is required. Flapjack infrastructure with no HOL
original, supplying a prerequisite for the separate native program-limit route. -/
theorem wordInstCakeMaxVar_corresponds {width : Nat} [NeZero width]
    (instruction : WordInst (BitVec width)) (native : WordLangInst (BitVec width))
    (encoded : wordLangInstToHOL instruction = some native) :
    wordInstCakeMaxVar instruction = maxVarInstHOL native := by
  cases instruction with
  | const destination value =>
      simp only [wordLangInstToHOL, Option.some.injEq] at encoded
      subst native
      rfl
  | arith operation =>
      cases h : wordLangArithToHOL operation with
      | none => simp [wordLangInstToHOL, h] at encoded
      | some result =>
          simp only [wordLangInstToHOL, h, Option.map_some, Option.some.injEq] at encoded
          subst native
          exact wordArithCakeMaxVar_corresponds operation result h
  | mem op destination address =>
      simp only [wordLangInstToHOL, Option.some.injEq] at encoded
      subst native
      cases op <;> simp [wordInstCakeMaxVar, maxVarInstHOL, Nat.max_comm]
  | memOffset op destination address offset =>
      simp only [wordLangInstToHOL, Option.some.injEq] at encoded
      subst native
      cases op <;> simp [wordInstCakeMaxVar, maxVarInstHOL, Nat.max_comm]

end Flapjack.RiscV
