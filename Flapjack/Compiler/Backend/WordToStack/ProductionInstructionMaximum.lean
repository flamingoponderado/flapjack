import Flapjack.RiscV.Allocator
import Flapjack.RiscV.AllocatorMemoryInvariant
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
import Flapjack.Pancake.WordLang.MaxVarInst

namespace Flapjack

/-- Flapjack-only normalization of the reviewed branch-based three-way
maximum to production's nested maximum. No HOL declaration is ported here. -/
private theorem max3_eq_max (a b c : Nat) : max3HOL a b c = max a (max b c) := by
  unfold max3HOL
  split <;> split <;> omega

/-- Full arithmetic maximum correspondence through the actual partial codec.
When the codec rejects the distinct five-register AddCarry, both mapped
expressions are none; no maximum correspondence is asserted for that case. No conversion
success or desired-maximum premise is assumed. This is Flapjack carrier
infrastructure, not a HOL theorem port. -/
theorem wordArithCakeMaxVar_codec {width : Nat} [NeZero width]
    (operation : WordArith (BitVec width)) :
    (wordLangArithToHOL operation).map (fun native => maxVarInstHOL (.arith native)) =
      (wordLangArithToHOL operation).map (fun _ => wordArithCakeMaxVar operation) := by
  cases operation <;>
    simp [wordLangArithToHOL, wordArithCakeMaxVar, maxVarInstHOL,
      max3_eq_max, Nat.max_assoc]
  all_goals cases ‹WordRegImm (BitVec width)› <;> dsimp only [maxVarInstHOL]
  all_goals first | rfl | rw [max3_eq_max] | rw [Nat.max_zero]

/-- Instruction maxima agree through the existing operand-preserving codec
under the allocator's actual checked memory guard. The guard excludes ordinary
Load16/Store16, which HOL's max_var_inst catch-all ignores; it is not a caller
assumption about the desired maximum. Every arithmetic codec rejection remains
explicit. Flapjack-only carrier correspondence; full program codec closure and
the native frame/production route remain separate obligations. -/
theorem wordInstCakeMaxVar_codec {width : Nat} [NeZero width]
    (instruction : WordInst (BitVec width))
    (supported : RiscV.allocatorMemorySupported (.inst instruction) = true) :
    (wordLangInstToHOL instruction).map maxVarInstHOL =
      (wordLangInstToHOL instruction).map (fun _ => wordInstCakeMaxVar instruction) := by
  cases instruction with
  | const destination value => rfl
  | arith operation =>
      simpa only [wordLangInstToHOL, Option.map_map, Function.comp_def,
        wordInstCakeMaxVar] using wordArithCakeMaxVar_codec operation
  | mem operation destination address =>
      cases operation <;>
        simp_all [RiscV.allocatorMemorySupported, wordLangInstToHOL,
          wordInstCakeMaxVar, maxVarInstHOL, Nat.max_comm]
  | memOffset operation destination address offset =>
      cases operation <;>
        simp_all [RiscV.allocatorMemorySupported, wordLangInstToHOL,
          wordInstCakeMaxVar, maxVarInstHOL, Nat.max_comm]

end Flapjack
