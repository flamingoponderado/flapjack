import Flapjack.Compiler.Backend.StackProps.EvaluateNeutral

namespace Flapjack.Test.StackEvaluateClockNeutralParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackProps.EvaluateNeutral

example {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (clock : Nat)
    (hypothesis : evaluate (program, source) = (result, post) ∧ clockNeutralHOL program) :
    evaluate (program, {source with clock := clock}) = (result, {post with clock := clock}) :=
  evaluateClockNeutral program source post result clock hypothesis

example {C F : Type}
    (source post : StackSemStateFiniteExact 1 C F)
    (result : Option (StackSemResult 1))
    (execution : evaluate ((.seq (.seq .skip (.inst .skip)) (.halt 0) : HolProg 1), source) = (result, post)) :
    evaluate ((.seq (.seq .skip (.inst .skip)) (.halt 0) : HolProg 1), {source with clock := 0}) =
      (result, {post with clock := 0}) :=
  evaluateClockNeutral _ source post result 0 ⟨execution, by simp [clockNeutralHOL]⟩

example {C F : Type}
    (source post : StackSemStateFiniteExact 8 C F)
    (result : Option (StackSemResult 8))
    (execution : evaluate ((.seq (.seq .skip (.inst .skip)) (.halt 0) : HolProg 8), source) = (result, post)) :
    evaluate ((.seq (.seq .skip (.inst .skip)) (.halt 0) : HolProg 8), {source with clock := 17}) =
      (result, {post with clock := 17}) :=
  evaluateClockNeutral _ source post result 17 ⟨execution, by simp [clockNeutralHOL]⟩

example {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F)
    (result : Option (StackSemResult 64))
    (execution : evaluate ((.seq (.seq .skip (.inst .skip)) (.halt 0) : HolProg 64), source) = (result, post)) :
    evaluate ((.seq (.seq .skip (.inst .skip)) (.halt 0) : HolProg 64), {source with clock := 0}) =
      (result, {post with clock := 0}) :=
  evaluateClockNeutral _ source post result 0 ⟨execution, by simp [clockNeutralHOL]⟩

example {C F : Type}
    (source post : StackSemStateFiniteExact 80 C F)
    (result : Option (StackSemResult 80))
    (execution : evaluate ((.seq (.seq .skip (.inst .skip)) (.halt 0) : HolProg 80), source) = (result, post)) :
    evaluate ((.seq (.seq .skip (.inst .skip)) (.halt 0) : HolProg 80), {source with clock := 123456789}) =
      (result, {post with clock := 123456789}) :=
  evaluateClockNeutral _ source post result 123456789 ⟨execution, by simp [clockNeutralHOL]⟩

-- Original neutral_clock_skip=T
example : clockNeutralHOL (.skip : HolProg 64) := by simp [clockNeutralHOL]

-- Original neutral_clock_halt=T
example : clockNeutralHOL (.halt 0 : HolProg 64) := by simp [clockNeutralHOL]

-- Original neutral_clock_inst=T
example : clockNeutralHOL (.inst .skip : HolProg 64) := by simp [clockNeutralHOL]

-- Original neutral_clock_seq=T
example : clockNeutralHOL (.seq .skip (.halt 0) : HolProg 64) := by simp [clockNeutralHOL]

-- Original neutral_clock_nested=T
example : clockNeutralHOL (.seq (.seq .skip (.inst .skip)) (.halt 0) : HolProg 64) := by simp [clockNeutralHOL]

-- Original neutral_clock_tick=F
example : ¬clockNeutralHOL (.tick : HolProg 64) := by simp [clockNeutralHOL]

-- Original neutral_clock_loop=F
example : ¬clockNeutralHOL (.loop .skip : HolProg 64) := by simp [clockNeutralHOL]

end Flapjack.Test.StackEvaluateClockNeutralParity
