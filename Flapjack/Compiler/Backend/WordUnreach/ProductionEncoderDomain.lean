import Flapjack.Compiler.Backend.WordUnreach.ProductionDecoderDomain
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.Domain

/-! Flapjack-only codec infrastructure for routing the executed unreach pass.
The decoder-closure theorem requires a decoder-accepted native input. This
module derives that fact from the actual production encoder, without assuming
output success or a carrier roundtrip. No HOL theorem declares these codecs. -/
namespace Flapjack.Compiler.Backend.WordUnreach
open Flapjack WordProgCarrierCodec

/-- Every accepted production instruction encodes a supported native
instruction. Legacy five-register AddCarry remains rejected; zero-offset
memory normalization does not affect decoder acceptance. -/
private theorem instructionImage {width : Nat}
    (instruction : WordInst (BitVec width)) (native : WordLangInst (BitVec width))
    (encoded : wordLangInstToHOL instruction = some native) :
    (wordLangInstFromHOL native).isSome = true := by
  cases instruction with
  | const destination value =>
    simp only [wordLangInstToHOL, Option.some.injEq] at encoded
    subst native
    rfl
  | arith operation =>
    cases operation <;> simp only [wordLangInstToHOL, wordLangArithToHOL,
      Option.map_some, Option.map_none, Option.some.injEq, reduceCtorEq] at encoded
    all_goals try subst native
    all_goals rfl
  | mem operation destination address =>
    simp only [wordLangInstToHOL, Option.some.injEq] at encoded
    subst native
    simp [wordLangInstFromHOL]
  | memOffset operation destination address offset =>
    simp only [wordLangInstToHOL, Option.some.injEq] at encoded
    subst native
    simp only [wordLangInstFromHOL]
    split <;> rfl

/-- Actual encoder output is in the native decoder domain for every production
constructor and both optional Call continuations. The sole hypothesis is the
actual encoder equation; no output decoding premise is assumed. -/
theorem encoderImage_decoderDomain {width : Nat}
    (production : WordProg (BitVec width)) :
    ∀ native, wordLangProgToHOL production = some native → decoderDomain native = true := by
  fun_induction wordApplyColour (fun name => name) production
  all_goals intro native encoded
  all_goals simp [wordLangProgToHOL, Option.map_eq_some_iff,
    Option.bind_eq_some_iff] at encoded
  all_goals repeat' rcases encoded with ⟨component, run, encoded⟩
  all_goals try subst native
  all_goals simp_all [decoderDomain]
  all_goals exact instructionImage _ _ (by assumption)

/-- Full input acceptance required by native removeUnreach decoder closure. -/
theorem wordLangProgFromHOL_of_toHOL_isSome {width : Nat}
    (production : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL production = some native) :
    (wordLangProgFromHOL native).isSome = true := by
  rw [decoderDomain_eq]
  exact encoderImage_decoderDomain production native encoded

/-- The actual encode/native-remove/decode boundary has no new decoder failure
on an accepted production input. This proves the missing codec obligation,
not a program simulation or that the production caller is already routed. -/
theorem removeUnreach_of_toHOL_decoder_isSome {width : Nat} [NeZero width]
    (production : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL production = some native) :
    (wordLangProgFromHOL (removeUnreach native)).isSome = true :=
  removeUnreach_decoder_isSome native (wordLangProgFromHOL_of_toHOL_isSome production native encoded)

end Flapjack.Compiler.Backend.WordUnreach
