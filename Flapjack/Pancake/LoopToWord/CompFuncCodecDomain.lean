import Flapjack.Pancake.LoopToWord.CompFuncProductionRoute
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.Domain

namespace Flapjack
open WordProgCarrierCodec

/-- The compatibility compiler never emits the separate five-register
AddCarry extension. Full source syntax, context and labels are arbitrary.
This is Flapjack codec infrastructure, not a HOL semantics theorem. -/
theorem supportsCodec_loopToWordProgWithLabels {α : Type u} [OfNat α 1]
    (context : WordContext) (labels : Nat × Nat) (body : LoopProg α) :
    supportsCodec (loopToWordProgWithLabels context labels body).1 = true := by
  fun_induction loopToWordProgWithLabels context labels body
  all_goals simp_all [supportsCodec]
  case case8 =>
    cases ‹LoopProg α› <;> simp_all [loopToWordAtom, supportsCodec]
    all_goals try (cases ‹LoopArith› <;> simp [wordArith, supportsCodec])
    all_goals repeat' (split <;> simp_all [supportsCodec])

/-- Every compatibility function body is accepted by the real Word codec,
without a source-encoding or successful-compilation premise. Flapjack carrier
infrastructure; it does not prove compiler semantics or native limit wiring. -/
theorem wordLangProgToHOL_loopToWordCompFunc_isSome
    {width : Nat} [NeZero width] (name : Nat) (parameters : List Nat)
    (body : LoopProg (BitVec width)) :
    (wordLangProgToHOL (LoopToWord.loopToWordCompFunc name parameters body)).isSome = true := by
  rw [codecDomain]
  exact supportsCodec_loopToWordProgWithLabels _ _ body

/-- Every actual routed function output is accepted by the native Word codec.
The exact path uses the decoder's proved inverse; the compatibility path uses
the full constructor proof above. No source-encoding, byte-name or successful
target-compilation premise is required. This is Flapjack carrier closure, not
a HOL semantics theorem or a claim that native limit is already wired. -/
theorem wordLangProgToHOL_loopToWordCompFuncRouted_isSome
    {width : Nat} [NeZero width] (name : Nat) (parameters : List Nat)
    (body : LoopProg (BitVec width)) :
    (wordLangProgToHOL (loopToWordCompFuncRouted name parameters body)).isSome = true := by
  unfold loopToWordCompFuncRouted
  cases routed : loopToWordCompFuncViaHOL name parameters body with
  | none => exact wordLangProgToHOL_loopToWordCompFunc_isSome name parameters body
  | some output =>
      unfold loopToWordCompFuncViaHOL at routed
      split at routed
      · cases source : executableLoopProgToHol body with
        | none => simp [source] at routed
        | some exactBody =>
            simp only [source] at routed
            have encoded := wordLangProgToHOL_of_fromHOL _ output routed
            simp only [encoded, Option.isSome_some]
      · simp at routed

end Flapjack
