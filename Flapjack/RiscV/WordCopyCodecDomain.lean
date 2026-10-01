import Flapjack.RiscV.WordCopyProp
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.Domain

namespace Flapjack.RiscV
open WordProgCarrierCodec

/-- Flapjack carrier-domain infrastructure for the actual copy instruction
rewriter. It preserves encoder acceptance, including rejection of the separate
five-register AddCarry. This has no HOL original and is not semantic correctness. -/
theorem wordCopyInst_codecDomain {width : Nat} (state : WordCopyState)
    (instruction : WordInst (BitVec width)) :
    (wordLangInstToHOL (wordCopyInst state instruction).1).isSome =
      (wordLangInstToHOL instruction).isSome := by
  cases instruction with
  | arith operation =>
      cases operation <;>
        simp [wordCopyInst, wordLangInstToHOL, wordLangArithToHOL]
  | const destination value => rfl
  | mem operator destination address =>
      cases operator <;> rfl
  | memOffset operator destination address offset =>
      cases operator <;> rfl

/-- Flapjack carrier-domain infrastructure over the executed copy pass, with
arbitrary input state. Calls retain both original continuations. No successful
encoding or source/target evaluation premise is assumed; no HOL port is claimed. -/
theorem wordCopyProg_codecDomain {width : Nat} [WordCseHash (BitVec width)]
    (state : WordCopyState) (program : WordProg (BitVec width)) :
    (wordLangProgToHOL (wordCopyProg state program).1).isSome =
      (wordLangProgToHOL program).isSome := by
  induction state, program using wordCopyProg.induct <;>
    simp_all [wordCopyProg, wordLangProgToHOL,
      Option.isSome_map, optionMapDomain, optionPairDomain]
  all_goals try (split <;> simp_all [wordLangProgToHOL])
  rename_i initial original rewritten final h
  have preserved := wordCopyInst_codecDomain initial original
  simpa only [h] using preserved

/-- Public executed copy propagation preserves the exact carrier encoder's
domain. This is untagged Flapjack infrastructure, not a pass simulation. -/
theorem wordCopyProp_codecDomain {width : Nat} [WordCseHash (BitVec width)]
    (program : WordProg (BitVec width)) :
    (wordLangProgToHOL (wordCopyProp program)).isSome =
      (wordLangProgToHOL program).isSome :=
  wordCopyProg_codecDomain wordCopyEmpty program

end Flapjack.RiscV
