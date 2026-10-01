import Flapjack.RiscV.WordDeadCode
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.Domain

namespace Flapjack
open WordProgCarrierCodec
open RiscV

/-- Flapjack-only closure for the actual production deletion primitive. -/
private theorem deadInstructionDomain {width : Nat} (live : List Nat)
    (instruction : WordInst (BitVec width))
    (accepted : supportsCodec (.inst instruction) = true) :
    supportsCodec (wordDeadInst live instruction).1 = true := by
  unfold wordDeadInst
  split <;> simp_all [supportsCodec]

/-- Flapjack-only move deletion cannot introduce an unsupported constructor. -/
private theorem deadMoveDomain {width : Nat} (priority : Nat)
    (live : List Nat) (moves : List (Nat × Nat)) :
    supportsCodec (wordDeadMove (α := BitVec width) priority live moves).1 = true := by
  unfold wordDeadMove
  dsimp only
  split <;> simp [supportsCodec]

/-- Full production three-component dead-code pass closure, with arbitrary
backward state. Untagged Flapjack carrier infrastructure, no HOL original. -/
private theorem deadDomain {width : Nat} (program : WordProg (BitVec width))
    (live : List Nat) (frames : List (List Nat × List Nat))
    (returnLabels nlive : List Nat)
    (accepted : supportsCodec program = true) :
    supportsCodec (wordDeadCodeWithStores program live frames returnLabels nlive).1 = true := by
  fun_induction wordApplyColour (fun name => name) program generalizing live frames returnLabels nlive <;>
    simp_all [wordDeadCodeWithStores, supportsCodec, wordDeadCodeAuxWithLabels,
      deadInstructionDomain, deadMoveDomain]
  case case7 =>
    cases ‹WordExp (BitVec width)› <;> simp_all [supportsCodec]
    split <;> simp_all [supportsCodec]
  all_goals repeat' (split <;> simp_all [supportsCodec])

/-- Full actual three-component production deletion preserves native codec
acceptance for arbitrary live variables, loop frames, return labels and global
backward-store state. Flapjack-only carrier infrastructure, no HOL original. -/
theorem wordLangProgToHOL_wordDeadCodeWithStores_isSome {width : Nat}
    (program : WordProg (BitVec width)) (live : List Nat)
    (frames : List (List Nat × List Nat)) (returnLabels nlive : List Nat)
    (accepted : (wordLangProgToHOL program).isSome = true) :
    (wordLangProgToHOL (wordDeadCodeWithStores program live frames returnLabels nlive).1).isSome = true := by
  rw [codecDomain] at accepted ⊢
  exact deadDomain program live frames returnLabels nlive accepted

/-- Actual executed dead-program elimination preserves native codec acceptance.
Deletion can turn a rejected input into an accepted output, so this is the
required one-way closure. No output-codec, memory-guard or pass-success premise
is assumed. Flapjack-only production carrier infrastructure, not a HOL port. -/
theorem wordLangProgToHOL_wordRemoveDeadProgram_isSome {width : Nat}
    (program : WordProg (BitVec width))
    (accepted : (wordLangProgToHOL program).isSome = true) :
    (wordLangProgToHOL (wordRemoveDeadProgram program)).isSome = true := by
  rw [codecDomain] at accepted ⊢
  exact deadDomain program [] [] (wordDeadReturnLabels program) [] accepted

end Flapjack
