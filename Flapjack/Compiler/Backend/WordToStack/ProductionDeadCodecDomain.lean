import Flapjack.RiscV.WordDeadCode
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip

namespace Flapjack
open RiscV

/-- Private structural view of the actual partial codec's domain. The theorem
below proves equality with the real encoder for every program. This is not an
alternate evaluator or a caller assumption. Flapjack-only infrastructure;
there is no HOL declaration for this production carrier predicate. -/
private def supportsCodec {α : Type u} : WordProg α → Bool
  | .inst (.arith (.addCarry _ _ _ _ _)) => false
  | .seq first second | .ite _ _ _ first second => supportsCodec first && supportsCodec second
  | .loop _ body _ | .mustTerminate body => supportsCodec body
  | .call returns _ _ handler =>
      (match returns with
       | none => true
       | some (_, _, body, _, _) => supportsCodec body) &&
      (match handler with
       | none => true
       | some (_, body, _, _) => supportsCodec body)
  | _ => true
termination_by program => sizeOf program

/-- Flapjack-only Option-domain packaging, with no separate HOL original. -/
private theorem optionPairDomain {α β γ : Type} (first : Option α)
    (second : Option β) (make : α → β → γ) :
    (first.bind fun a => second.bind fun b => some (make a b)).isSome =
      (first.isSome && second.isSome) := by
  cases first <;> cases second <;> rfl

/-- Flapjack-only single-payload Option-domain packaging. -/
private theorem optionMapDomain {α β : Type} (value : Option α) (make : α → β) :
    (value.bind fun a => some (make a)).isSome = value.isSome := by
  cases value <;> rfl

/-- Instruction-domain equality on every production constructor. Ordinary
16-bit memory is codec-accepted; only the distinct five-register arithmetic
primitive is rejected here. Flapjack-only codec infrastructure. -/
private theorem instructionDomain {width : Nat} (instruction : WordInst (BitVec width)) :
    (wordLangInstToHOL instruction).isSome = supportsCodec (.inst instruction) := by
  cases instruction with
  | const destination value => simp [wordLangInstToHOL, supportsCodec]
  | arith operation => cases operation <;> simp [wordLangInstToHOL, wordLangArithToHOL, supportsCodec]
  | mem operation destination address => simp [wordLangInstToHOL, supportsCodec]
  | memOffset operation destination address offset => simp [wordLangInstToHOL, supportsCodec]

/-- Full proved equality with the actual encoder, including both optional
Call continuations. This is Flapjack-only carrier correspondence. -/
private theorem codecDomain {width : Nat} (program : WordProg (BitVec width)) :
    (wordLangProgToHOL program).isSome = supportsCodec program := by
  -- The total colouring recursion supplies complete constructor induction,
  -- including both Call bodies; the colour values play no role here.
  fun_induction wordApplyColour (fun name => name) program <;>
    simp_all [wordLangProgToHOL, supportsCodec, instructionDomain,
      optionPairDomain, optionMapDomain]

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
