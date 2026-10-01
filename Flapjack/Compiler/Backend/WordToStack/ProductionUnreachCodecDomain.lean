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

/-- Actual sequence pruning/merge closure. Both input domains are established
independently, and unreachable tails may be discarded. Flapjack-only helper. -/
private theorem sequenceDomain {width : Nat} (first second : WordProg (BitVec width))
    (left : supportsCodec first = true) (right : supportsCodec second = true) :
    supportsCodec (wordCopyUnreachSeq first second) = true := by
  unfold wordCopyUnreachSeq
  repeat' (split <;> simp_all [supportsCodec])

/-- Actual fold closure on accepted pieces. Flapjack-only carrier helper. -/
private theorem foldDomain {width : Nat} (pieces : List (WordProg (BitVec width)))
    (accepted : ∀ piece ∈ pieces, supportsCodec piece = true) :
    supportsCodec (pieces.foldr wordCopyUnreachSeq .skip) = true := by
  induction pieces with
  | nil => simp [supportsCodec]
  | cons first rest ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at accepted
    exact sequenceDomain first _ accepted.1 (ih accepted.2)

/-- Full actual suffix-accumulator flattening closure, including both returning
Call bodies and an unchanged nonreturning handler. Flapjack-only helper. -/
private theorem partsDomain {width : Nat} (program : WordProg (BitVec width))
    (suffix : List (WordProg (BitVec width)))
    (accepted : supportsCodec program = true)
    (suffixAccepted : ∀ piece ∈ suffix, supportsCodec piece = true) :
    ∀ piece ∈ wordCopyUnreachPartsAcc program suffix, supportsCodec piece = true := by
  fun_induction wordApplyColour (fun name => name) program generalizing suffix <;>
    simp_all [wordCopyUnreachPartsAcc, supportsCodec]
  case case8 => solve_by_elim
  all_goals try constructor
  all_goals apply foldDomain
  all_goals apply_assumption
  all_goals simp

/-- Actual executed post-copy unreachable elimination preserves native codec
acceptance. Unreachable rejected primitives can disappear, so the result is
one-way. No normal-form, output-codec, memory-guard, termination or successful-
pass premise is assumed. Flapjack-only infrastructure, not a HOL theorem port. -/
theorem wordLangProgToHOL_wordRemoveUnreachableAfterCopy_isSome {width : Nat}
    (program : WordProg (BitVec width))
    (accepted : (wordLangProgToHOL program).isSome = true) :
    (wordLangProgToHOL (wordRemoveUnreachableAfterCopy program)).isSome = true := by
  rw [codecDomain] at accepted ⊢
  apply foldDomain
  exact partsDomain program [] accepted (by simp)

end Flapjack
