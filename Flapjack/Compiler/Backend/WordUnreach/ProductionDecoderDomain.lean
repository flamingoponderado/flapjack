import Flapjack.Compiler.Backend.WordUnreach
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec

/-! Flapjack-only representation infrastructure for the executed Word decoder.
The native unreachable-code pass retains instruction leaves, so it cannot
introduce an unsupported instruction into a decoder-accepted program. These
are codec-domain facts, not HOL pass-correctness ports or evaluation premises.
-/

namespace Flapjack.Compiler.Backend.WordUnreach

open Flapjack

/-- Structural view of the actual decoder, including both optional Call bodies.
The equality below ties this predicate to the real partial decoder. -/
def decoderDomain {width : Nat} : WordLangProgHOL (BitVec width) → Bool
  | .inst instruction => (wordLangInstFromHOL instruction).isSome
  | .seq first second | .ite _ _ _ first second =>
      decoderDomain first && decoderDomain second
  | .loop _ body _ | .mustTerminate body => decoderDomain body
  | .call returns _ _ handler =>
      (match returns with
        | none => true
        | some (_, _, body, _, _) => decoderDomain body) &&
      (match handler with
        | none => true
        | some (_, body, _, _) => decoderDomain body)
  | _ => true
termination_by program => sizeOf program

private theorem pairDomain {α β γ : Type} (first : Option α)
    (second : Option β) (make : α → β → γ) :
    (first.bind fun a => second.bind fun b => some (make a b)).isSome =
      (first.isSome && second.isSome) := by
  cases first <;> cases second <;> rfl

private theorem mapDomain {α β : Type} (value : Option α) (make : α → β) :
    (value.bind fun a => some (make a)).isSome = value.isSome := by
  cases value <;> rfl

/-- Every constructor's structural domain equals actual decoder acceptance.
There is no assumed output relation or successful compilation premise. -/
theorem decoderDomain_eq {width : Nat} (program : WordLangProgHOL (BitVec width)) :
    (wordLangProgFromHOL program).isSome = decoderDomain program := by
  fun_induction decoderDomain program <;>
    try simp_all [wordLangProgFromHOL, pairDomain, mapDomain]
  case case6 returns target arguments handler ihReturns ihHandler =>
    rcases returns with _ | ⟨values, sets, body, firstLabel, secondLabel⟩ <;>
      rcases handler with _ | ⟨exception, handlerBody, handlerFirst, handlerSecond⟩ <;>
      simp_all [wordLangProgFromHOL, pairDomain, mapDomain]
  case case7 program h1 h2 h3 h4 h5 h6 =>
    cases program <;> try rfl
    case inst instruction => exact (h1 instruction rfl).elim
    case seq first second => exact (h2 first second rfl).elim
    case ite operator condition right first second =>
      exact (h3 operator condition right first second rfl).elim
    case loop liveIn body liveOut => exact (h4 liveIn body liveOut rfl).elim
    case mustTerminate body => exact (h5 body rfl).elim
    case call returns target arguments handler =>
      exact (h6 returns target arguments handler rfl).elim

/-- Native sequence simplification preserves the actual decoder domain;
discarding an unreachable continuation does not invent an instruction. -/
theorem simpSeq_decoderDomain {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width))
    (left : decoderDomain first = true) (right : decoderDomain second = true) :
    decoderDomain (simpSeq first second) = true := by
  unfold simpSeq
  split
  · exact left
  · cases first <;> try simp_all [decoderDomain]
    case move priority moves =>
      cases second <;> try simp_all [destSeqMove, decoderDomain]
      case seq head tail =>
        cases head <;> try simp_all [decoderDomain]
        split <;> simp_all [decoderDomain]

/-- Right association and unreachable pruning preserve decodability for the
full native program and arbitrary decodable accumulator, including both Call
continuations. This is representation closure, not an evaluator simulation. -/
theorem seqAssocRight_decoderDomain {width : Nat} [NeZero width]
    (program acc : WordLangProgHOL (BitVec width))
    (accepted : decoderDomain program = true) (accAccepted : decoderDomain acc = true) :
    decoderDomain (seqAssocRight program acc) = true := by
  fun_induction seqAssocRight program acc
  case case1 => exact accAccepted
  case case2 first second acc ihSecond ihFirst =>
    simp only [decoderDomain, Bool.and_eq_true] at accepted
    exact ihFirst accepted.1 (ihSecond accepted.2 accAccepted)
  case case3 operator condition right first second acc ihFirst ihSecond =>
    apply simpSeq_decoderDomain _ _ _ accAccepted
    simp only [decoderDomain, Bool.and_eq_true] at accepted ⊢
    exact ⟨ihFirst accepted.1 (by simp [decoderDomain]),
      ihSecond accepted.2 (by simp [decoderDomain])⟩
  case case4 body acc ih =>
    apply simpSeq_decoderDomain _ _ _ accAccepted
    simp only [decoderDomain] at accepted ⊢
    exact ih accepted (by simp [decoderDomain])
  case case5 => exact accepted
  case case6 target arguments handler acc values sets body firstLabel secondLabel ihBody ihHandler =>
    apply simpSeq_decoderDomain _ _ _ accAccepted
    rcases handler with _ | ⟨exception, handlerBody, handlerFirst, handlerSecond⟩ <;>
      simp_all [decoderDomain]
  case case7 liveIn body liveOut acc ih =>
    apply simpSeq_decoderDomain _ _ _ accAccepted
    simp only [decoderDomain] at accepted ⊢
    exact ih accepted (by simp [decoderDomain])
  case case8 => exact simpSeq_decoderDomain _ _ accepted accAccepted

/-- Every decoder-accepted native input remains accepted after the reviewed
native unreachable-code pass. Only the input representation domain is assumed;
the output decoder success is proved. No HOL theorem is claimed by this codec
fact, and rejected instructions are not silently substituted. -/
theorem removeUnreach_decoder_isSome {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width))
    (accepted : (wordLangProgFromHOL program).isSome = true) :
    (wordLangProgFromHOL (removeUnreach program)).isSome = true := by
  rw [decoderDomain_eq] at accepted ⊢
  exact seqAssocRight_decoderDomain program .skip accepted (by simp [decoderDomain])

end Flapjack.Compiler.Backend.WordUnreach
