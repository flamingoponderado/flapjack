import Flapjack.Compiler.Backend.WordUnreach.ProductionDecoderDomain
import Flapjack.RiscV.AllocatorMemoryInvariant
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.Domain

/-! Flapjack-only allocator-domain infrastructure for routing the executed
unreachable-code pass. The native pass retains instruction leaves, so it cannot
introduce an instruction the executed allocator rejects. These are codec and
runtime-domain facts, not HOL pass-correctness ports or evaluation premises. -/

namespace Flapjack.Compiler.Backend.WordUnreach

open Flapjack

/-- Structural view of executed allocator support on the native carrier: a leaf
instruction is checked through the actual decoder, and every nested program,
including both optional Call bodies, is traversed. -/
def memDomain {width : Nat} : WordLangProgHOL (BitVec width) → Bool
  | .inst instruction =>
      match wordLangInstFromHOL instruction with
      | some decoded => RiscV.allocatorMemorySupported (WordProg.inst decoded)
      | none => true
  | .seq first second | .ite _ _ _ first second => memDomain first && memDomain second
  | .loop _ body _ | .mustTerminate body => memDomain body
  | .call returns _ _ handler =>
      (match returns with
        | none => true
        | some (_, _, body, _, _) => memDomain body) &&
      (match handler with
        | none => true
        | some (_, body, _, _) => memDomain body)
  | _ => true
termination_by program => sizeOf program

/-- Every decoded program's executed allocator support is the structural
domain of its native source. No allocation success is assumed. -/
theorem memDomain_decode {width : Nat} (program : WordLangProgHOL (BitVec width)) :
    ∀ decoded, wordLangProgFromHOL program = some decoded →
      RiscV.allocatorMemorySupported decoded = memDomain program := by
  fun_induction memDomain program
  case case1 instruction inner hinner =>
    intro decoded h
    simp only [wordLangProgFromHOL, hinner, Option.map_some, Option.some.injEq] at h
    subst h
    rfl
  case case2 instruction hinner =>
    intro decoded h
    simp [wordLangProgFromHOL, hinner] at h
  case case3 first second ihFirst ihSecond =>
    intro decoded h
    cases ha : wordLangProgFromHOL first with
    | none => simp [wordLangProgFromHOL, ha] at h
    | some a =>
      cases hb : wordLangProgFromHOL second with
      | none => simp [wordLangProgFromHOL, ha, hb] at h
      | some b =>
        simp [wordLangProgFromHOL, ha, hb] at h
        subst h
        simp [RiscV.allocatorMemorySupported, ihFirst a ha, ihSecond b hb]
  case case4 operator condition right first second ihFirst ihSecond =>
    intro decoded h
    cases ha : wordLangProgFromHOL first with
    | none => simp [wordLangProgFromHOL, ha] at h
    | some a =>
      cases hb : wordLangProgFromHOL second with
      | none => simp [wordLangProgFromHOL, ha, hb] at h
      | some b =>
        simp [wordLangProgFromHOL, ha, hb] at h
        subst h
        simp [RiscV.allocatorMemorySupported, ihFirst a ha, ihSecond b hb]
  case case5 liveIn body liveOut ih =>
    intro decoded h
    cases ha : wordLangProgFromHOL body with
    | none => simp [wordLangProgFromHOL, ha] at h
    | some a =>
      simp [wordLangProgFromHOL, ha] at h
      subst h
      simp [RiscV.allocatorMemorySupported, ih a ha]
  case case6 body ih =>
    intro decoded h
    cases ha : wordLangProgFromHOL body with
    | none => simp [wordLangProgFromHOL, ha] at h
    | some a =>
      simp [wordLangProgFromHOL, ha] at h
      subst h
      simp [RiscV.allocatorMemorySupported, ih a ha]
  case case7 returns target arguments handler ihReturns ihHandler =>
    intro decoded h
    rcases returns with _ | ⟨values, sets, body, firstLabel, secondLabel⟩ <;>
      rcases handler with _ | ⟨exception, handlerBody, handlerFirst, handlerSecond⟩
    · simp [wordLangProgFromHOL] at h
      subst h
      simp [RiscV.allocatorMemorySupported]
    · cases hh : wordLangProgFromHOL handlerBody with
      | none => simp [wordLangProgFromHOL, hh] at h
      | some hb =>
        simp [wordLangProgFromHOL, hh] at h
        subst h
        simp [RiscV.allocatorMemorySupported, ihHandler hb hh]
    · cases hr : wordLangProgFromHOL body with
      | none => simp [wordLangProgFromHOL, hr] at h
      | some rb =>
        simp [wordLangProgFromHOL, hr] at h
        subst h
        simp [RiscV.allocatorMemorySupported, ihReturns rb hr]
    · cases hr : wordLangProgFromHOL body with
      | none => simp [wordLangProgFromHOL, hr] at h
      | some rb =>
        cases hh : wordLangProgFromHOL handlerBody with
        | none => simp [wordLangProgFromHOL, hr, hh] at h
        | some hb =>
          simp [wordLangProgFromHOL, hr, hh] at h
          subst h
          simp [RiscV.allocatorMemorySupported,
            ihReturns rb hr,
            ihHandler hb hh]
  case case8 program notInst notSeq notIte notLoop notMust notCall =>
    intro decoded h
    cases program
    case inst instruction => exact (notInst instruction rfl).elim
    case seq first second => exact (notSeq first second rfl).elim
    case ite operator condition right first second =>
      exact (notIte operator condition right first second rfl).elim
    case loop liveIn body liveOut => exact (notLoop liveIn body liveOut rfl).elim
    case mustTerminate body => exact (notMust body rfl).elim
    case call returns target arguments handler =>
      exact (notCall returns target arguments handler rfl).elim
    all_goals simp only [wordLangProgFromHOL, Option.some.injEq] at h
    all_goals subst h
    all_goals simp [RiscV.allocatorMemorySupported]

/-- Native sequence simplification preserves the allocator domain; discarding
an unreachable continuation does not invent an instruction. -/
theorem simpSeq_memDomain {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width))
    (left : memDomain first = true) (right : memDomain second = true) :
    memDomain (simpSeq first second) = true := by
  unfold simpSeq
  split
  · exact left
  · cases first <;> try simp_all [memDomain]
    case move priority moves =>
      cases second <;> try simp_all [destSeqMove, memDomain]
      case seq head tail =>
        cases head <;> try simp_all [memDomain]
        split <;> simp_all [memDomain]

/-- Right association and unreachable pruning preserve the allocator domain for
the full native program and an arbitrary in-domain accumulator, including both
Call continuations. Representation closure, not an evaluator simulation. -/
theorem seqAssocRight_memDomain {width : Nat} [NeZero width]
    (program acc : WordLangProgHOL (BitVec width))
    (accepted : memDomain program = true) (accAccepted : memDomain acc = true) :
    memDomain (seqAssocRight program acc) = true := by
  fun_induction seqAssocRight program acc
  case case1 => exact accAccepted
  case case2 first second acc ihSecond ihFirst =>
    simp only [memDomain, Bool.and_eq_true] at accepted
    exact ihFirst accepted.1 (ihSecond accepted.2 accAccepted)
  case case3 operator condition right first second acc ihFirst ihSecond =>
    apply simpSeq_memDomain _ _ _ accAccepted
    simp only [memDomain, Bool.and_eq_true] at accepted ⊢
    exact ⟨ihFirst accepted.1 (by simp [memDomain]),
      ihSecond accepted.2 (by simp [memDomain])⟩
  case case4 body acc ih =>
    apply simpSeq_memDomain _ _ _ accAccepted
    simp only [memDomain] at accepted ⊢
    exact ih accepted (by simp [memDomain])
  case case5 => exact accepted
  case case6 target arguments handler acc values sets body firstLabel secondLabel ihBody ihHandler =>
    apply simpSeq_memDomain _ _ _ accAccepted
    rcases handler with _ | ⟨exception, handlerBody, handlerFirst, handlerSecond⟩ <;>
      simp_all [memDomain]
  case case7 liveIn body liveOut acc ih =>
    apply simpSeq_memDomain _ _ _ accAccepted
    simp only [memDomain] at accepted ⊢
    exact ih accepted (by simp [memDomain])
  case case8 => exact simpSeq_memDomain _ _ accepted accAccepted

/-- The reviewed native unreachable-code pass preserves the allocator domain. -/
theorem removeUnreach_memDomain {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (accepted : memDomain program = true) :
    memDomain (removeUnreach program) = true :=
  seqAssocRight_memDomain program .skip accepted (by simp [memDomain])

/-- Every accepted production instruction's native image has the same
allocator support; zero-offset memory normalization keeps the operation. -/
private theorem instructionMemImage {width : Nat}
    (instruction : WordInst (BitVec width)) (native : WordLangInst (BitVec width))
    (encoded : wordLangInstToHOL instruction = some native) :
    memDomain (WordLangProgHOL.inst native) =
      RiscV.allocatorMemorySupported (WordProg.inst instruction) := by
  cases instruction with
  | const destination value =>
    simp only [wordLangInstToHOL, Option.some.injEq] at encoded
    subst native
    simp [memDomain, wordLangInstFromHOL]
  | arith operation =>
    cases operation <;> simp only [wordLangInstToHOL, wordLangArithToHOL,
      Option.map_some, Option.map_none, Option.some.injEq, reduceCtorEq] at encoded
    all_goals try subst native
    all_goals simp [memDomain, wordLangInstFromHOL, wordLangArithFromHOL,
      RiscV.allocatorMemorySupported]
  | mem operation destination address =>
    simp only [wordLangInstToHOL, Option.some.injEq] at encoded
    subst native
    simp [memDomain, wordLangInstFromHOL]
  | memOffset operation destination address offset =>
    simp only [wordLangInstToHOL, Option.some.injEq] at encoded
    subst native
    by_cases zero : offset = 0
    · subst offset
      cases operation <;> simp [memDomain, wordLangInstFromHOL, RiscV.allocatorMemorySupported]
    · simp only [memDomain, wordLangInstFromHOL]
      rw [if_neg (by exact zero)]

/-- Actual encoder output has exactly the production program's allocator
support, for every constructor and both optional Call continuations. The sole
hypothesis is the actual encoder equation. -/
theorem encoderImage_memDomain {width : Nat}
    (production : WordProg (BitVec width)) :
    ∀ native, wordLangProgToHOL production = some native →
      memDomain native = RiscV.allocatorMemorySupported production := by
  fun_induction wordApplyColour (fun name => name) production
  all_goals intro native encoded
  all_goals simp [wordLangProgToHOL, Option.map_eq_some_iff,
    Option.bind_eq_some_iff] at encoded
  all_goals repeat' rcases encoded with ⟨component, run, encoded⟩
  all_goals try subst native
  all_goals simp_all [memDomain, RiscV.allocatorMemorySupported]
  all_goals (have image := instructionMemImage _ _ (by assumption)
             simpa only [memDomain] using image)

end Flapjack.Compiler.Backend.WordUnreach
