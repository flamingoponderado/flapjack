import Flapjack.Compiler.Backend.WordUnreach.Production
import Flapjack.Compiler.Backend.WordAlloc.ProductionCanonicalCutsetCodec

namespace Flapjack.Compiler.Backend.WordUnreach
open Flapjack WordAlloc

/-- Flapjack codec invariant: sequence simplification retains canonical cutsets.
Moves contain no cutsets, and dropping unreachable tails cannot invalidate a
retained field. This has no independent HOL declaration. -/
theorem simpSeq_setsWf {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width))
    (left : WordAllocatorProgramSetsWf first) (right : WordAllocatorProgramSetsWf second) :
    WordAllocatorProgramSetsWf (simpSeq first second) := by
  unfold simpSeq
  split
  · exact left
  · cases first <;> try simp_all [WordAllocatorProgramSetsWf]
    case move priority moves =>
      cases second <;> try simp_all [destSeqMove, WordAllocatorProgramSetsWf]
      case seq head tail =>
        cases head <;> try simp_all [WordAllocatorProgramSetsWf]
        split <;> simp_all [WordAllocatorProgramSetsWf]

/-- Complete canonical-cutset preservation by native right association,
including both Call bodies and their retained cutset fields. Flapjack codec
infrastructure; no output invariant or evaluation is assumed. -/
theorem seqAssocRight_setsWf {width : Nat} [NeZero width]
    (program acc : WordLangProgHOL (BitVec width))
    (valid : WordAllocatorProgramSetsWf program) (accValid : WordAllocatorProgramSetsWf acc) :
    WordAllocatorProgramSetsWf (seqAssocRight program acc) := by
  fun_induction seqAssocRight program acc
  case case1 => exact accValid
  case case2 first second acc ihSecond ihFirst =>
    simp only [WordAllocatorProgramSetsWf] at valid
    exact ihFirst valid.1 (ihSecond valid.2 accValid)
  case case3 operator condition right first second acc ihFirst ihSecond =>
    apply simpSeq_setsWf _ _ _ accValid
    simp only [WordAllocatorProgramSetsWf] at valid ⊢
    exact ⟨ihFirst valid.1 (by simp [WordAllocatorProgramSetsWf]),
      ihSecond valid.2 (by simp [WordAllocatorProgramSetsWf])⟩
  case case4 body acc ih =>
    apply simpSeq_setsWf _ _ _ accValid
    simp only [WordAllocatorProgramSetsWf] at valid ⊢
    exact ih valid (by simp [WordAllocatorProgramSetsWf])
  case case5 => exact valid
  case case6 target arguments handler acc values sets body firstLabel secondLabel ihBody ihHandler =>
    apply simpSeq_setsWf _ _ _ accValid
    rcases handler with _ | ⟨exception, handlerBody, handlerFirst, handlerSecond⟩ <;>
      simp_all [WordAllocatorProgramSetsWf]
  case case7 liveIn body liveOut acc ih =>
    apply simpSeq_setsWf _ _ _ accValid
    simp only [WordAllocatorProgramSetsWf] at valid ⊢
    exact ⟨valid.1, ih valid.2 (by simp [WordAllocatorProgramSetsWf])⟩
  case case8 => exact simpSeq_setsWf _ _ valid accValid

/-- Native unreachable removal preserves the complete canonical program image.
This is representation closure, not an additional HOL evaluation hypothesis. -/
theorem removeUnreach_setsWf {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (valid : WordAllocatorProgramSetsWf program) :
    WordAllocatorProgramSetsWf (removeUnreach program) :=
  seqAssocRight_setsWf program .skip valid (by simp [WordAllocatorProgramSetsWf])

/-- The actual output re-encodes literally to the reviewed native pass output.
Canonical cutsets are derived from the input encoder and pass preservation,
not assumed about the output. Flapjack production codec infrastructure. -/
theorem executedUnreach_literalImage {width : Nat} [NeZero width]
    (source : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native) :
    ∃ output : WordProg (BitVec width),
      RiscV.wordRemoveUnreachViaHOL? source = some output ∧
      wordLangProgToHOL output = some (removeUnreach native) := by
  have available := RiscV.wordRemoveUnreachViaHOL?_isSome source
    (by simp only [encoded, Option.isSome_some])
  unfold RiscV.wordRemoveUnreachViaHOL? at available
  simp only [encoded, Option.bind_some] at available
  cases decoded : wordLangProgFromHOL (removeUnreach native) with
  | none => simp [decoded] at available
  | some output =>
      refine ⟨output, ?_, canonicalProgram_codec _ output
        (removeUnreach_setsWf native (productionProgram_setsWf source native encoded)) decoded⟩
      simp only [RiscV.wordRemoveUnreachViaHOL?, encoded, Option.bind_some, decoded]

end Flapjack.Compiler.Backend.WordUnreach
