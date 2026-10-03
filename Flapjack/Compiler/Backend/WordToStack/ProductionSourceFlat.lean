import Flapjack.Compiler.Backend.WordToStack.ProductionPreSsaDomain
import Flapjack.Compiler.Backend.WordToStack.ProductionSelectorFlat

namespace Flapjack
open RiscV

/-- Every actually encoded pre-SSA allocator body satisfies the original
native flat convention. This follows the executed whole instruction selector,
not a source-flat assumption. Flapjack production API infrastructure; no
independent HOL theorem corresponds to this historical carrier wrapper. -/
theorem wordBeforeSsaAllocatorBody_nativeFlat_map {width : Nat} [NeZero width]
    (body : WordProg (BitVec width)) :
    (wordLangProgToHOL (wordBeforeSsaAllocatorBody body)).map flatExpConventions =
      (wordLangProgToHOL (wordBeforeSsaAllocatorBody body)).map (fun _ => true) := by
  unfold wordBeforeSsaAllocatorBody
  exact wordInstSelectProgramFrom_nativeFlat_map _

/-- The exact source function producer consumed by the executed allocator
supplies a native flat body. Codec availability is derived from source syntax
and the flat property is proved for actual selector output; neither is a
premise. Every Loop source constructor and both nested Call bodies are covered
by the imported full producer/selector proofs. This is Flapjack caller
composition, not a substitute for full compiler evaluation correctness. -/
theorem executedSourceAllocatorInput_nativeFlat
    {width : Nat} [NeZero width] (name : Nat) (parameters : List Nat)
    (body : LoopProg (BitVec width)) :
    ∃ native,
      wordLangProgToHOL (wordBeforeSsaAllocatorBody
        (LoopToWord.loopToWordCompFunc name parameters body)) = some native ∧
      flatExpConventions native = true := by
  have available := executedSourceAllocatorInput_isSome name parameters body
  have observed := wordBeforeSsaAllocatorBody_nativeFlat_map
    (LoopToWord.loopToWordCompFunc name parameters body)
  cases encoded : wordLangProgToHOL (wordBeforeSsaAllocatorBody
      (LoopToWord.loopToWordCompFunc name parameters body)) with
  | none => simp only [encoded, Option.isSome_none, Bool.false_eq_true] at available
  | some native =>
      refine ⟨native, rfl, ?_⟩
      simpa only [encoded, Option.map_some, Option.some.injEq] using observed

end Flapjack
