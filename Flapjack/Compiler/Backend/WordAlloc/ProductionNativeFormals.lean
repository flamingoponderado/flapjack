import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSAAllocation

namespace Flapjack.WordAlloc
open RiscV RiscV.CakeRegAlloc Compiler.Backend.WordAlloc

/-- The shared consumer retains its actual SSA producer's state and formal
list through cleanup and colouring. This is implementation correspondence,
not an additional HOL theorem or a semantic simulation assumption. -/
theorem allocatorWithSsa_metadata {α : Type} [OfNat α 0] [WordCseHash α] [BEq α]
    (dead : WordProg α → WordProg α)
    (unreach : WordProg α → Option (WordProg α))
    (ssa : Nat → WordProg α → Option (WordSsaState × List Nat × WordProg α))
    (label : Nat) (parameters : List Nat) (source : WordProg α)
    (output : CakeAllocationWithColour α)
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsa dead unreach ssa label parameters source = some output) :
    ∃ body, ssa parameters.length source = some (output.ssaState, output.parameters, body) := by
  unfold cakeAllocateWordFunctionAfterDeadWithColourWithSsa at produced
  split at produced <;> simp_all
  cases ssaResult : ssa parameters.length source with
  | none => simp [ssaResult] at produced
  | some result =>
    rcases result with ⟨state, formals, body⟩
    simp only [ssaResult, Option.bind_some] at produced
    repeat' (split at produced <;> simp_all)
    all_goals rcases produced with ⟨_, _, _, rfl⟩
    all_goals simp

/-- The actual allocator's returned formal list is precisely the native SSA
prologue fresh-name sequence. Encoding names the source; success names the
observed allocator result. No desired formal-list equality is assumed.
This producer relation has no independent HOL original and does not assert
that the original arguments and renamed formals have a semantic state relation. -/
theorem nativeAllocator_parameterNames {width : Nat} [NeZero width]
    (label : Nat) (parameters : List Nat) (source : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (output : CakeAllocationWithColour (BitVec width))
    (produced : cakeAllocateWordFunctionAfterDeadWithColourNativeSSA label parameters source = some output) :
    output.parameters =
      (List.range parameters.length).map (fun index => 4 * index + limitVar native) := by
  unfold cakeAllocateWordFunctionAfterDeadWithColourNativeSSA at produced
  simp only [encoded, Option.bind_some] at produced
  obtain ⟨body, metadata⟩ := allocatorWithSsa_metadata _ _ _ label parameters source output produced
  simp only [wordFullSsaCcTransNativeWithStateFromHOL] at metadata
  cases decoded : wordLangProgFromHOL (fullSsaCcTransWithMetadata parameters.length native).program with
  | none => simp [decoded] at metadata
  | some result =>
    simp only [decoded, Option.map_some, Option.some.injEq, Prod.mk.injEq] at metadata
    rw [← metadata.2.1]
    exact fullSsaCcTransWithMetadata_parameters parameters.length native

end Flapjack.WordAlloc
