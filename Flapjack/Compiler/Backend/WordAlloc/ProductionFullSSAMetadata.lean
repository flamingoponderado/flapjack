import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSA
import Flapjack.Compiler.Backend.WordAlloc.ProductionSSAStateRoute
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameLookup
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASetup.ListNextVarRenameArithmetic
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASetup.EvenListDistinct

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack allocator packaging around the native full SSA program. The extra
fields are caller metadata, not additional HOL full-pass results. -/
structure FullSsaAllocatorResult (width : Nat) [NeZero width] where
  program : WordLangProgHOL (BitVec width)
  current : Spt Nat
  next : Nat
  parameters : List Nat

/-- Run native setup and body renaming once, retaining the metadata otherwise
discarded by HOL full_ssa_cc_trans. No separate HOL declaration has this result
carrier. The entire program projection is proved equal to the tagged pass. -/
def fullSsaCcTransWithMetadata {width : Nat} [NeZero width]
    (parameterCount : Nat) (program : WordLangProgHOL (BitVec width)) : FullSsaAllocatorResult width :=
  let (entry, initial, next) := setupSSA (outputWidth := width) parameterCount (limitVar program) program
  let (body, current, finalNext) := ssaCcTrans program initial next []
  ⟨.seq entry body, current, finalNext, (evenList parameterCount).map (optionLookup initial)⟩

/-- Unconditional entire program equality to the source-reviewed native full
pass. Metadata packaging introduces no alternative program producer. -/
theorem fullSsaCcTransWithMetadata_program {width : Nat} [NeZero width]
    (parameterCount : Nat) (program : WordLangProgHOL (BitVec width)) :
    (fullSsaCcTransWithMetadata parameterCount program).program = fullSsaCcTrans parameterCount program := by
  rfl

/-- The allocator formals are exactly the original native prologue fresh-name
sequence, for every parameter count and initial counter. No map validity or
successful program evaluation is assumed. Flapjack metadata infrastructure. -/
theorem setupSSA_parameterNames {width : Nat} [NeZero width]
    (count limit : Nat) (program : WordLangProgHOL (BitVec width)) :
    (evenList count).map (optionLookup (setupSSA (outputWidth := width) count limit program).2.1) =
      (List.range count).map (fun index => 4 * index + limit) := by
  unfold setupSSA
  dsimp only
  generalize h : listNextVarRename (evenList count) .ln limit = result
  rcases result with ⟨outputs, map, next⟩
  have arithmetic := listNextVarRenameLemma1 (evenList count) .ln limit outputs map next h
  have lookup := listNextVarRenameLemma2Prime (evenList count) .ln limit outputs map next h (evenListNodup count)
  have mapped : (evenList count).map (optionLookup map) = outputs := by
    rw [lookup.1]
    apply List.map_congr_left
    intro key member
    unfold optionLookup
    cases sptLookup key map <;> rfl
  rw [mapped, arithmetic.2.1]
  simp [evenList]

/-- Exact entry-formal metadata of the complete native pass, independent of
body contents and subsequent renamings. -/
theorem fullSsaCcTransWithMetadata_parameters {width : Nat} [NeZero width]
    (count : Nat) (program : WordLangProgHOL (BitVec width)) :
    (fullSsaCcTransWithMetadata count program).parameters =
      (List.range count).map (fun index => 4 * index + limitVar program) := by
  have names := setupSSA_parameterNames count (limitVar program) program
  unfold fullSsaCcTransWithMetadata
  dsimp only
  generalize hs : setupSSA (outputWidth := width) count (limitVar program) program = setup at names ⊢
  rcases setup with ⟨entry, initial, next⟩
  generalize hb : ssaCcTrans program initial next [] = body
  rcases body with ⟨renamed, final, finalNext⟩
  exact names

/-- Convert only the allocator facade; native tree traversal owns enumeration. -/
def FullSsaAllocatorResult.toProductionState {width : Nat} [NeZero width]
    (result : FullSsaAllocatorResult width) : WordSsaState :=
  ⟨sptToAList result.current, result.next⟩

/-- Every final map lookup and the final counter survive the facade conversion,
for unrestricted native results. This is Flapjack representation infrastructure. -/
theorem FullSsaAllocatorResult.toProductionState_corresponds {width : Nat} [NeZero width]
    (result : FullSsaAllocatorResult width) :
    result.toProductionState.next = result.next ∧
      ∀ key, lookupNatInfo key result.toProductionState.current = sptLookup key result.current := by
  exact ⟨rfl, productionSsaDecodedLookup result.current⟩

end Flapjack.Compiler.Backend.WordAlloc

namespace Flapjack
open Compiler.Backend.WordAlloc

/-- Decode an already encoded complete native full-pass result. The native
setup/body pass runs once and provides the allocator metadata. -/
def wordFullSsaCcTransNativeWithStateFromHOL {width : Nat} [NeZero width]
    (parameterCount : Nat) (native : WordLangProgHOL (BitVec width)) :
    Option (WordSsaState × List Nat × WordProg (BitVec width)) :=
  let result := fullSsaCcTransWithMetadata parameterCount native
  (wordLangProgFromHOL result.program).map fun body =>
    (result.toProductionState, result.parameters, body)

/-- Native full SSA with allocator metadata, using one native setup/body pass.
This API adapter has no independent HOL original. -/
def wordFullSsaCcTransNativeWithState {width : Nat} [NeZero width]
    (parameterCount : Nat) (program : WordProg (BitVec width)) :
    Option (WordSsaState × List Nat × WordProg (BitVec width)) :=
  (wordLangProgToHOL program).bind fun native =>
    wordFullSsaCcTransNativeWithStateFromHOL parameterCount native

/-- The tuple adapter preserves precisely the complete native full-pass program
boundary, including rejection; no successful output is a premise. -/
theorem wordFullSsaCcTransNativeWithState_program {width : Nat} [NeZero width]
    (parameterCount : Nat) (program : WordProg (BitVec width)) :
    (wordFullSsaCcTransNativeWithState parameterCount program).map (fun result => result.2.2) =
      wordFullSsaCcTransNative parameterCount program := by
  cases encoded : wordLangProgToHOL program <;>
    simp [wordFullSsaCcTransNativeWithState, wordFullSsaCcTransNativeWithStateFromHOL, wordFullSsaCcTransNative, encoded,
      fullSsaCcTransWithMetadata_program, Option.map_map, Function.comp_def]

/-- Every encoder-accepted production program obtains the whole native tuple;
no final-state, output decoder or target execution premise is assumed. -/
theorem wordFullSsaCcTransNativeWithState_domain {width : Nat} [NeZero width]
    (parameterCount : Nat) (program : WordProg (BitVec width)) :
    (wordFullSsaCcTransNativeWithState parameterCount program).isSome =
      (wordLangProgToHOL program).isSome := by
  have projection := congrArg Option.isSome (wordFullSsaCcTransNativeWithState_program parameterCount program)
  simpa only [Option.isSome_map, wordFullSsaCcTransNative_domain] using projection

end Flapjack
