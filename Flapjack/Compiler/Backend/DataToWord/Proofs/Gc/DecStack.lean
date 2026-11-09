module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.LocMerge
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackRel
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackSwap
public import Mathlib.Data.List.Forall2

@[expose] public section

/-! Preservation of the data-to-word stack relation by stack decoding. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack WordSemStackEq

private theorem alistPresent {α : Type} (key : Nat) :
    ∀ entries : List (Nat × α),
      (sptLookup key (sptFromAList entries)).isSome = true ↔ key ∈ entries.map Prod.fst
  | [] => by simp [sptLookup_sptFromAList, sptAListLookup]
  | (k, v) :: entries => by
    rw [sptLookup_sptFromAList]
    by_cases eq : key = k
    · subst k; simp [sptAListLookup]
    · simp only [sptAListLookup, eq, ↓reduceIte, List.map_cons, List.mem_cons, false_or]
      simpa only [sptLookup_sptFromAList] using alistPresent key entries

private theorem stackEnvRel_keys {width : Nat} [NeZero width]
    (dataSize wordSize : Option Nat) (env : Spt DataSem.Value)
    (nonGc gc gc' : List (Nat × WordLocW width))
    (related : stackEnvRel dataSize wordSize env nonGc gc)
    (keys : gc.map Prod.fst = gc'.map Prod.fst) :
    stackEnvRel dataSize wordSize env nonGc gc' := by
  rcases related with ⟨even, size, nonGcKeys, distinct, domain⟩
  refine ⟨?_, size, nonGcKeys, ?_, ?_⟩
  · intro pair member
    have keyMem : pair.1 ∈ gc.map Prod.fst := by
      rw [keys]
      exact List.mem_map.mpr ⟨pair, member, rfl⟩
    obtain ⟨old, oldMem, oldKey⟩ := List.mem_map.mp keyMem
    simpa [oldKey] using even old oldMem
  · simpa [← keys] using distinct
  · intro n
    rw [alistPresent, ← keys, ← alistPresent]
    exact domain n

private theorem stackRel_frameKeys {width : Nat} [NeZero width]
    (source : DataSem.Stack) (before after : WordSemStackFrame width)
    (related : stackRel source before) (keys : sFrameKeyEq before after) : stackRel source after := by
  rcases before with ⟨size, nonGc, gc, handler⟩
  rcases after with ⟨size', nonGc', gc', handler'⟩
  rw [sFrameKeyEqDef2] at keys
  rcases keys with ⟨keyEq, handlerEq, nonGcEq, sizeEq⟩
  subst handler'
  subst nonGc'
  subst size'
  cases source <;> cases handler <;> simp only [stackRel] at related ⊢
  · exact stackEnvRel_keys _ _ _ _ _ _ related keyEq
  · exact ⟨stackEnvRel_keys _ _ _ _ _ _ related.1 keyEq, related.2⟩

private theorem containsLoc_frameKeys {width : Nat} [NeZero width]
    (before after : WordSemStackFrame width) (loc : Nat × Nat)
    (present : containsLoc before loc) (keys : sFrameKeyEq before after) : containsLoc after loc := by
  rcases before with ⟨size, nonGc, gc, handler⟩
  rcases after with ⟨size', nonGc', gc', handler'⟩
  rcases loc with ⟨l1, l2⟩
  rw [sFrameKeyEqDef2] at keys
  simpa [containsLoc, ← keys.2.2.1] using present

/-- Decoding preserves the source frame relation and saved return locations.
The collector-specific form below follows from this general key-preservation
fact for any successful stack decode. -/
theorem stackRel_decStack {width : Nat} [NeZero width]
    (source : List DataSem.Stack) (before after : List (WordSemStackFrame width))
    (locs : List (Nat × Nat)) (roots : List (WordLocW width))
    (related : List.Forall₂ stackRel source before)
    (locations : List.Forall₂ containsLoc before locs)
    (decoded : wordSemDecStack roots before = some after) :
    List.Forall₂ stackRel source after ∧ List.Forall₂ containsLoc after locs := by
  have keyEq := decStackStackKeyEq roots before after decoded
  clear decoded roots
  induction related generalizing after locs with
  | nil =>
    cases after <;> cases locs <;> simp_all [sKeyEq]
  | @cons s b ss bs rel rels ih =>
    cases after with
    | nil => simp [sKeyEq] at keyEq
    | cons a as' =>
      cases locs with
      | nil => cases locations
      | cons loc locs =>
        have frameKey := keyEq.2
        have tailKey := keyEq.1
        cases locations with
        | cons locRel locsRel =>
          have tails := ih as' locs locsRel tailKey
          exact ⟨List.Forall₂.cons (stackRel_frameKeys s b a rel frameKey) tails.1,
            List.Forall₂.cons (containsLoc_frameKeys b a loc locRel frameKey) tails.2⟩

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "stack_rel_dec_stack_IMP_stack_rel"
  (words_as_type_indexed_bitvec)]
theorem stackRel_decStack_locMerge {width : Nat} [NeZero width]
    (before : List (WordSemStackFrame width)) (roots : List (WordLocW width))
    (source : List DataSem.Stack) (after : List (WordSemStackFrame width))
    (locs : List (Nat × Nat))
    (related : List.Forall₂ stackRel source before)
    (locations : List.Forall₂ containsLoc before locs)
    (decoded : wordSemDecStack (locMerge (wordSemEncStack before) roots) before = some after) :
    List.Forall₂ stackRel source after ∧ List.Forall₂ containsLoc after locs :=
  stackRel_decStack source before after locs _ related locations decoded

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
