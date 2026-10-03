import Flapjack.Pancake.Proofs.WordConvs.ApplyColour
import Flapjack.Compiler.Backend.WordAlloc.WordAllocDef

/-! Native structural preservation for the `word_alloc` section of wordConvsProof.
The existing native allocator and colouring carriers retain the original source branches.
These proofs do not change the executed allocator route. -/

namespace Flapjack.WordConvs
open Flapjack.WordAlloc Flapjack.Compiler.Encoders.Asm

/-- Flapjack factoring of the literal allocator branches: every output is the input
or an application of a total colouring. No allocator success is assumed. -/
private theorem wordAlloc_cases {width : Nat} [NeZero width]
    (fc : Nat) (c : AsmConfigExact width) (alg k : Nat)
    (prog : WordLangProgHOL (BitVec width)) (col : Option (Spt Nat)) :
    wordAlloc fc c alg k prog col = prog ∨
      ∃ f : Nat → Nat, wordAlloc fc c alg k prog col = applyColour f prog := by
  have oracle : ∀ out, oracleColourOk k col (getClashTree prog []) prog
      (getForced c prog []) = some out → ∃ f : Nat → Nat, out = applyColour f prog := by
    intro out h
    unfold oracleColourOk at h
    split at h <;> try dsimp only at h
    · contradiction
    · split at h <;> try dsimp only at h
      · split at h <;> try dsimp only at h
        · cases h; exact ⟨_, rfl⟩
        · contradiction
      · contradiction
  unfold wordAlloc
  dsimp only
  cases h : oracleColourOk k col (getClashTree prog []) prog (getForced c prog []) with
  | none =>
    dsimp only
    cases getHeuristics alg fc prog with
    | mk moves costs =>
      dsimp only
      cases selectRegAlloc alg costs k moves (getClashTree prog [])
          (getForced c prog []) (getStackOnly prog) with
      | failure e => exact Or.inl rfl
      | success colour => exact Or.inr ⟨_, rfl⟩
  | some out => exact Or.inr (oracle out h)

/-- Original unconditional label equality, with only the reviewed word translation. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_alloc_lab_pres"
  (words_as_type_indexed_bitvec)]
theorem wordAlloc_labPres {width : Nat} [NeZero width]
    (fc : Nat) (c : AsmConfigExact width) (alg k : Nat)
    (prog : WordLangProgHOL (BitVec width)) (col : Option (Spt Nat)) :
    extractLabels prog = extractLabels (wordAlloc fc c alg k prog col) := by
  rcases wordAlloc_cases fc c alg k prog col with h | ⟨f, h⟩
  · rw [h]
  · rw [h]; exact applyColour_labPres f prog

/-- Original implication for arbitrary subprogram predicate; no output premise. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_alloc_not_created_subprogs"
  (words_as_type_indexed_bitvec)]
theorem wordAlloc_notCreatedSubprogs {width : Nat} [NeZero width]
    (P : WordLangProgHOL (BitVec width) → Bool) (prog : WordLangProgHOL (BitVec width))
    (fc : Nat) (c : AsmConfigExact width) (alg k : Nat) (col : Option (Spt Nat)) :
    notCreatedSubprogsHOL P prog = true →
      notCreatedSubprogsHOL P (wordAlloc fc c alg k prog col) = true := by
  rcases wordAlloc_cases fc c alg k prog col with h | ⟨f, h⟩
  · rw [h]; exact id
  · rw [h]; exact applyColour_notCreatedSubprogs P prog f

/-- Original unconditional code-label equality. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_word_alloc"
  (words_as_type_indexed_bitvec)]
theorem getCodeLabels_wordAlloc {width : Nat} [NeZero width]
    (fc : Nat) (c : AsmConfigExact width) (alg k : Nat)
    (prog : WordLangProgHOL (BitVec width)) (col : Option (Spt Nat)) :
    getCodeLabelsHOL (wordAlloc fc c alg k prog col) = getCodeLabelsHOL prog := by
  rcases wordAlloc_cases fc c alg k prog col with h | ⟨f, h⟩
  · rw [h]
  · rw [h]; exact getCodeLabels_applyColour f prog

/-- Original handler-label equivalence, retaining the arbitrary handler label. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_word_alloc"
  (words_as_type_indexed_bitvec)]
theorem goodHandlers_wordAlloc {width : Nat} [NeZero width]
    (n fc : Nat) (c : AsmConfigExact width) (alg k : Nat)
    (prog : WordLangProgHOL (BitVec width)) (col : Option (Spt Nat)) :
    goodHandlersHOL n (wordAlloc fc c alg k prog col) = true ↔
      goodHandlersHOL n prog = true := by
  rcases wordAlloc_cases fc c alg k prog col with h | ⟨f, h⟩
  · rw [h]
  · rw [h]; exact goodHandlers_applyColour n f prog

end Flapjack.WordConvs
