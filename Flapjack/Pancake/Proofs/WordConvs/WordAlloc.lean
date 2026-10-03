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

/-- Original flat-expression implication for arbitrary colouring. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_alloc_flat_exp_conventions_lem" (words_as_type_indexed_bitvec)]
theorem applyColour_flatExpConventions {width : Nat} [NeZero width] (f : Nat → Nat) :
    ∀ prog : WordLangProgHOL (BitVec width),
      flatExpConventions prog = true → flatExpConventions (applyColour f prog) = true
  | .seq a b => by
      intro h
      simp_all [applyColour, flatExpConventions, applyColour_flatExpConventions f a,
        applyColour_flatExpConventions f b]
  | .ite _ _ _ a b => by
      intro h
      simp_all [applyColour, flatExpConventions, applyColour_flatExpConventions f a,
        applyColour_flatExpConventions f b]
  | .mustTerminate a => by
      simpa [applyColour, flatExpConventions] using applyColour_flatExpConventions f a
  | .loop _ a _ => by
      simpa [applyColour, flatExpConventions] using applyColour_flatExpConventions f a
  | .call none _ _ none => by simp [applyColour, flatExpConventions]
  | .call none _ _ (some (_, p, _, _)) => by
      simpa [applyColour, flatExpConventions] using applyColour_flatExpConventions f p
  | .call (some (_, _, r, _, _)) _ _ none => by
      simpa [applyColour, flatExpConventions] using applyColour_flatExpConventions f r
  | .call (some (_, _, r, _, _)) _ _ (some (_, p, _, _)) => by
      intro h
      simp_all [applyColour, flatExpConventions, applyColour_flatExpConventions f r,
        applyColour_flatExpConventions f p]
  | .set _ exp => by
      cases exp <;> simp [applyColour, flatExpConventions, applyColourExp, applyColourExpCore]
  | .shareInst _ _ exp => by
      intro h
      cases exp <;> simp_all [applyColour, flatExpConventions, applyColourExp, applyColourExpCore]
      unfold flatExpConventions at h
      split at h <;> simp_all [flatExpConventions, applyColourExpCore]
  | .skip | .move _ _ | .inst _ | .assign _ _ | .get _ _ | .store _ _
  | .alloc _ _ | .storeConsts _ _ _ _ _ | .raise _ | .return _ _ | .break _ | .continue _
  | .tick | .opCurrHeap _ _ _ | .locValue _ _ | .install _ _ _ _ _ | .codeBufferWrite _ _
  | .dataBufferWrite _ _ | .ffi _ _ _ _ _ _ => by simp [applyColour, flatExpConventions]

/-- Flapjack instruction-case factoring: equality of destination and first source
is preserved by arbitrary renaming, without assuming injectivity. -/
private theorem twoRegInst_applyColourInst {width : Nat} [NeZero width]
    (f : Nat → Nat) (i : WordLangInst (BitVec width)) :
    twoRegInst i = true → twoRegInst (applyColourInst f i) = true := by
  intro h
  cases i with
  | skip => simp [applyColourInst, applyColourInstCore, twoRegInst]
  | const r w => simp [applyColourInst, applyColourInstCore, twoRegInst]
  | arith a =>
      cases a <;> simp_all [applyColourInst, applyColourInstCore, twoRegInst, beq_iff_eq]
  | mem op r a =>
      cases op <;> cases a <;> simp [applyColourInst, applyColourInstCore, twoRegInst]
  | fp op =>
      cases op <;> simp [applyColourInst, applyColourInstCore, twoRegInst]

/-- Original full instruction-convention implication. The positive-width theorem
uses the constructor-for-constructor instruction carrier and the literal
`twoRegInst` clauses; its width-general helper admits zero width, but this
statement retains HOL positivity. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_alloc_two_reg_inst_lem" (words_as_type_indexed_bitvec)]
theorem applyColour_twoRegInst {width : Nat} [NeZero width] (f : Nat → Nat) :
    ∀ prog : WordLangProgHOL (BitVec width),
      everyInst twoRegInst prog = true → everyInst twoRegInst (applyColour f prog) = true
  | .seq a b => by
      intro h
      simp_all [applyColour, everyInst, applyColour_twoRegInst f a, applyColour_twoRegInst f b]
  | .ite _ _ _ a b => by
      intro h
      simp_all [applyColour, everyInst, applyColour_twoRegInst f a, applyColour_twoRegInst f b]
  | .mustTerminate a => by
      simpa [applyColour, everyInst] using applyColour_twoRegInst f a
  | .loop _ a _ => by
      simpa [applyColour, everyInst] using applyColour_twoRegInst f a
  | .call none _ _ none => by simp [applyColour, everyInst]
  | .call none _ _ (some (_, _, _, _)) => by simp [applyColour, everyInst]
  | .call (some (_, _, r, _, _)) _ _ none => by
      simpa [applyColour, everyInst] using applyColour_twoRegInst f r
  | .call (some (_, _, r, _, _)) _ _ (some (_, p, _, _)) => by
      intro h
      simp_all [applyColour, everyInst, applyColour_twoRegInst f r, applyColour_twoRegInst f p]
  | .inst i => by simpa [applyColour, everyInst] using twoRegInst_applyColourInst f i
  | .opCurrHeap _ _ _ => by
      simp only [applyColour, everyInst, twoRegInst, beq_iff_eq]
      intro h
      exact congrArg f h
  | .skip | .move _ _ | .assign _ _ | .get _ _ | .store _ _ | .set _ _ | .shareInst _ _ _
  | .alloc _ _ | .storeConsts _ _ _ _ _ | .raise _ | .return _ _ | .break _ | .continue _
  | .tick | .locValue _ _ | .install _ _ _ _ _ | .codeBufferWrite _ _
  | .dataBufferWrite _ _ | .ffi _ _ _ _ _ _ => by simp [applyColour, everyInst]

/-- Original allocator flat-expression implication for every allocator branch. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_alloc_flat_exp_conventions" (words_as_type_indexed_bitvec)]
theorem wordAlloc_flatExpConventions {width : Nat} [NeZero width]
    (fc : Nat) (c : AsmConfigExact width) (alg k : Nat)
    (prog : WordLangProgHOL (BitVec width)) (col : Option (Spt Nat)) :
    flatExpConventions prog = true → flatExpConventions (wordAlloc fc c alg k prog col) = true := by
  rcases wordAlloc_cases fc c alg k prog col with h | ⟨f, h⟩
  · rw [h]; exact id
  · rw [h]; exact applyColour_flatExpConventions f prog

/-- Original allocator two-register implication for every allocator branch. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_alloc_two_reg_inst" (words_as_type_indexed_bitvec)]
theorem wordAlloc_twoRegInst {width : Nat} [NeZero width]
    (fc : Nat) (c : AsmConfigExact width) (alg k : Nat)
    (prog : WordLangProgHOL (BitVec width)) (col : Option (Spt Nat)) :
    everyInst twoRegInst prog = true → everyInst twoRegInst (wordAlloc fc c alg k prog col) = true := by
  rcases wordAlloc_cases fc c alg k prog col with h | ⟨f, h⟩
  · rw [h]; exact id
  · rw [h]; exact applyColour_twoRegInst f prog

end Flapjack.WordConvs
