import Flapjack.Compiler.Backend.WordAlloc.Colour
import Flapjack.Pancake.WordConvs
import Flapjack.Pancake.WordConvs.NotCreated
import Flapjack.Pancake.WordConvs.CodeLabels

/-!
# `wordConvsProof` `apply_colour` preservation group

The `apply_colour` theorems of the `word_alloc` section of
`cakeml/compiler/backend/proofs/wordConvsProofScript.sml` (2781-2898): colouring
preserves labels, created subprograms, code labels and handler labels. The
`word_alloc_*` theorems of that section are ported in the adjacent
`WordConvs.WordAlloc` module using the reviewed native allocator.
-/

namespace Flapjack.WordConvs

open Flapjack.WordAlloc

/-- HOL `apply_colour_lab_pres` (`wordConvsProofScript.sml:2782-2789`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "apply_colour_lab_pres"
  (words_as_type_indexed_bitvec)]
theorem applyColour_labPres {width : Nat} [NeZero width] (col : Nat → Nat) :
    ∀ prog : WordLangProgHOL (BitVec width),
      extractLabels prog = extractLabels (applyColour col prog)
  | .seq a b => by
      simp [applyColour, extractLabels, applyColour_labPres col a, applyColour_labPres col b]
  | .ite _ _ _ a b => by
      simp [applyColour, extractLabels, applyColour_labPres col a, applyColour_labPres col b]
  | .mustTerminate a => by simp [applyColour, extractLabels, applyColour_labPres col a]
  | .loop _ a _ => by simp [applyColour, extractLabels, applyColour_labPres col a]
  | .call none _ _ none => by simp [applyColour, extractLabels]
  | .call none _ _ (some (_, _, _, _)) => by simp [applyColour, extractLabels]
  | .call (some (_, _, r, _, _)) _ _ none => by
      simp [applyColour, extractLabels, applyColour_labPres col r]
  | .call (some (_, _, r, _, _)) _ _ (some (_, p, _, _)) => by
      simp [applyColour, extractLabels, applyColour_labPres col r, applyColour_labPres col p]
  | .skip | .move _ _ | .inst _ | .assign _ _ | .get _ _ | .set _ _ | .store _ _
  | .alloc _ _ | .storeConsts _ _ _ _ _ | .raise _ | .return _ _ | .break _ | .continue _
  | .tick | .opCurrHeap _ _ _ | .locValue _ _ | .install _ _ _ _ _ | .codeBufferWrite _ _
  | .dataBufferWrite _ _ | .ffi _ _ _ _ _ _ | .shareInst _ _ _ => by
      simp [applyColour, extractLabels]

/-- `not_created_subprogs` is invariant under colouring (Flapjack infrastructure
for the tagged implication below). -/
theorem notCreatedSubprogs_applyColour_eq {width : Nat} [NeZero width]
    (P : WordLangProgHOL (BitVec width) → Bool) (f : Nat → Nat) :
    ∀ prog : WordLangProgHOL (BitVec width),
      notCreatedSubprogsHOL P (applyColour f prog) = notCreatedSubprogsHOL P prog
  | .seq a b => by
      simp [applyColour, notCreatedSubprogsHOL, notCreatedSubprogs_applyColour_eq P f a,
        notCreatedSubprogs_applyColour_eq P f b]
  | .ite _ _ _ a b => by
      simp [applyColour, notCreatedSubprogsHOL, notCreatedSubprogs_applyColour_eq P f a,
        notCreatedSubprogs_applyColour_eq P f b]
  | .mustTerminate a => by
      simp [applyColour, notCreatedSubprogsHOL, notCreatedSubprogs_applyColour_eq P f a]
  | .loop _ a _ => by
      simp [applyColour, notCreatedSubprogsHOL, notCreatedSubprogs_applyColour_eq P f a]
  | .call none _ _ none => by simp [applyColour, notCreatedSubprogsHOL]
  | .call none _ _ (some (_, p, _, _)) => by
      simp [applyColour, notCreatedSubprogsHOL, notCreatedSubprogs_applyColour_eq P f p]
  | .call (some (_, _, r, _, _)) _ _ none => by
      simp [applyColour, notCreatedSubprogsHOL, notCreatedSubprogs_applyColour_eq P f r]
  | .call (some (_, _, r, _, _)) _ _ (some (_, p, _, _)) => by
      simp [applyColour, notCreatedSubprogsHOL, notCreatedSubprogs_applyColour_eq P f r,
        notCreatedSubprogs_applyColour_eq P f p]
  | .skip | .move _ _ | .inst _ | .assign _ _ | .get _ _ | .set _ _ | .store _ _
  | .alloc _ _ | .storeConsts _ _ _ _ _ | .raise _ | .return _ _ | .break _ | .continue _
  | .tick | .opCurrHeap _ _ _ | .locValue _ _ | .install _ _ _ _ _ | .codeBufferWrite _ _
  | .dataBufferWrite _ _ | .ffi _ _ _ _ _ _ | .shareInst _ _ _ => by
      simp [applyColour, notCreatedSubprogsHOL]

/-- HOL `apply_colour_not_created_subprogs` (`wordConvsProofScript.sml:2855-2864`);
HOL's free `P`, `prog` and `f` are the binders. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "apply_colour_not_created_subprogs"
  (words_as_type_indexed_bitvec)]
theorem applyColour_notCreatedSubprogs {width : Nat} [NeZero width]
    (P : WordLangProgHOL (BitVec width) → Bool) (prog : WordLangProgHOL (BitVec width))
    (f : Nat → Nat) :
    notCreatedSubprogsHOL P prog = true → notCreatedSubprogsHOL P (applyColour f prog) = true := by
  rw [notCreatedSubprogs_applyColour_eq]; exact id

/-- HOL `word_get_code_labels_apply_colour` (`wordConvsProofScript.sml:2880-2888`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_apply_colour"
  (words_as_type_indexed_bitvec)]
theorem getCodeLabels_applyColour {width : Nat} [NeZero width] (col : Nat → Nat) :
    ∀ ps : WordLangProgHOL (BitVec width),
      getCodeLabelsHOL (applyColour col ps) = getCodeLabelsHOL ps
  | .seq a b => by
      simp [applyColour, getCodeLabelsHOL, getCodeLabels_applyColour col a,
        getCodeLabels_applyColour col b]
  | .ite _ _ _ a b => by
      simp [applyColour, getCodeLabelsHOL, getCodeLabels_applyColour col a,
        getCodeLabels_applyColour col b]
  | .mustTerminate a => by simp [applyColour, getCodeLabelsHOL, getCodeLabels_applyColour col a]
  | .loop _ a _ => by simp [applyColour, getCodeLabelsHOL, getCodeLabels_applyColour col a]
  | .call none _ _ none => by simp [applyColour, getCodeLabelsHOL]
  | .call none _ _ (some (_, p, _, _)) => by
      simp [applyColour, getCodeLabelsHOL, getCodeLabels_applyColour col p]
  | .call (some (_, _, r, _, _)) _ _ none => by
      simp [applyColour, getCodeLabelsHOL, getCodeLabels_applyColour col r]
  | .call (some (_, _, r, _, _)) _ _ (some (_, p, _, _)) => by
      simp [applyColour, getCodeLabelsHOL, getCodeLabels_applyColour col r,
        getCodeLabels_applyColour col p]
  | .skip | .move _ _ | .inst _ | .assign _ _ | .get _ _ | .set _ _ | .store _ _
  | .alloc _ _ | .storeConsts _ _ _ _ _ | .raise _ | .return _ _ | .break _ | .continue _
  | .tick | .opCurrHeap _ _ _ | .locValue _ _ | .install _ _ _ _ _ | .codeBufferWrite _ _
  | .dataBufferWrite _ _ | .ffi _ _ _ _ _ _ | .shareInst _ _ _ => by
      simp [applyColour, getCodeLabelsHOL]

/-- HOL `word_good_handlers_apply_colour` (`wordConvsProofScript.sml:2890-2898`);
HOL's free handler label `n` is the leading binder. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_apply_colour"
  (words_as_type_indexed_bitvec)]
theorem goodHandlers_applyColour {width : Nat} [NeZero width] (n : Nat) (col : Nat → Nat) :
    ∀ ps : WordLangProgHOL (BitVec width),
      goodHandlersHOL n (applyColour col ps) = true ↔ goodHandlersHOL n ps = true
  | .seq a b => by
      simp [applyColour, goodHandlersHOL, goodHandlers_applyColour n col a,
        goodHandlers_applyColour n col b]
  | .ite _ _ _ a b => by
      simp [applyColour, goodHandlersHOL, goodHandlers_applyColour n col a,
        goodHandlers_applyColour n col b]
  | .mustTerminate a => by simp [applyColour, goodHandlersHOL, goodHandlers_applyColour n col a]
  | .loop _ a _ => by simp [applyColour, goodHandlersHOL, goodHandlers_applyColour n col a]
  | .call none _ _ none => by simp [applyColour, goodHandlersHOL]
  | .call none _ _ (some (_, _, _, _)) => by simp [applyColour, goodHandlersHOL]
  | .call (some (_, _, r, _, _)) _ _ none => by
      simp [applyColour, goodHandlersHOL, goodHandlers_applyColour n col r]
  | .call (some (_, _, r, _, _)) _ _ (some (_, p, _, _)) => by
      simp [applyColour, goodHandlersHOL, goodHandlers_applyColour n col r,
        goodHandlers_applyColour n col p]
  | .skip | .move _ _ | .inst _ | .assign _ _ | .get _ _ | .set _ _ | .store _ _
  | .alloc _ _ | .storeConsts _ _ _ _ _ | .raise _ | .return _ _ | .break _ | .continue _
  | .tick | .opCurrHeap _ _ _ | .locValue _ _ | .install _ _ _ _ _ | .codeBufferWrite _ _
  | .dataBufferWrite _ _ | .ffi _ _ _ _ _ _ | .shareInst _ _ _ => by
      simp [applyColour, goodHandlersHOL]

end Flapjack.WordConvs
