import Flapjack.Compiler.Backend.LabSem.Navigation
import Flapjack.Compiler.Backend.LabSem.Updates
import Flapjack.Compiler.Backend.StackToLab.Native
import Flapjack.Compiler.Backend.Semantics.StackSem.Control
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
import Flapjack.Compiler.Encoders.AsmSem
import Flapjack.Misc.FiniteMapApply
import Flapjack.HolArb
import Mathlib.Tactic.SplitIfs

/-!
Opening lemmas of `stack_to_labProofScript.sml` (lines 32-99, its "TODO: move"
group): word shifts, the trivial LabSem assertion, the absence of fetched
labels, the jump-destination selectors and comparison negation.
-/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.Prelude
open Flapjack
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Backend.StackToLab Flapjack.StackSemControl

-- This supplies only HOL type inhabitedness. Undefined FAPPLY results remain
-- the opaque holFapplyOutside; this instance does not choose a missing value.
local instance {width : Nat} [NeZero width] : Nonempty (WordLocW width) := ⟨.word 0⟩

/-- A defined `word_sh` is in range and agrees with the total `word_shift`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "word_sh_word_shift"
  (words_as_type_indexed_bitvec)]
theorem wordShWordShift {width : Nat} [NeZero width] {a : Flapjack.Shift}
    {b : BitVec width} {c : Nat} {z : BitVec width} :
    wordShiftHOL a b c = some z → c < width ∧ z = wordShift a b c := by
  intro h
  have pos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  unfold wordShiftHOL at h
  split_ifs at h with range
  refine ⟨by omega, ?_⟩
  cases a <;> simp_all [wordShift]

/-- The LabSem assertion of a true condition is the identity. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "assert_T"
  (words_as_type_indexed_bitvec)]
theorem assertT {width : Nat} [NeZero width] {C F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) : assertState true s = s := by
  cases s
  simp [assertState]

/-- `asm_fetch_aux` never returns a label line. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "asm_fetch_aux_no_label"
  (words_as_type_indexed_bitvec)]
theorem asmFetchAuxNoLabel {width : Nat} [NeZero width] {l1 l2 : Nat} {x : Nat} :
    ∀ (pc : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
        (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
        (BitVec width)))),
      asmFetchAux pc code = some (.label l1 l2 x) → False := by
  intro pc code
  induction pc, code using asmFetchAux.induct <;> intro h <;> rw [asmFetchAux] at h <;>
    simp_all [isLabelHOL]

/-- Canonical standalone-map witness for the `dest_to_loc_def` register map. -/
theorem holFmapAsFiniteSupportParamWitness_destToLoc_regs {width : Nat} [NeZero width]
    {β : Type} (regs : HolFiniteMapExact β (WordLocW width)) (key : β) :
    (HolFiniteMapExact.mk regs.lookup regs.finiteSupport).lookup key = regs.lookup key ∧
      (HolFiniteMapExact.mk regs.lookup regs.finiteSupport).finiteSupport =
        regs.finiteSupport ∧
      HolFiniteMapExact.mk regs.lookup regs.finiteSupport = regs :=
  ⟨rfl, rfl, rfl⟩

/-- Complete original destination selector over a finite register map: a
register is read with the original `FAPPLY`, and a non-`Loc` value is HOL's
unspecified incomplete-case `ARB`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "dest_to_loc_def"
  (fmap_as_finite_support_parameters := [regs]) (words_as_type_indexed_bitvec)]
noncomputable def destToLoc {width : Nat} [NeZero width] {β : Type}
    (regs : HolFiniteMapExact β (WordLocW width)) (dest : Nat ⊕ β) : Nat :=
  match dest with
  | .inl p => p
  | .inr r =>
      match holFapply regs r with
      | .loc loc _ => loc
      | .word _ => holArb Nat

/-- Complete original destination selector over a total register function;
a non-`Loc` value is HOL's unspecified incomplete-case `ARB`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "dest_to_loc'_def"
  (words_as_type_indexed_bitvec)]
noncomputable def destToLoc' {width : Nat} [NeZero width] {β : Type}
    (regs : β → WordLocW width) (dest : Nat ⊕ β) : Nat :=
  match dest with
  | .inl p => p
  | .inr r =>
      match regs r with
      | .loc loc _ => loc
      | .word _ => holArb Nat

/-- A successful StackSem code lookup is the lookup at the selected
destination, and an indirect destination register is in the map's domain. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "find_code_lookup"
  (fmap_as_finite_support_relation := [regs]) (words_as_type_indexed_bitvec)]
theorem findCodeLookup {width : Nat} [NeZero width] {β α : Type}
    {dest : Nat ⊕ β} {regs : HolFiniteMapExact β (WordLocW width)} {code : Spt α}
    {p : α} :
    findCode dest regs code = some p →
      sptLookup (destToLoc regs dest) code = some p ∧
        (∀ r, dest = .inr r → (regs.lookup r).isSome) := by
  intro h
  cases dest with
  | inl l => exact ⟨by simpa [findCode, destToLoc] using h, by simp⟩
  | inr r =>
      unfold findCode at h
      simp only at h
      split at h
      · rename_i label found
        refine ⟨?_, ?_⟩
        · simpa [destToLoc, holFapply_of_lookup found] using h
        · intro r' e
          cases e
          simp [found]
      · simp at h

/-- A compiled jump is never a label. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "not_is_Label_compile_jump"
  (words_as_type_indexed_bitvec)]
theorem notIsLabelCompileJump {width : Nat} [NeZero width] (dest : Nat ⊕ Nat) :
    isLabelHOL (compileJumpHOL (width := width) dest) = false := by
  cases dest <;> rfl

/-- WordSem comparison of two words is always defined. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "word_cmp_not_NONE"
  (words_as_type_indexed_bitvec)]
theorem wordCmpNotNone {width : Nat} [NeZero width] (cmp : HolCmp) (w1 w2 : BitVec width) :
    wordSemWordCmp cmp (.word w1) (.word w2) ≠ none := by
  simp [wordSemWordCmp]

/-- ASM comparison of the negated condition is the Boolean negation. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "word_cmp_negate_alt"
  (words_as_type_indexed_bitvec)]
theorem wordCmpNegateAlt {width : Nat} [NeZero width] (cmp : HolCmp) (w1 w2 : BitVec width) :
    wordCmpHOL (negateHOL cmp) w1 w2 = !wordCmpHOL cmp w1 w2 := by
  cases cmp <;> simp [negateHOL, wordCmpHOL, bne]

/-- WordSem comparison of the negated condition maps negation over the
original optional result. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "word_cmp_negate"
  (words_as_type_indexed_bitvec)]
theorem wordCmpNegate {width : Nat} [NeZero width] (cmp : HolCmp) (w1 w2 : WordLocW width) :
    wordSemWordCmp (negateHOL cmp) w1 w2 = (wordSemWordCmp cmp w1 w2).map (!·) := by
  cases w1 <;> cases w2 <;> cases cmp <;>
    simp [negateHOL, wordSemWordCmp, wordCmpHOL, bne] <;> split_ifs <;> simp

end Flapjack.Compiler.Backend.StackToLab.Proofs.Prelude
