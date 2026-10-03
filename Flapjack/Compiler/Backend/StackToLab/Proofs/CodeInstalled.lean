import Flapjack.Compiler.Backend.LabSem.Navigation
import Flapjack.Compiler.Backend.LabProps.Labels
import Flapjack.Compiler.Backend.StackToLab.Native
import Mathlib.Tactic.SplitIfs

/-! Code-installation lemmas of `stack_to_labProofScript.sml` (lines 102-600):
`code_installed`, `code_installed'`, `labs_correct` and the `asm_fetch_aux` /
`loc_to_pc` append and prefix laws, over the native LabLang carrier.
-/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

/-- Complete original installation predicate: labels resolve to the current
position, other lines are fetched there. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed_def"
  (words_as_type_indexed_bitvec)]
def codeInstalled {width : Nat} [NeZero width] (n : Nat) :
    List (LabLineHOL width) → LabProgHOL width → Prop
  | [], _ => True
  | x :: xs, code =>
    if isLabelHOL x then
      (match x with
       | .label l1 l2 _ => locToPc l1 l2 code = some n
       | _ => True) ∧ codeInstalled n xs code
    else asmFetchAux n code = some x ∧ codeInstalled (n + 1) xs code

/-- The cons equation of `codeInstalled`. -/
theorem codeInstalled_cons {width : Nat} [NeZero width] (n : Nat) (x : LabLineHOL width)
    (xs : List (LabLineHOL width)) (code : LabProgHOL width) :
    codeInstalled n (x :: xs) code =
      if isLabelHOL x then
        (match x with
         | .label l1 l2 _ => locToPc l1 l2 code = some n
         | _ => True) ∧ codeInstalled n xs code
      else asmFetchAux n code = some x ∧ codeInstalled (n + 1) xs code := rfl

/-- Complete original fetch append law. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "asm_fetch_aux_SOME_append"
  (words_as_type_indexed_bitvec)]
theorem asmFetchAuxSomeAppend {width : Nat} [NeZero width] :
    ∀ (pc : Nat) (code : LabProgHOL width) (l : LabLineHOL width) (code2 : LabProgHOL width),
      asmFetchAux pc code = some l → asmFetchAux pc (code ++ code2) = some l := by
  intro pc code
  induction pc, code using asmFetchAux.induct <;> intro l code2 h <;>
    simp_all [asmFetchAux]

/-- Complete original fetch prefix law. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "asm_fetch_aux_SOME_isPREFIX"
  (words_as_type_indexed_bitvec)]
theorem asmFetchAuxSomeIsPrefix {width : Nat} [NeZero width] :
    ∀ (pc : Nat) (code : LabProgHOL width) (l : LabLineHOL width) (code2 : LabProgHOL width),
      asmFetchAux pc code = some l ∧ code <+: code2 → asmFetchAux pc code2 = some l := by
  rintro pc code l code2 ⟨h, ⟨t, rfl⟩⟩
  exact asmFetchAuxSomeAppend pc code l t h

/-- Complete original label-position append law. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "loc_to_pc_APPEND"
  (words_as_type_indexed_bitvec)]
theorem locToPcAppend {width : Nat} [NeZero width] :
    ∀ (n m : Nat) (code : LabProgHOL width) (pc : Nat) (code2 : LabProgHOL width),
      locToPc n m code = some pc → locToPc n m (code ++ code2) = some pc := by
  intro n m code
  induction code with
  | nil => intro pc code2 h; simp [locToPc.eq_1] at h
  | cons s rest ih =>
    obtain ⟨sid, lines⟩ := s
    induction lines with
    | nil =>
      intro pc code2 h
      simp only [List.cons_append, locToPc.eq_2] at h ⊢
      by_cases hc : sid = n ∧ m = 0
      · rw [if_pos hc] at h ⊢; exact h
      · rw [if_neg hc] at h ⊢; exact ih pc code2 h
    | cons line lines ihl =>
      intro pc code2 h
      have tail : ∀ p, locToPc n m (⟨sid, lines⟩ :: rest) = some p →
          locToPc n m (⟨sid, lines⟩ :: (rest ++ code2)) = some p :=
        fun p hp => by simpa using ihl p code2 hp
      have mapped : ∀ q, Option.map (fun x => x + 1) (locToPc n m (⟨sid, lines⟩ :: rest)) = q →
          q = some pc → Option.map (fun x => x + 1)
            (locToPc n m (⟨sid, lines⟩ :: (rest ++ code2))) = some pc := by
        rintro q hq rfl
        obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
        rw [tail p hp]; rfl
      cases line with
      | label a b c =>
        simp only [List.cons_append, locToPc.eq_3] at h ⊢
        split_ifs at h ⊢ with h1 h2 h3
        all_goals first | exact h | exact tail pc h | exact mapped _ rfl h | simp_all
      | asm i e l =>
        simp only [List.cons_append, locToPc.eq_4] at h ⊢
        split_ifs at h ⊢ with h1 h2 h3
        all_goals first | exact h | exact tail pc h | exact mapped _ rfl h | simp_all
      | labAsm i p e l =>
        simp only [List.cons_append, locToPc.eq_4] at h ⊢
        split_ifs at h ⊢ with h1 h2 h3
        all_goals first | exact h | exact tail pc h | exact mapped _ rfl h | simp_all


/-- Complete original installation append law. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed_APPEND"
  (words_as_type_indexed_bitvec)]
theorem codeInstalledAppend {width : Nat} [NeZero width] :
    ∀ (ls : List (LabLineHOL width)) (pc : Nat) (code code2 : LabProgHOL width),
      codeInstalled pc ls code → codeInstalled pc ls (code ++ code2) := by
  intro ls
  induction ls with
  | nil => intros; trivial
  | cons x xs ih =>
    intro pc code code2 h
    rw [codeInstalled_cons] at h ⊢
    split at h
    · rename_i lab
      rw [if_pos lab]
      refine ⟨?_, ih _ _ _ h.2⟩
      cases x with
      | label l1 l2 _ => exact locToPcAppend _ _ _ _ _ h.1
      | _ => trivial
    · rename_i lab
      rw [if_neg lab]
      exact ⟨asmFetchAuxSomeAppend _ _ _ _ h.1, ih _ _ _ h.2⟩

/-- Complete original installation prefix law. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed_isPREFIX"
  (words_as_type_indexed_bitvec)]
theorem codeInstalledIsPrefix {width : Nat} [NeZero width] :
    ∀ (ls : List (LabLineHOL width)) (pc : Nat) (code code2 : LabProgHOL width),
      codeInstalled pc ls code ∧ code <+: code2 → codeInstalled pc ls code2 := by
  rintro ls pc code code2 ⟨h, ⟨t, rfl⟩⟩
  exact codeInstalledAppend ls pc code t h

/-- Complete original label-position prefix law. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "loc_to_pc_isPREFIX"
  (words_as_type_indexed_bitvec)]
theorem locToPcIsPrefix {width : Nat} [NeZero width] :
    ∀ (n m : Nat) (code : LabProgHOL width) (pc : Nat) (code2 : LabProgHOL width),
      locToPc n m code = some pc ∧ code <+: code2 → locToPc n m code2 = some pc := by
  rintro n m code pc code2 ⟨h, ⟨t, rfl⟩⟩
  exact locToPcAppend n m code pc t h

/-- Complete original installation split for an appended line list. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed_append_imp"
  (words_as_type_indexed_bitvec)]
theorem codeInstalledAppendImp {width : Nat} [NeZero width] :
    ∀ (l1 : List (LabLineHOL width)) (pc : Nat) (l2 : List (LabLineHOL width))
      (code : LabProgHOL width),
      codeInstalled pc (l1 ++ l2) code →
      codeInstalled pc l1 code ∧
        codeInstalled (pc + (l1.filter (fun x => !isLabelHOL x)).length) l2 code := by
  intro l1
  induction l1 with
  | nil => intro pc l2 code h; exact ⟨trivial, by simpa using h⟩
  | cons x xs ih =>
    intro pc l2 code h
    simp only [List.cons_append] at h
    rw [codeInstalled_cons] at h ⊢
    split at h
    · rename_i lab
      obtain ⟨first, rest⟩ := ih pc l2 code h.2
      refine ⟨by rw [if_pos lab]; exact ⟨h.1, first⟩, ?_⟩
      simpa [List.filter_cons, lab] using rest
    · rename_i lab
      obtain ⟨first, rest⟩ := ih (pc + 1) l2 code h.2
      refine ⟨by rw [if_neg lab]; exact ⟨h.1, first⟩, ?_⟩
      simp only [List.filter_cons, lab, Bool.not_false, if_true, List.length_cons]
      simpa [Nat.add_assoc, Nat.add_comm 1] using rest

end Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
