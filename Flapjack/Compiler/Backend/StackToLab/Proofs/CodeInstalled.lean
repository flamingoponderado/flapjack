import Flapjack.Compiler.Backend.LabSem.Navigation
import Flapjack.Compiler.Backend.LabProps.Labels
import Flapjack.Compiler.Backend.StackToLab.Native
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqSyntaxExact

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
        all_goals first | exact h | exact tail pc h | exact mapped _ rfl h
      | asm i e l =>
        simp only [List.cons_append, locToPc.eq_4] at h ⊢
        split_ifs at h ⊢ with h1 h2 h3
        all_goals first | exact h | exact tail pc h | exact mapped _ rfl h
      | labAsm i p e l =>
        simp only [List.cons_append, locToPc.eq_4] at h ⊢
        split_ifs at h ⊢ with h1 h2 h3
        all_goals first | exact h | exact tail pc h | exact mapped _ rfl h


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

/-- Number of non-label lines in a list of sections (HOL
`LENGTH (FLAT (MAP (FILTER ($~ o is_Label) o Section_lines) code))`). -/
def codeLength {width : Nat} [NeZero width] (code : LabProgHOL width) : Nat :=
  ((code.map fun s => s.lines.filter fun x => !isLabelHOL x).flatten).length

/-- Fetch after skipping the non-label lines of one section. -/
theorem asmFetchAuxSkipLines {width : Nat} [NeZero width] (sid : Nat) :
    ∀ (lines : List (LabLineHOL width)) (pc : Nat) (rest : LabProgHOL width),
      asmFetchAux ((lines.filter fun x => !isLabelHOL x).length + pc) (⟨sid, lines⟩ :: rest) =
        asmFetchAux pc rest := by
  intro lines
  induction lines with
  | nil => intro pc rest; simp [asmFetchAux.eq_2]
  | cons line lines ih =>
    intro pc rest
    rw [asmFetchAux.eq_3]
    by_cases lab : isLabelHOL line = true
    · rw [if_pos lab]; simpa [List.filter_cons, lab] using ih pc rest
    · rw [if_neg lab]
      simp only [List.filter_cons, lab, Bool.not_false, if_true, List.length_cons]
      rw [if_neg (by omega), show (lines.filter fun x => !isLabelHOL x).length + 1 + pc - 1 =
        (lines.filter fun x => !isLabelHOL x).length + pc by omega]
      exact ih pc rest

/-- Complete original fetch law for code appended on the left. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "asm_fetch_aux_SOME_append2"
  (words_as_type_indexed_bitvec)]
theorem asmFetchAuxSomeAppend2 {width : Nat} [NeZero width] :
    ∀ (pc : Nat) (code : LabProgHOL width) (l : LabLineHOL width) (code2 : LabProgHOL width),
      asmFetchAux pc code2 = some l →
      asmFetchAux (codeLength code + pc) (code ++ code2) = some l := by
  intro pc code l code2 h
  induction code with
  | nil => simpa [codeLength] using h
  | cons s rest ih =>
    obtain ⟨sid, lines⟩ := s
    have := asmFetchAuxSkipLines sid lines (codeLength rest + pc) (rest ++ code2)
    simp only [codeLength, List.map_cons, List.flatten_cons, List.length_append] at this ih ⊢
    rw [Nat.add_assoc, List.cons_append, this]
    exact ih

/-- Complete original installation law for code appended on the left. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "ALOOKUP_PARTITION"]
theorem alookupPartition {α β : Type} [DecidableEq α] :
    ∀ (ls : List (α × β)) (n : α) (v : β), holAlookup ls n = some v →
      ∃ ls1 ls2, ls = ls1 ++ [(n, v)] ++ ls2 ∧ n ∉ ls1.map Prod.fst := by
  intro ls
  induction ls with
  | nil => intro n v h; simp [holAlookup] at h
  | cons e es ih =>
    obtain ⟨k, w⟩ := e
    intro n v h
    simp only [holAlookup] at h
    split at h
    · cases h; rename_i hk; subst hk; exact ⟨[], es, rfl, by simp⟩
    · rename_i hk
      obtain ⟨ls1, ls2, rfl, notMem⟩ := ih n v h
      exact ⟨(k, w) :: ls1, ls2, rfl, by simp [notMem]; exact fun h => hk h.symm⟩

/-- Complete original installation predicate ignoring label positions. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed'_def"
  (words_as_type_indexed_bitvec)]
def codeInstalled' {width : Nat} [NeZero width] (n : Nat) :
    List (LabLineHOL width) → LabProgHOL width → Prop
  | [], _ => True
  | x :: xs, code =>
    if isLabelHOL x then codeInstalled' n xs code
    else asmFetchAux n code = some x ∧ codeInstalled' (n + 1) xs code

/-- Complete original label correctness predicate. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "labs_correct_def"
  (words_as_type_indexed_bitvec)]
def labsCorrect {width : Nat} [NeZero width] (n : Nat) :
    List (LabLineHOL width) → LabProgHOL width → Prop
  | [], _ => True
  | x :: xs, code =>
    if isLabelHOL x then labsCorrect n xs code ∧
      (match x with
       | .label l1 l2 _ => locToPc l1 l2 code = some n
       | _ => True)
    else labsCorrect (n + 1) xs code

/-- Complete original decomposition of installation. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed_eq"
  (words_as_type_indexed_bitvec)]
theorem codeInstalledEq {width : Nat} [NeZero width] :
    ∀ (pc : Nat) (xs : List (LabLineHOL width)) (code : LabProgHOL width),
      codeInstalled pc xs code ↔ codeInstalled' pc xs code ∧ labsCorrect pc xs code := by
  intro pc xs
  induction xs generalizing pc with
  | nil => intro code; simp [codeInstalled, codeInstalled', labsCorrect]
  | cons x xs ih =>
    intro code
    rw [codeInstalled_cons]
    simp only [codeInstalled', labsCorrect]
    by_cases lab : isLabelHOL x = true
    · simp only [lab, if_true, ih]; tauto
    · simp only [lab, Bool.false_eq_true, ite_false, ih]; tauto

/-- Complete original `code_installed'` cons law for a leading section. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed_cons"
  (words_as_type_indexed_bitvec)]
theorem codeInstalledCons {width : Nat} [NeZero width] (rest : LabProgHOL width) :
    ∀ (xs ys : List (LabLineHOL width)) (pos pc : Nat),
      codeInstalled' pc xs rest →
      codeInstalled' (pc + (ys.filter fun x => !isLabelHOL x).length) xs (⟨pos, ys⟩ :: rest) := by
  intro xs
  induction xs with
  | nil => intros; trivial
  | cons x xs ih =>
    intro ys pos pc h
    simp only [codeInstalled'] at h ⊢
    by_cases lab : isLabelHOL x = true
    · simp only [lab, if_true] at h ⊢; exact ih ys pos pc h
    · simp only [lab] at h ⊢
      refine ⟨?_, ?_⟩
      · rw [Nat.add_comm, asmFetchAuxSkipLines]; exact h.1
      · have := ih ys pos (pc + 1) h.2
        rwa [show pc + 1 + (ys.filter fun x => !isLabelHOL x).length =
          pc + (ys.filter fun x => !isLabelHOL x).length + 1 by omega] at this

/-- Complete original fetch shift over a leading section. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "asm_fetch_aux_add"
  (words_as_type_indexed_bitvec)]
theorem asmFetchAuxAdd {width : Nat} [NeZero width] :
    ∀ (ys : List (LabLineHOL width)) (pc pos : Nat) (rest : LabProgHOL width),
      asmFetchAux (pc + (ys.filter fun x => !isLabelHOL x).length) (⟨pos, ys⟩ :: rest) =
        asmFetchAux pc rest := by
  intro ys pc pos rest
  rw [Nat.add_comm]; exact asmFetchAuxSkipLines pos ys pc rest

end Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
