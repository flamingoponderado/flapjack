import Flapjack.Compiler.Backend.LabSem.Navigation
import Flapjack.Compiler.Backend.LabProps.Labels
import Flapjack.Compiler.Backend.LabProps.LabelSets
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

/-- Skipping a section that cannot contain the searched label. Local factoring
of `loc_to_pc_skip_section` and `loc_to_pc_append2`. -/
theorem locToPcSkip {width : Nat} [NeZero width] (k ll sid : Nat) (hsid : sid ≠ k) :
    ∀ (lines : List (LabLineHOL width)) (rest : LabProgHOL width),
      (∀ line ∈ lines, ∀ a b c, line = .label a b c → ¬(a = k ∧ b = ll ∧ ll ≠ 0)) →
      locToPc k ll (⟨sid, lines⟩ :: rest) =
        (locToPc k ll rest).map (· + (lines.filter fun x => !isLabelHOL x).length) := by
  intro lines
  induction lines with
  | nil =>
    intro rest _
    rw [locToPc.eq_2, if_neg (by omega)]
    cases locToPc k ll rest <;> rfl
  | cons line lines ih =>
    intro rest hok
    have tailOk : ∀ line ∈ lines, ∀ a b c, line = .label a b c → ¬(a = k ∧ b = ll ∧ ll ≠ 0) :=
      fun l m => hok l (List.mem_cons_of_mem _ m)
    cases line with
    | label a b c =>
      have no := hok _ List.mem_cons_self a b c rfl
      rw [locToPc.eq_3, if_neg (by omega)]
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
      rw [if_neg (by tauto)]
      simp only [isLabelHOL, if_true, List.filter_cons, Bool.not_true]
      exact ih rest tailOk
    | asm i e l =>
      rw [locToPc.eq_4, if_neg (by omega)]
      simp only [isLabelHOL, Bool.false_eq_true, if_false, Bool.false_and, List.filter_cons,
        Bool.not_false, if_true, List.length_cons, ih rest tailOk, Option.map_map]
      · rfl
      · intro _ _ _ h; cases h
    | labAsm i p e l =>
      rw [locToPc.eq_4, if_neg (by omega)]
      simp only [isLabelHOL, Bool.false_eq_true, if_false, Bool.false_and, List.filter_cons,
        Bool.not_false, if_true, List.length_cons, ih rest tailOk, Option.map_map]
      · rfl
      · intro _ _ _ h; cases h

/-- Complete original section-entry search past another section. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "loc_to_pc_skip_section"
  (words_as_type_indexed_bitvec)]
theorem locToPcSkipSection {width : Nat} [NeZero width] (n p : Nat) (xs : LabProgHOL width) :
    ∀ lines : List (LabLineHOL width), n ≠ p →
      locToPc n 0 (⟨p, lines⟩ :: xs) =
        match locToPc n 0 xs with
        | none => none
        | some k => some (k + (lines.filter fun x => !isLabelHOL x).length) := by
  intro lines hnp
  rw [locToPcSkip n 0 p (Ne.symm hnp) lines xs (fun _ _ _ _ _ _ h => h.2.2 rfl)]
  cases locToPc n 0 xs <;> rfl

/-- Complete original label-position law for code appended on the left. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "loc_to_pc_append2"
  (words_as_type_indexed_bitvec)]
theorem locToPcAppend2 {width : Nat} [NeZero width] :
    ∀ (k ll : Nat) (code code2 : LabProgHOL width) (pc : Nat),
      k ∉ code.map (·.sectionId) ∧ (∀ s ∈ code, LabProps.secLabelsOk s) ∧
        locToPc k ll code2 = some pc →
      locToPc k ll (code ++ code2) = some (pc + codeLength code) := by
  intro k ll code code2 pc ⟨notMem, ok, h⟩
  induction code with
  | nil => simpa [codeLength] using h
  | cons s rest ih =>
    obtain ⟨sid, lines⟩ := s
    simp only [List.map_cons, List.mem_cons, not_or] at notMem
    have secOk := ok _ List.mem_cons_self
    rw [List.cons_append, locToPcSkip k ll sid (Ne.symm notMem.1) lines (rest ++ code2) ?_,
      ih notMem.2 (fun s m => ok s (List.mem_cons_of_mem _ m))]
    · simp [codeLength]; omega
    · intro line member a b c eq
      subst eq
      have := secOk _ member
      simp only [LabProps.secLabelOk] at this
      omega

/-- Complete original installation law for code appended on the left. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed_append2"
  (words_as_type_indexed_bitvec)]
theorem codeInstalledAppend2 {width : Nat} [NeZero width] :
    ∀ (lines : List (LabLineHOL width)) (pc : Nat) (c1 c2 : LabProgHOL width) (k : Nat),
      k ∉ c1.map (·.sectionId) ∧ (∀ s ∈ c1, LabProps.secLabelsOk s) ∧
        (∀ line ∈ lines, LabProps.secLabelOk k line) ∧ codeInstalled pc lines c2 →
      codeInstalled (codeLength c1 + pc) lines (c1 ++ c2) := by
  intro lines
  induction lines with
  | nil => intros; trivial
  | cons x xs ih =>
    intro pc c1 c2 k ⟨notMem, ok, linesOk, h⟩
    rw [codeInstalled_cons] at h ⊢
    have tailOk : ∀ line ∈ xs, LabProps.secLabelOk k line :=
      fun l m => linesOk l (List.mem_cons_of_mem _ m)
    by_cases lab : isLabelHOL x = true
    · rw [if_pos lab] at h ⊢
      refine ⟨?_, ih pc c1 c2 k ⟨notMem, ok, tailOk, h.2⟩⟩
      cases x with
      | label l1 l2 _ =>
        have xOk := linesOk _ List.mem_cons_self
        simp only [LabProps.secLabelOk] at xOk
        have := locToPcAppend2 l1 l2 c1 c2 pc ⟨by rw [xOk.1]; exact notMem, ok, h.1⟩
        show locToPc l1 l2 (c1 ++ c2) = some (codeLength c1 + pc)
        rw [this, Nat.add_comm]
      | _ => trivial
    · rw [if_neg lab] at h ⊢
      refine ⟨?_, ?_⟩
      · exact asmFetchAuxSomeAppend2 pc c1 x c2 h.1
      · have := ih (pc + 1) c1 c2 k ⟨notMem, ok, tailOk, h.2⟩
        rwa [← Nat.add_assoc] at this

/-- Complete original `code_installed'` law for a leading label line. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed'_cons_label"
  (words_as_type_indexed_bitvec)]
theorem codeInstalled'ConsLabel {width : Nat} [NeZero width] (h : LabLineHOL width)
    (n : Nat) (xs : List (LabLineHOL width)) (other : LabProgHOL width) :
    ∀ (lines : List (LabLineHOL width)) (pos : Nat), isLabelHOL h = true →
      (codeInstalled' pos lines (⟨n, h :: xs⟩ :: other) ↔
        codeInstalled' pos lines (⟨n, xs⟩ :: other)) := by
  intro lines
  induction lines with
  | nil => intros; simp [codeInstalled']
  | cons x lines ih =>
    intro pos lab
    simp only [codeInstalled']
    by_cases lx : isLabelHOL x = true
    · simp only [lx, if_true]; exact ih pos lab
    · simp only [lx, Bool.false_eq_true, if_false, ih (pos + 1) lab, asmFetchAux.eq_3, lab,
        if_true]

/-- Complete original `code_installed'` law for a leading non-label line,
specialised as in the source to position zero. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed'_cons_non_label"
  (words_as_type_indexed_bitvec)]
theorem codeInstalled'ConsNonLabel {width : Nat} [NeZero width] (h : LabLineHOL width)
    (n : Nat) (xs : List (LabLineHOL width)) (other : LabProgHOL width)
    (lines : List (LabLineHOL width)) (nonLabel : ¬isLabelHOL h = true) :
    codeInstalled' 1 lines (⟨n, h :: xs⟩ :: other) ↔ codeInstalled' 0 lines (⟨n, xs⟩ :: other) := by
  suffices general : ∀ (lines : List (LabLineHOL width)) (pos : Nat),
      codeInstalled' (pos + 1) lines (⟨n, h :: xs⟩ :: other) ↔
        codeInstalled' pos lines (⟨n, xs⟩ :: other) from general lines 0
  intro lines
  induction lines with
  | nil => intros; simp [codeInstalled']
  | cons x lines ih =>
    intro pos
    simp only [codeInstalled']
    by_cases lx : isLabelHOL x = true
    · simp only [lx, if_true]; exact ih pos
    · simp only [lx, Bool.false_eq_true, if_false, ih (pos + 1), asmFetchAux.eq_3, nonLabel,
        Nat.add_one_ne_zero, Nat.add_sub_cancel]

/-- Complete original self-installation of a section prefix. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "code_installed'_simp"
  (words_as_type_indexed_bitvec)]
theorem codeInstalled'Simp {width : Nat} [NeZero width] (n : Nat) (rest : List (LabLineHOL width))
    (other : LabProgHOL width) :
    ∀ lines : List (LabLineHOL width), codeInstalled' 0 lines (⟨n, lines ++ rest⟩ :: other) := by
  intro lines
  induction lines with
  | nil => trivial
  | cons x lines ih =>
    simp only [codeInstalled', List.cons_append]
    by_cases lx : isLabelHOL x = true
    · simp only [lx, if_true]; exact (codeInstalled'ConsLabel x n _ other lines 0 lx).mpr ih
    · simp only [lx, Bool.false_eq_true, if_false]
      refine ⟨by rw [asmFetchAux.eq_3, if_neg lx, if_pos rfl], ?_⟩
      exact (codeInstalled'ConsNonLabel x n _ other lines lx).mpr ih

/-- Complete original label-correctness prefix law. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "labs_correct_append"
  (words_as_type_indexed_bitvec)]
theorem labsCorrectAppend {width : Nat} [NeZero width] (rest : List (LabLineHOL width))
    (code : LabProgHOL width) :
    ∀ (ls : List (LabLineHOL width)) (pc : Nat),
      labsCorrect pc (ls ++ rest) code → labsCorrect pc ls code := by
  intro ls
  induction ls with
  | nil => intros; trivial
  | cons x ls ih =>
    intro pc h
    simp only [List.cons_append, labsCorrect] at h ⊢
    by_cases lab : isLabelHOL x = true
    · rw [if_pos lab] at h ⊢; exact ⟨ih pc h.1, h.2⟩
    · rw [if_neg lab] at h ⊢; exact ih (pc + 1) h

open Flapjack.Compiler.Backend.LabProps.LabelSets in
/-- Searching a positive label through a section prefix that does not contain
it. Local factoring of `labs_correct_hd`. -/
theorem locToPcPrefix {width : Nat} [NeZero width] (n b sid : Nat) (hb : b ≠ 0)
    (rest : List (LabLineHOL width)) (code : LabProgHOL width) :
    ∀ extra : List (LabLineHOL width), (n, b) ∉ extractLabels extra →
      locToPc n b (⟨sid, extra ++ rest⟩ :: code) =
        (locToPc n b (⟨sid, rest⟩ :: code)).map (· + (extra.filter fun x => !isLabelHOL x).length) := by
  intro extra
  induction extra with
  | nil => intro _; simp
  | cons x extra ih =>
    intro notMem
    cases x with
    | label a c d =>
      simp only [extractLabels, List.mem_cons, not_or] at notMem
      rw [List.cons_append, locToPc.eq_3, if_neg (by omega)]
      have : ¬((a == n && c == b && b != 0) = true) := by
        intro h
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h
        obtain ⟨⟨ha, hc⟩, _⟩ := h
        exact notMem.1 (by rw [ha, hc])
      rw [if_neg this]
      simp only [isLabelHOL, if_true, List.filter_cons, Bool.not_true]
      exact ih notMem.2
    | asm i e l =>
      simp only [extractLabels] at notMem
      rw [List.cons_append, locToPc.eq_4, if_neg (by omega)]
      · simp only [isLabelHOL, Bool.false_eq_true, if_false, Bool.false_and, List.filter_cons,
          Bool.not_false, if_true, List.length_cons, ih notMem, Option.map_map]
        rfl
      · intro _ _ _ h; cases h
    | labAsm i p e l =>
      simp only [extractLabels] at notMem
      rw [List.cons_append, locToPc.eq_4, if_neg (by omega)]
      · simp only [isLabelHOL, Bool.false_eq_true, if_false, Bool.false_and, List.filter_cons,
          Bool.not_false, if_true, List.length_cons, ih notMem, Option.map_map]
        rfl
      · intro _ _ _ h; cases h

open Flapjack.Compiler.Backend.LabProps.LabelSets in
/-- Complete original label correctness of a section's own labels. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "labs_correct_hd"
  (words_as_type_indexed_bitvec)]
theorem labsCorrectHd {width : Nat} [NeZero width] (n : Nat) (code : LabProgHOL width) :
    ∀ (extra l : List (LabLineHOL width)),
      (extractLabels (extra ++ l)).Nodup ∧
        (∀ p ∈ extractLabels (extra ++ l), p.1 = n ∧ p.2 ≠ 0) →
      labsCorrect ((extra.filter fun x => !isLabelHOL x).length) l (⟨n, extra ++ l⟩ :: code) := by
  intro extra l
  induction l generalizing extra with
  | nil => intros; trivial
  | cons x l ih =>
    rintro ⟨nodup, every⟩
    have shifted := ih (extra ++ [x]) ⟨by simpa using nodup, by simpa using every⟩
    simp only [List.append_assoc, List.singleton_append] at shifted
    simp only [labsCorrect]
    by_cases lab : isLabelHOL x = true
    · rw [if_pos lab]
      refine ⟨by simpa [List.filter_append, lab] using shifted, ?_⟩
      cases x with
      | label a b c =>
        have hab := every (a, b) (by simp [extractLabels_append, extractLabels])
        simp only at hab
        obtain ⟨rfl, hb⟩ := hab
        have notMem : (a, b) ∉ extractLabels extra := by
          rw [extractLabels_append] at nodup
          simp only [extractLabels] at nodup
          intro m
          exact (List.nodup_append.mp nodup).2.2 _ m _ List.mem_cons_self rfl
        show locToPc a b (⟨a, extra ++ Line.label a b c :: l⟩ :: code) = _
        rw [locToPcPrefix a b a hb _ code extra notMem, locToPc.eq_3, if_neg (by omega)]
        simp [hb]
      | _ => simp [isLabelHOL] at lab
    · rw [if_neg lab]
      simpa [List.filter_append, lab] using shifted

end Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
