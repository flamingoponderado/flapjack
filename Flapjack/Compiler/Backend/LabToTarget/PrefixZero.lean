import Flapjack.Compiler.Backend.LabToTarget.LineLength
import Flapjack.Compiler.Backend.LabSem.Classifier
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Full original quantified prefix invariant. The original n-bound conjunct
is curried so each m<=n observation has the checked bound m<length.
No total HOL EL or out-of-range default is used or specified. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def labelPrefixZero {width : Nat} [NeZero width] (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) : Prop :=
  ∀ n, ∀ hn : n < ls.length,
    (∀ m, ∀ hm : m ≤ n, isLabelHOL (ls[m]'(Nat.lt_of_le_of_lt hm hn)) = true) →
    ∀ m, ∀ hm : m ≤ n, lineLen (ls[m]'(Nat.lt_of_le_of_lt hm hn)) = 0

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def secLabelPrefixZero {width : Nat} [NeZero width] (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) : Prop :=
  labelPrefixZero sec.lines

/-- Flapjack-specific reduction of the full bounded-index predicate at a label. -/
private theorem prefixLabel {width : Nat} [NeZero width]
    (x : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) (xs : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (hx : isLabelHOL x = true) :
    labelPrefixZero (x :: xs) ↔ lineLen x = 0 ∧ labelPrefixZero xs := by
  constructor
  · intro h
    have hzero := h 0 (by simp) (by
      intro m hm
      have he : m = 0 := by omega
      subst m
      simpa using hx) 0 (by omega)
    refine ⟨by simpa using hzero, ?_⟩
    intro n hn hall m hm
    have hfull : ∀ k, ∀ hk : k ≤ n + 1,
        isLabelHOL ((x :: xs)[k]'(by simp; omega)) = true := by
      intro k hk
      cases k with
      | zero => simpa using hx
      | succ k => simpa using hall k (by omega)
    have hh := h (n + 1) (by simp; omega) hfull (m + 1) (by omega)
    simpa using hh
  · rintro ⟨hzero,htail⟩ n hn hall m hm
    cases m with
    | zero => simpa using hzero
    | succ m =>
      cases n with
      | zero => omega
      | succ n =>
        have hn' : n < xs.length := by simp only [List.length_cons] at hn; omega
        have hlabels : ∀ k, ∀ hk : k ≤ n,
            isLabelHOL (xs[k]'(Nat.lt_of_le_of_lt hk hn')) = true := by
          intro k hk
          simpa using hall (k + 1) (by omega)
        simpa using htail n hn' hlabels m (by omega)

/-- Flapjack-specific reduction: a nonlabel head makes every all-label-prefix antecedent false. -/
private theorem prefixNonlabel {width : Nat} [NeZero width]
    (x : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) (xs : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (hx : isLabelHOL x ≠ true) :
    labelPrefixZero (x :: xs) := by
  intro n hn hall m hm
  have hh := hall 0 (by omega)
  simp only [List.getElem_cons_zero] at hh
  exact False.elim (hx hh)

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem labelPrefixZero_cons {width : Nat} [NeZero width]
    (l1 l2 len : Nat) (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (a : AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (b : List (BitVec 8)) (c : Nat)
    (d : AsmWithLab HolCmp (HolRegImm width) MlString) (e : BitVec width)
    (f : List (BitVec 8)) (g : Nat) :
    (labelPrefixZero (.label l1 l2 len :: ls) ↔ len = 0 ∧ labelPrefixZero ls) ∧
    (labelPrefixZero (.asm a b c :: ls) ↔ True) ∧
    (labelPrefixZero (.labAsm d e f g :: ls) ↔ True) := by
  refine ⟨?_,?_,?_⟩
  · simpa [lineLen] using prefixLabel (.label l1 l2 len) ls rfl
  · exact iff_true_intro (prefixNonlabel (.asm a b c) ls (by simp [isLabelHOL]))
  · exact iff_true_intro (prefixNonlabel (.labAsm d e f g) ls (by simp [isLabelHOL]))

/-- Flapjack-specific empty-case arithmetic, no out-of-range observation. -/
private theorem prefixNil {width : Nat} [NeZero width] :
    labelPrefixZero ([] : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) := by
  intro n hn
  simp at hn

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem labelPrefixZero_append {width : Nat} [NeZero width]
    (l1 l2 : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    labelPrefixZero l1 ∧ labelPrefixZero l2 → labelPrefixZero (l1 ++ l2) := by
  induction l1 with
  | nil => rintro ⟨_,h⟩; simpa using h
  | cons x xs ih =>
    rintro ⟨h1,h2⟩
    cases x with
    | label k1 k2 n =>
      have h := (prefixLabel (.label k1 k2 n) xs rfl).mp h1
      apply (prefixLabel (.label k1 k2 n) (xs ++ l2) rfl).mpr
      exact ⟨h.1,ih ⟨h.2,h2⟩⟩
    | asm a bs n => exact prefixNonlabel (.asm a bs n) (xs ++ l2) (by simp [isLabelHOL])
    | labAsm a w bs n => exact prefixNonlabel (.labAsm a w bs n) (xs ++ l2) (by simp [isLabelHOL])

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem labelPrefixZero_append_nonlabel {width : Nat} [NeZero width]
    (l1 l2 : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    labelPrefixZero l1 ∧ (∃ line ∈ l1, isLabelHOL line ≠ true) →
    labelPrefixZero (l1 ++ l2) := by
  induction l1 with
  | nil => rintro ⟨_,h⟩; simp at h
  | cons x xs ih =>
    rintro ⟨h1,h2⟩
    cases x with
    | label k1 k2 n =>
      have h := (prefixLabel (.label k1 k2 n) xs rfl).mp h1
      have ht : ∃ line ∈ xs, isLabelHOL line ≠ true := by
        rcases h2 with ⟨line,hm,hnot⟩
        rcases List.mem_cons.mp hm with heq | hmem
        · subst line
          simp [isLabelHOL] at hnot
        · exact ⟨line,hmem,hnot⟩
      apply (prefixLabel (.label k1 k2 n) (xs ++ l2) rfl).mpr
      exact ⟨h.1,ih ⟨h.2,ht⟩⟩
    | asm a bs n => exact prefixNonlabel (.asm a bs n) (xs ++ l2) (by simp [isLabelHOL])
    | labAsm a w bs n => exact prefixNonlabel (.labAsm a w bs n) (xs ++ l2) (by simp [isLabelHOL])

/-- Flapjack-specific public empty-case reduction of the bounded predicate. -/
@[simp] theorem labelPrefixZero_nil {width : Nat} [NeZero width] :
    labelPrefixZero ([] : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) := prefixNil

/-- Flapjack-specific uniform constructor reduction, derived from the full
bounded-index definition; the original constructor conjunction is tagged above. -/
@[simp] theorem labelPrefixZero_cons_iff {width : Nat} [NeZero width]
    (x : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) (xs : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    labelPrefixZero (x :: xs) ↔ (isLabelHOL x = true → lineLen x = 0 ∧ labelPrefixZero xs) := by
  cases x with
  | label k1 k2 n => simpa [isLabelHOL,lineLen] using prefixLabel (.label k1 k2 n) xs rfl
  | asm a bs n => simpa [isLabelHOL] using iff_true_intro (prefixNonlabel (.asm a bs n) xs (by simp [isLabelHOL]))
  | labAsm a w bs n => simpa [isLabelHOL] using iff_true_intro (prefixNonlabel (.labAsm a w bs n) xs (by simp [isLabelHOL]))

end Flapjack.Compiler.Backend.LabToTarget
