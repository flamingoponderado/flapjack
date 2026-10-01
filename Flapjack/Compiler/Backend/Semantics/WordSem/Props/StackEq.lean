import Flapjack.Compiler.Backend.Semantics.WordSem.State
import Flapjack.HolRef

/-!
# wordProps stack key/value equivalences

Counterpart of `cakeml/compiler/backend/semantics/wordPropsScript.sml:1793-2010`:
the "stack swap" relations `s_frame_val_eq`/`s_val_eq` (stacks agree except
for the keys of the GC-ed cut sets) and `s_frame_key_eq`/`s_key_eq` (stacks
agree except for those values), with reflexivity and the fact that both
together give equality. HOL booleans are rendered as propositions.
-/

namespace Flapjack

namespace WordSemStackEq

/-- Exact HOL `s_frame_val_eq_def` (`wordPropsScript.sml:1796-1802`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_val_eq_def"
  (words_as_type_indexed_bitvec)]
def sFrameValEq {width : Nat} [NeZero width] :
    WordSemStackFrame width → WordSemStackFrame width → Prop
  | .stackFrame n _ ls none, .stackFrame n' _ ls' none =>
      ls.map Prod.snd = ls'.map Prod.snd ∧ n = n'
  | .stackFrame n _ ls (some y), .stackFrame n' _ ls' (some y') =>
      ls.map Prod.snd = ls'.map Prod.snd ∧ y = y' ∧ n = n'
  | _, _ => False

/-- Exact HOL `s_val_eq_def` (`wordPropsScript.sml:1811-1816`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_def"
  (words_as_type_indexed_bitvec)]
def sValEq {width : Nat} [NeZero width] :
    List (WordSemStackFrame width) → List (WordSemStackFrame width) → Prop
  | [], [] => True
  | x :: xs, y :: ys => sValEq xs ys ∧ sFrameValEq x y
  | _, _ => False

/-- Exact HOL `s_frame_key_eq_def` (`wordPropsScript.sml:1819-1825`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_key_eq_def"
  (words_as_type_indexed_bitvec)]
def sFrameKeyEq {width : Nat} [NeZero width] :
    WordSemStackFrame width → WordSemStackFrame width → Prop
  | .stackFrame n ls0 ls none, .stackFrame n' ls0' ls' none =>
      ls.map Prod.fst = ls'.map Prod.fst ∧ ls0 = ls0' ∧ n = n'
  | .stackFrame n ls0 ls (some y), .stackFrame n' ls0' ls' (some y') =>
      ls.map Prod.fst = ls'.map Prod.fst ∧ y = y' ∧ ls0 = ls0' ∧ n = n'
  | _, _ => False

/-- Exact HOL `s_key_eq_def` (`wordPropsScript.sml:1834-1839`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_def"
  (words_as_type_indexed_bitvec)]
def sKeyEq {width : Nat} [NeZero width] :
    List (WordSemStackFrame width) → List (WordSemStackFrame width) → Prop
  | [], [] => True
  | x :: xs, y :: ys => sKeyEq xs ys ∧ sFrameKeyEq x y
  | _, _ => False

/-- Exact HOL `s_frame_val_eq_def2` (`wordPropsScript.sml:1804-1809`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_val_eq_def2"
  (words_as_type_indexed_bitvec)]
theorem sFrameValEqDef2 {width : Nat} [NeZero width] (n n' : Option Nat)
    (ls0 ls ls0' ls' : List (Nat × WordLocW width)) (y y' : Option (Nat × Nat × Nat)) :
    sFrameValEq (.stackFrame n ls0 ls y) (.stackFrame n' ls0' ls' y') ↔
      ls.map Prod.snd = ls'.map Prod.snd ∧ y = y' ∧ n = n' := by
  cases y <;> cases y' <;> simp [sFrameValEq]

/-- Exact HOL `s_frame_key_eq_def2` (`wordPropsScript.sml:1827-1832`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_key_eq_def2"
  (words_as_type_indexed_bitvec)]
theorem sFrameKeyEqDef2 {width : Nat} [NeZero width] (n n' : Option Nat)
    (ls0 ls ls0' ls' : List (Nat × WordLocW width)) (y y' : Option (Nat × Nat × Nat)) :
    sFrameKeyEq (.stackFrame n ls0 ls y) (.stackFrame n' ls0' ls' y') ↔
      ls.map Prod.fst = ls'.map Prod.fst ∧ y = y' ∧ ls0 = ls0' ∧ n = n' := by
  cases y <;> cases y' <;> simp [sFrameKeyEq]

/-- Exact HOL `s_frame_key_eq_refl` (`wordPropsScript.sml:1858-1863`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_key_eq_refl"
  (words_as_type_indexed_bitvec)]
theorem sFrameKeyEqRefl {width : Nat} [NeZero width] :
    ∀ ls : WordSemStackFrame width, sFrameKeyEq ls ls = True := by
  intro ls
  rcases ls with ⟨n, ls0, ls, y⟩
  exact eq_true ((sFrameKeyEqDef2 _ _ _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl, rfl⟩)

/-- Exact HOL `s_frame_val_eq_refl` (`wordPropsScript.sml:1865-1870`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_val_eq_refl"
  (words_as_type_indexed_bitvec)]
theorem sFrameValEqRefl {width : Nat} [NeZero width] :
    ∀ ls : WordSemStackFrame width, sFrameValEq ls ls = True := by
  intro ls
  rcases ls with ⟨n, ls0, ls, y⟩
  exact eq_true ((sFrameValEqDef2 _ _ _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩)

/-- Exact HOL `s_key_eq_refl` (`wordPropsScript.sml:1872-1878`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_refl"
  (words_as_type_indexed_bitvec)]
theorem sKeyEqRefl {width : Nat} [NeZero width] :
    ∀ ls : List (WordSemStackFrame width), sKeyEq ls ls = True := by
  intro ls
  induction ls with
  | nil => simp [sKeyEq]
  | cons x xs ih =>
      exact eq_true (show sKeyEq xs xs ∧ sFrameKeyEq x x from
        ⟨of_eq_true ih, of_eq_true (sFrameKeyEqRefl x)⟩)

/-- Exact HOL `s_val_eq_refl` (`wordPropsScript.sml:1880-1886`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_refl"
  (words_as_type_indexed_bitvec)]
theorem sValEqRefl {width : Nat} [NeZero width] :
    ∀ ls : List (WordSemStackFrame width), sValEq ls ls = True := by
  intro ls
  induction ls with
  | nil => simp [sValEq]
  | cons x xs ih =>
      exact eq_true (show sValEq xs xs ∧ sFrameValEq x x from
        ⟨of_eq_true ih, of_eq_true (sFrameValEqRefl x)⟩)

/-- Pairs agreeing on both projections are equal (list form). -/
private theorem listEqOfMapFstSnd {α β : Type} :
    ∀ (l l' : List (α × β)), l.map Prod.fst = l'.map Prod.fst →
      l.map Prod.snd = l'.map Prod.snd → l = l'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | (a, b) :: l, (a', b') :: l', h1, h2 => by
      simp only [List.map_cons, List.cons.injEq] at h1 h2
      rw [h1.1, h2.1, listEqOfMapFstSnd l l' h1.2 h2.2]

/-- Exact HOL `s_val_and_key_eq` (`wordPropsScript.sml:1983-1992`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_and_key_eq"
  (words_as_type_indexed_bitvec)]
theorem sValAndKeyEq {width : Nat} [NeZero width] :
    ∀ s t : List (WordSemStackFrame width), sValEq s t ∧ sKeyEq s t → s = t := by
  intro s
  induction s with
  | nil => intro t h; cases t with
    | nil => rfl
    | cons _ _ => exact absurd h.1 (by simp [sValEq])
  | cons x xs ih =>
      intro t h
      cases t with
      | nil => exact absurd h.1 (by simp [sValEq])
      | cons y ys =>
          obtain ⟨⟨hv, hfv⟩, hk, hfk⟩ := h
          rw [ih ys ⟨hv, hk⟩]
          rcases x with ⟨n, ls0, ls, hx⟩
          rcases y with ⟨n', ls0', ls', hy⟩
          rw [sFrameValEqDef2] at hfv
          rw [sFrameKeyEqDef2] at hfk
          obtain ⟨hsnd, rfl, rfl⟩ := hfv
          obtain ⟨hfst, -, rfl, -⟩ := hfk
          rw [listEqOfMapFstSnd ls ls' hfst hsnd]

end WordSemStackEq

end Flapjack
