import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackSwap

/-!
# wordProps stack list lemmas

Counterpart of `cakeml/compiler/backend/semantics/wordPropsScript.sml:2159-2315`:
`s_val_eq`/`s_key_eq` under append, reverse, take, `LASTN` and tail, the
`LASTN` frame-shape transport lemmas, and stack-size invariance. HOL `LASTN`
is the reviewed `wordSemLastN` rendering.
-/

namespace Flapjack

namespace WordSemStackEq

namespace StackListsWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field port. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end StackListsWitnesses

open StackListsWitnesses

/-- Exact HOL `s_val_eq_APPEND` (`wordPropsScript.sml:2159-2164`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_APPEND"
  (words_as_type_indexed_bitvec)]
theorem sValEqAppend {width : Nat} [NeZero width] :
    ∀ s t x y : List (WordSemStackFrame width),
      sValEq s t ∧ sValEq x y → sValEq (s ++ x) (t ++ y) := by
  intro s
  induction s with
  | nil => rintro t x y ⟨h1, h2⟩; cases t <;> simp_all [sValEq]
  | cons a s ih =>
      rintro t x y ⟨h1, h2⟩
      cases t with
      | nil => exact absurd h1 (by simp [sValEq])
      | cons b t => exact ⟨ih t x y ⟨h1.1, h2⟩, h1.2⟩

/-- Exact HOL `s_val_eq_REVERSE` (`wordPropsScript.sml:2166-2171`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_REVERSE"
  (words_as_type_indexed_bitvec)]
theorem sValEqReverse {width : Nat} [NeZero width] :
    ∀ s t : List (WordSemStackFrame width), sValEq s t → sValEq s.reverse t.reverse := by
  intro s
  induction s with
  | nil => intro t h; cases t <;> simp_all [sValEq]
  | cons a s ih =>
      intro t h
      cases t with
      | nil => exact absurd h (by simp [sValEq])
      | cons b t =>
          simp only [List.reverse_cons]
          exact sValEqAppend _ _ _ _ ⟨ih t h.1, ⟨trivial, h.2⟩⟩

/-- Exact HOL `s_val_eq_TAKE` (`wordPropsScript.sml:2173-2178`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_TAKE"
  (words_as_type_indexed_bitvec)]
theorem sValEqTake {width : Nat} [NeZero width] :
    ∀ (s t : List (WordSemStackFrame width)) (n : Nat), sValEq s t →
      sValEq (s.take n) (t.take n) := by
  intro s
  induction s with
  | nil => intro t n h; cases t <;> simp_all [sValEq]
  | cons a s ih =>
      intro t n h
      cases t with
      | nil => exact absurd h (by simp [sValEq])
      | cons b t =>
          cases n with
          | zero => simp [sValEq]
          | succ n => exact ⟨ih t n h.1, h.2⟩

/-- Exact HOL `s_val_eq_LASTN` (`wordPropsScript.sml:2180-2191`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_LASTN"
  (words_as_type_indexed_bitvec)]
theorem sValEqLastN {width : Nat} [NeZero width] :
    ∀ (s t : List (WordSemStackFrame width)) (n : Nat), sValEq s t →
      sValEq (wordSemLastN n s) (wordSemLastN n t) := by
  intro s t n h
  unfold wordSemLastN
  exact sValEqReverse _ _ (sValEqTake _ _ n (sValEqReverse s t h))

/-- Exact HOL `s_key_eq_APPEND` (`wordPropsScript.sml:2193-2198`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_APPEND"
  (words_as_type_indexed_bitvec)]
theorem sKeyEqAppend {width : Nat} [NeZero width] :
    ∀ s t x y : List (WordSemStackFrame width),
      sKeyEq s t ∧ sKeyEq x y → sKeyEq (s ++ x) (t ++ y) := by
  intro s
  induction s with
  | nil => rintro t x y ⟨h1, h2⟩; cases t <;> simp_all [sKeyEq]
  | cons a s ih =>
      rintro t x y ⟨h1, h2⟩
      cases t with
      | nil => exact absurd h1 (by simp [sKeyEq])
      | cons b t => exact ⟨ih t x y ⟨h1.1, h2⟩, h1.2⟩

/-- Exact HOL `s_key_eq_REVERSE` (`wordPropsScript.sml:2200-2205`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_REVERSE"
  (words_as_type_indexed_bitvec)]
theorem sKeyEqReverse {width : Nat} [NeZero width] :
    ∀ s t : List (WordSemStackFrame width), sKeyEq s t → sKeyEq s.reverse t.reverse := by
  intro s
  induction s with
  | nil => intro t h; cases t <;> simp_all [sKeyEq]
  | cons a s ih =>
      intro t h
      cases t with
      | nil => exact absurd h (by simp [sKeyEq])
      | cons b t =>
          simp only [List.reverse_cons]
          exact sKeyEqAppend _ _ _ _ ⟨ih t h.1, ⟨trivial, h.2⟩⟩

/-- Exact HOL `s_key_eq_TAKE` (`wordPropsScript.sml:2207-2212`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_TAKE"
  (words_as_type_indexed_bitvec)]
theorem sKeyEqTake {width : Nat} [NeZero width] :
    ∀ (s t : List (WordSemStackFrame width)) (n : Nat), sKeyEq s t →
      sKeyEq (s.take n) (t.take n) := by
  intro s
  induction s with
  | nil => intro t n h; cases t <;> simp_all [sKeyEq]
  | cons a s ih =>
      intro t n h
      cases t with
      | nil => exact absurd h (by simp [sKeyEq])
      | cons b t =>
          cases n with
          | zero => simp [sKeyEq]
          | succ n => exact ⟨ih t n h.1, h.2⟩

/-- Exact HOL `s_key_eq_LASTN` (`wordPropsScript.sml:2214-2225`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_LASTN"
  (words_as_type_indexed_bitvec)]
theorem sKeyEqLastN {width : Nat} [NeZero width] :
    ∀ (s t : List (WordSemStackFrame width)) (n : Nat), sKeyEq s t →
      sKeyEq (wordSemLastN n s) (wordSemLastN n t) := by
  intro s t n h
  unfold wordSemLastN
  exact sKeyEqReverse _ _ (sKeyEqTake _ _ n (sKeyEqReverse s t h))

/-- Exact HOL `s_key_eq_tail` (`wordPropsScript.sml:2227-2231`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_tail"
  (words_as_type_indexed_bitvec)]
theorem sKeyEqTail {width : Nat} [NeZero width] :
    ∀ (a : WordSemStackFrame width) (b : List (WordSemStackFrame width))
      (c : WordSemStackFrame width) (d : List (WordSemStackFrame width)),
      sKeyEq (a :: b) (c :: d) → sKeyEq b d :=
  fun _ _ _ _ h => h.1

/-- Exact HOL `s_val_eq_tail` (`wordPropsScript.sml:2233-2237`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_tail"
  (words_as_type_indexed_bitvec)]
theorem sValEqTail {width : Nat} [NeZero width] :
    ∀ (a : WordSemStackFrame width) (b : List (WordSemStackFrame width))
      (c : WordSemStackFrame width) (d : List (WordSemStackFrame width)),
      sValEq (a :: b) (c :: d) → sValEq b d :=
  fun _ _ _ _ h => h.1

/-- Exact HOL `s_key_eq_LASTN_exists` (`wordPropsScript.sml:2239-2252`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_LASTN_exists"
  (words_as_type_indexed_bitvec)]
theorem sKeyEqLastNExists {width : Nat} [NeZero width] :
    ∀ (s t : List (WordSemStackFrame width)) (n : Nat) (m : Option Nat)
      (e0 e : List (Nat × WordLocW width)) (y : Nat × Nat × Nat)
      (xs : List (WordSemStackFrame width)),
      sKeyEq s t ∧ wordSemLastN n s = .stackFrame m e0 e (some y) :: xs →
      ∃ e' ls, wordSemLastN n t = .stackFrame m e0 e' (some y) :: ls ∧
        e'.map Prod.fst = e.map Prod.fst ∧ sKeyEq xs ls := by
  rintro s t n m e0 e y xs ⟨h, hl⟩
  have hk := sKeyEqLastN s t n h
  rw [hl] at hk
  cases ht : wordSemLastN n t with
  | nil => rw [ht] at hk; exact absurd hk (by simp [sKeyEq])
  | cons fr ls =>
      rw [ht] at hk
      rcases fr with ⟨m', e0', e', y'⟩
      have hf := hk.2
      rw [sFrameKeyEqDef2] at hf
      obtain ⟨h1, rfl, rfl, rfl⟩ := hf
      exact ⟨e', ls, rfl, h1.symm, hk.1⟩

/-- Exact HOL `s_val_eq_LASTN_exists` (`wordPropsScript.sml:2254-2267`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_LASTN_exists"
  (words_as_type_indexed_bitvec)]
theorem sValEqLastNExists {width : Nat} [NeZero width] :
    ∀ (s t : List (WordSemStackFrame width)) (n : Nat) (m : Option Nat)
      (e0 e : List (Nat × WordLocW width)) (y : Nat × Nat × Nat)
      (xs : List (WordSemStackFrame width)),
      sValEq s t ∧ wordSemLastN n s = .stackFrame m e0 e (some y) :: xs →
      ∃ e0' e' ls, wordSemLastN n t = .stackFrame m e0' e' (some y) :: ls ∧
        e'.map Prod.snd = e.map Prod.snd ∧ sValEq xs ls := by
  rintro s t n m e0 e y xs ⟨h, hl⟩
  have hv := sValEqLastN s t n h
  rw [hl] at hv
  cases ht : wordSemLastN n t with
  | nil => rw [ht] at hv; exact absurd hv (by simp [sValEq])
  | cons fr ls =>
      rw [ht] at hv
      rcases fr with ⟨m', e0', e', y'⟩
      have hf := hv.2
      rw [sFrameValEqDef2] at hf
      obtain ⟨h1, rfl, rfl⟩ := hf
      exact ⟨e0', e', ls, rfl, h1.symm, hv.1⟩

/-- Exact HOL `LASTN_LENGTH_cond` (`wordPropsScript.sml:2269-2273`); HOL's
element type is generic. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "LASTN_LENGTH_cond"]
theorem lastNLengthCond {α : Type} : ∀ (n : Nat) (xs : List α), n = xs.length →
    wordSemLastN n xs = xs := by
  intro n xs h
  subst h
  unfold wordSemLastN
  rw [List.take_of_length_le (by simp), List.reverse_reverse]

/-- Exact HOL `handler_eq` (`wordPropsScript.sml:2275-2279`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "handler_eq"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem handlerEq {width : Nat} [NeZero width] {C F : Type}
    (x : WordSemStateFiniteExact width C F) : { x with handler := x.handler } = x := rfl

private theorem stackSizeCons {width : Nat} [NeZero width] (fr : WordSemStackFrame width)
    (rest : List (WordSemStackFrame width)) :
    wordSemStackSize (fr :: rest) =
      wordSemOptionAdd (wordSemStackSizeFrame fr) (wordSemStackSize rest) := rfl

/-- Exact HOL `s_val_eq_stack_size` (`wordPropsScript.sml:2281-2292`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_stack_size"
  (words_as_type_indexed_bitvec)]
theorem sValEqStackSize {width : Nat} [NeZero width] :
    ∀ xs ys : List (WordSemStackFrame width), sValEq xs ys →
      wordSemStackSize xs = wordSemStackSize ys := by
  intro xs
  induction xs with
  | nil => intro ys h; cases ys <;> simp_all [sValEq]
  | cons a xs ih =>
      intro ys h
      cases ys with
      | nil => exact absurd h (by simp [sValEq])
      | cons b ys =>
          rw [stackSizeCons, stackSizeCons, ih ys h.1]
          rcases a with ⟨n, l0, l, ha⟩
          rcases b with ⟨n', l0', l', hb⟩
          have hf := h.2
          rw [sFrameValEqDef2] at hf
          obtain ⟨-, rfl, rfl⟩ := hf
          cases ha <;> rfl

/-- Exact HOL `s_key_eq_stack_size` (`wordPropsScript.sml:2295-2304`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_stack_size"
  (words_as_type_indexed_bitvec)]
theorem sKeyEqStackSize {width : Nat} [NeZero width] :
    ∀ xs ys : List (WordSemStackFrame width), sKeyEq xs ys →
      wordSemStackSize xs = wordSemStackSize ys := by
  intro xs
  induction xs with
  | nil => intro ys h; cases ys <;> simp_all [sKeyEq]
  | cons a xs ih =>
      intro ys h
      cases ys with
      | nil => exact absurd h (by simp [sKeyEq])
      | cons b ys =>
          rw [stackSizeCons, stackSizeCons, ih ys h.1]
          rcases a with ⟨n, l0, l, ha⟩
          rcases b with ⟨n', l0', l', hb⟩
          have hf := h.2
          rw [sFrameKeyEqDef2] at hf
          obtain ⟨-, rfl, -, rfl⟩ := hf
          cases ha <;> rfl

/-- Exact HOL `s_val_append_eq_stack_size` (`wordPropsScript.sml:2306-2312`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_append_eq_stack_size"
  (words_as_type_indexed_bitvec)]
theorem sValAppendEqStackSize {width : Nat} [NeZero width] :
    ∀ (stk stk' : List (WordSemStackFrame width)) (frm : WordSemStackFrame width),
      sValEq stk stk' → wordSemStackSize (frm :: stk) = wordSemStackSize (frm :: stk') := by
  intro stk stk' frm h
  rw [stackSizeCons, stackSizeCons, sValEqStackSize stk stk' h]

end WordSemStackEq

end Flapjack
