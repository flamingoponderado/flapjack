import Flapjack.HolRef
import Lean.Elab.Tactic.Omega

namespace Flapjack.Compiler.Backend.WordToStack

/-- Literal original proof-side list update specification. Native List.set
matches HOL LUPDATE including ignored out-of-range writes. This HOL proof
utility has no compiler operation or production duplicate to route. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "list_LUPDATE_def"]
def listUpdate {α : Type} : List α → Nat → List α → List α
  | [], _, ys => ys
  | x :: xs, n, ys => listUpdate xs (n + 1) (ys.set n x)

/-- Full original length preservation. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LENGTH_list_LUPDATE"]
theorem lengthListUpdate {α : Type} (xs : List α) (n : Nat) (ys : List α) :
    (listUpdate xs n ys).length = ys.length := by
  induction xs generalizing n ys with
  | nil => rfl
  | cons x xs ih => simp [listUpdate, ih]

/-- Full original take transport without an index or length bound. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "TAKE_list_LUPDATE"]
theorem takeListUpdate {α : Type} (ys : List α) (xs : List α) (n i : Nat) :
    (listUpdate ys i xs).take n = listUpdate ys i (xs.take n) := by
  induction ys generalizing xs i with
  | nil => rfl
  | cons y ys ih => simp only [listUpdate, ih, List.take_set]

/-- Full original optional lookup preservation beyond the update interval.
LLOOKUP is HOL oEL, so no total EL or inhabited payload default is used. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LLOOKUP_list_LUPDATE_IGNORE"]
theorem lookupListUpdateIgnore {α : Type} (xs : List α) (i n : Nat) (ys : List α)
    (h : i + xs.length ≤ n) :
    (listUpdate xs i ys)[n]? = ys[n]? := by
  induction xs generalizing i ys with
  | nil => rfl
  | cons x xs ih =>
    rw [listUpdate, ih (i + 1) (ys.set i x) (by simp only [List.length_cons] at h; omega)]
    exact List.getElem?_set_ne (by simp only [List.length_cons] at h; omega)

/-- Full original drop transport with exactly the original offset bound. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DROP_list_LUPDATE"]
theorem dropListUpdate {α : Type} (ys : List α) (n m : Nat) (xs : List α)
    (h : n ≤ m) :
    (listUpdate ys m xs).drop n = listUpdate ys (m - n) (xs.drop n) := by
  induction ys generalizing m xs with
  | nil => rfl
  | cons y ys ih =>
    rw [listUpdate, ih (m + 1) (xs.set m y) (by omega)]
    rw [List.drop_set, if_neg (by omega)]
    have heq : m + 1 - n = (m - n) + 1 := by omega
    rw [heq]
    rfl

/-- Full original suffix preservation beyond the update interval. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DROP_list_LUPDATE_IGNORE"]
theorem dropListUpdateIgnore {α : Type} (xs : List α) (i : Nat) (ys : List α) (n : Nat)
    (h : xs.length + i ≤ n) :
    (listUpdate xs i ys).drop n = ys.drop n := by
  induction xs generalizing i ys with
  | nil => rfl
  | cons x xs ih =>
    rw [listUpdate, ih (i + 1) (ys.set i x) (by simp only [List.length_cons] at h; omega)]
    exact List.drop_set_of_lt (by simp only [List.length_cons] at h; omega)

/-- Full original empty-destination preservation. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "list_LUPDATE_NIL"]
theorem listUpdateNil {α : Type} (xs : List α) (i : Nat) :
    listUpdate xs i [] = [] := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => simp [listUpdate, ih]

/-- Full original single-update take/drop decomposition, including out-of-range indices. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LUPDATE_TAKE_LEMMA"]
theorem singleUpdateTakeDrop {α : Type} (xs : List α) (n : Nat) (w : α) :
    xs.set n w = xs.take n ++ (xs.drop n).set 0 w := by
  induction n generalizing xs with
  | zero => simp
  | succ n ih =>
    cases xs with
    | nil => simp
    | cons x xs => simp [ih]

/-- Flapjack structural helper for native list update under an unchanged head;
no separate HOL declaration is attached to this induction step. -/
private theorem listUpdateConsSucc {α : Type} (xs : List α) (n : Nat) (y : α) (ys : List α) :
    listUpdate xs (n + 1) (y :: ys) = y :: listUpdate xs n ys := by
  induction xs generalizing n ys with
  | nil => rfl
  | cons x xs ih => simp [listUpdate, ih, Nat.add_assoc]

/-- Full original arbitrary sequential-update take/drop reconstruction. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "list_LUPDATE_TAKE_DROP"]
theorem listUpdateTakeDrop {α : Type} (xs ys : List α) (n : Nat) :
    listUpdate xs n ys = ys.take n ++ listUpdate xs 0 (ys.drop n) := by
  induction n generalizing ys with
  | zero => simp
  | succ n ih =>
    cases ys with
    | nil => simp [listUpdateNil]
    | cons y ys => simp [listUpdateConsSucc, ih]

/-- Full original zero-offset update on a nonempty destination. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "list_LUPDATE_0_CONS"]
theorem listUpdateZeroCons {α : Type} (xs : List α) (x : α) (ys : List α) (y : α) :
    listUpdate (x :: xs) 0 (y :: ys) = x :: listUpdate xs 0 ys := by
  simp only [listUpdate, List.set_cons_zero]
  exact listUpdateConsSucc xs 0 x ys

/-- Full original prefix overwrite for equal-length source/destination prefixes. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "list_LUPDATE_APPEND"]
theorem listUpdateAppend {α : Type} (xs ys zs : List α) (h : xs.length = ys.length) :
    listUpdate xs 0 (ys ++ zs) = xs ++ zs := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [listUpdate]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.cons_append, listUpdateZeroCons]
      rw [ih ys (by simpa using h)]

end Flapjack.Compiler.Backend.WordToStack
