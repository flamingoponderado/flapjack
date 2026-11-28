module

public import Flapjack.HolRef
public import Flapjack.Translator.Monadic.MonadBase
public import Flapjack.Translator.Monadic.MonadBase.ListPrimitives
public import Flapjack.Translator.Monadic.MonadBase.ArrayLength
public import Flapjack.Misc.ListEl

@[expose] public section

/-!
# ml_monadBase fixed-array primitives

Ports of the fixed-array operations of
`cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml:123-214` that are
not in the canonical `ListPrimitives`/`ArrayLength` modules (`Msub`/`Mupdate`,
their failure equations and `Marray_length` live there). HOL
represents a fixed array in the monad state as a list, so the Lean carrier is
`List`; an out-of-range index fails with the supplied exception and leaves
the state unchanged, exactly as in HOL. The success theorem uses `holEl n l`;
under `n < LENGTH l` it agrees with the bounded `l[n]`.
-/

namespace Flapjack.Translator.Monadic.MonadBase

/-- Exact HOL `Msub_eq` (`ml_monadBaseScript.sml:131-138`):
`!l n e. n < LENGTH l ==> Msub e n l = M_success (EL n l)`, HOL `EL` as the
exact `holEl` (HOL types are inhabited, hence `[Nonempty value]`). -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Msub_eq"
  (total_function_inhabitants := [value])]
theorem msubEq {value exception : Type} [Nonempty value] :
    ∀ (l : List value) (n : Nat) (e : exception),
      n < l.length → mSub e n l = .success (holEl n l) := by
  intro l
  induction l with
  | nil => intro n e h; simp at h
  | cons x l ih =>
      intro n e h
      cases n with
      | zero => simp [mSub, holEl, holHd]
      | succ n =>
          simp only [mSub, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, holEl, List.tail_cons]
          exact ih n e (by simp at h; omega)

/-- Exact HOL `Mupdate_eq` (`ml_monadBaseScript.sml:163-170`); HOL `LUPDATE x n l`
is `l.set n x`. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mupdate_eq"]
theorem mupdateEq {value exception : Type} :
    ∀ (l : List value) (n : Nat) (x : value) (e : exception),
      n < l.length → mUpdate e x n l = .success (l.set n x) := by
  intro l
  induction l with
  | nil => intro n x e h; simp at h
  | cons y l ih =>
      intro n x e h
      cases n with
      | zero => simp [mUpdate]
      | succ n =>
          simp only [mUpdate, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
          rw [ih n x e (by simp at h; omega)]
          rfl

/-- HOL `Marray_sub` (`ml_monadBaseScript.sml:204-207`). -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Marray_sub_def"]
def arraySub {state value exception : Type} (getArr : state → List value)
    (e : exception) (n : Nat) : M state value exception :=
  fun s => (mSub e n (getArr s), s)

/-- HOL `Marray_update` (`ml_monadBaseScript.sml:209-214`): on failure the
state is unchanged. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Marray_update_def"]
def arrayUpdate {state value exception : Type} (getArr : state → List value)
    (setArr : List value → state → state) (e : exception) (n : Nat) (x : value) :
    M state Unit exception :=
  fun s =>
    match mUpdate e x n (getArr s) with
    | .success a => (.success (), setArr a s)
    | .failure e => (.failure e, s)

/-- Original `array_resize_def`: pad or truncate `a` to length `n` with `x`.
    HOL recurses on `n` while keeping `a` in the empty case, so the Lean
    definition is well-founded on `n`. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "array_resize_def"]
def arrayResize {α : Type} (n : Nat) (x : α) (a : List α) : List α :=
  if n = 0 then []
  else
    match a with
    | [] => x :: arrayResize (n - 1) x a
    | x' :: a' => x' :: arrayResize (n - 1) x a'
termination_by n

/-- Original `array_resize_eq`: resizing is a truncation followed by padding. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "array_resize_eq"]
theorem arrayResizeEq {α : Type} (a : List α) (n : Nat) (x : α) :
    arrayResize n x a = a.take n ++ List.replicate (n - a.length) x := by
  induction n generalizing a with
  | zero =>
      unfold arrayResize
      simp
  | succ n ih =>
      cases a with
      | nil =>
          unfold arrayResize
          simp [ih, List.replicate_succ]
      | cons y a =>
          unfold arrayResize
          simp [ih, List.take_succ_cons, Nat.succ_sub_succ_eq_sub]

/-- HOL `Marray_resize` (`ml_monadBaseScript.sml:216-220`). -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Marray_resize_def"]
def arrayResizeM {α β γ δ : Type} (getArr : α → List δ) (setArr : List δ → α → γ)
    (n : Nat) (x : δ) : α → Exc Unit β × γ :=
  fun s => (.success (), setArr (arrayResize n x (getArr s)) s)

end Flapjack.Translator.Monadic.MonadBase
