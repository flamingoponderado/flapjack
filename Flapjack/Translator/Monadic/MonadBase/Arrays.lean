import Flapjack.HolRef
import Flapjack.Translator.Monadic.MonadBase

/-!
# ml_monadBase fixed-array primitives

Ports of the fixed-array operations of
`cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml:123-214`. HOL
represents a fixed array in the monad state as a list, so the Lean carrier is
`List`; an out-of-range index fails with the supplied exception and leaves
the state unchanged, exactly as in HOL. HOL `EL n l` under `n < LENGTH l` is
the bounded `l[n]`.
-/

namespace Flapjack.Translator.Monadic.MonadBase

/-- HOL `Msub` (`ml_monadBaseScript.sml:124-129`). -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Msub_def"]
def msub {value exception : Type} (e : exception) : Nat → List value → Exc value exception
  | _, [] => .failure e
  | n, x :: l' => if n = 0 then .success x else msub e (n - 1) l'

/-- HOL `Msub_eq` (`ml_monadBaseScript.sml:131-138`).

Provisional and untagged: this ports HOL `Msub_eq` but its statement uses HOL `EL`
(rendered by the untagged total `holEl`, or its bounded form), whose HOL
`listScript` provenance is pending review (bead flapjack-pxn.18.5.15.3.38.1).
Restore the `@[hol]` tag once that review is accepted. -/
theorem msubEq {value exception : Type} :
    ∀ (l : List value) (n : Nat) (e : exception) (h : n < l.length),
      msub e n l = .success (l[n]'h) := by
  intro l
  induction l with
  | nil => intro n e h; simp at h
  | cons x l ih =>
      intro n e h
      cases n with
      | zero => simp [msub]
      | succ n =>
          simp only [msub, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, List.getElem_cons_succ]
          exact ih n e (by simp at h; omega)

/-- Exact HOL `Msub_exn_eq` (`ml_monadBaseScript.sml:140-147`). -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Msub_exn_eq"]
theorem msubExnEq {value exception : Type} :
    ∀ (l : List value) (n : Nat) (e : exception), n ≥ l.length → msub e n l = .failure e := by
  intro l
  induction l with
  | nil => intro n e _; simp [msub]
  | cons x l ih =>
      intro n e h
      cases n with
      | zero => simp at h
      | succ n =>
          simp only [msub, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
          exact ih n e (by simp at h; omega)

/-- HOL `Mupdate` (`ml_monadBaseScript.sml:150-161`): an inner failure is
returned unchanged. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mupdate_def"]
def mupdate {value exception : Type} (e : exception) (x : value) :
    Nat → List value → Exc (List value) exception
  | _, [] => .failure e
  | n, x' :: l' =>
      if n = 0 then .success (x :: l')
      else
        match mupdate e x (n - 1) l' with
        | .success l'' => .success (x' :: l'')
        | other => other

/-- Exact HOL `Mupdate_eq` (`ml_monadBaseScript.sml:163-170`); HOL `LUPDATE x n l`
is `l.set n x`. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mupdate_eq"]
theorem mupdateEq {value exception : Type} :
    ∀ (l : List value) (n : Nat) (x : value) (e : exception),
      n < l.length → mupdate e x n l = .success (l.set n x) := by
  intro l
  induction l with
  | nil => intro n x e h; simp at h
  | cons y l ih =>
      intro n x e h
      cases n with
      | zero => simp [mupdate]
      | succ n =>
          simp only [mupdate, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
          rw [ih n x e (by simp at h; omega)]
          rfl

/-- Exact HOL `Mupdate_exn_eq` (`ml_monadBaseScript.sml:172-179`). -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mupdate_exn_eq"]
theorem mupdateExnEq {value exception : Type} :
    ∀ (l : List value) (n : Nat) (x : value) (e : exception),
      n ≥ l.length → mupdate e x n l = .failure e := by
  intro l
  induction l with
  | nil => intro n x e _; simp [mupdate]
  | cons y l ih =>
      intro n x e h
      cases n with
      | zero => simp at h
      | succ n =>
          simp only [mupdate, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
          rw [ih n x e (by simp at h; omega)]

/-- HOL `Marray_length` (`ml_monadBaseScript.sml:199-202`). -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Marray_length_def"]
def arrayLength {state value exception : Type} (getArr : state → List value) :
    M state Nat exception :=
  fun s => (.success (getArr s).length, s)

/-- HOL `Marray_sub` (`ml_monadBaseScript.sml:204-207`). -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Marray_sub_def"]
def arraySub {state value exception : Type} (getArr : state → List value)
    (e : exception) (n : Nat) : M state value exception :=
  fun s => (msub e n (getArr s), s)

/-- HOL `Marray_update` (`ml_monadBaseScript.sml:209-214`): on failure the
state is unchanged. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Marray_update_def"]
def arrayUpdate {state value exception : Type} (getArr : state → List value)
    (setArr : List value → state → state) (e : exception) (n : Nat) (x : value) :
    M state Unit exception :=
  fun s =>
    match mupdate e x n (getArr s) with
    | .success a => (.success (), setArr a s)
    | .failure e => (.failure e, s)

end Flapjack.Translator.Monadic.MonadBase
