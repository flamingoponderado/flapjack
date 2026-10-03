import Flapjack.HolRef
import Flapjack.Translator.Monadic.MonadBase
import Flapjack.Translator.Monadic.MonadBase.ListPrimitives
import Flapjack.Translator.Monadic.MonadBase.ArrayLength
import Flapjack.Misc.ListEl

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
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Msub_eq"]
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

end Flapjack.Translator.Monadic.MonadBase
