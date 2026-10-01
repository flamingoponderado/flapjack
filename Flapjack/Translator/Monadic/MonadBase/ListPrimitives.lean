import Flapjack.Translator.Monadic.MonadBase

namespace Flapjack.Translator.Monadic.MonadBase

/-- Literal list subscript primitive: empty or out-of-range input fails with
the caller's exception value. No fixed array or machine-width restriction. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Msub_def"]
def mSub {value exception : Type} (error : exception) (index : Nat) :
    List value → Exc value exception
  | [] => .failure error
  | head :: tail =>
    if index = 0 then .success head else mSub error (index - 1) tail

/-- Literal list update primitive, retaining the prefix only on recursive
success and propagating the recursive failure unchanged. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mupdate_def"]
def mUpdate {value exception : Type} (error : exception) (replacement : value)
    (index : Nat) : List value → Exc (List value) exception
  | [] => .failure error
  | head :: tail =>
    if index = 0 then .success (replacement :: tail)
    else match mUpdate error replacement (index - 1) tail with
      | .success updated => .success (head :: updated)
      | .failure error' => .failure error'

@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Msub_exn_eq"]
theorem mSubExnEq {value exception : Type} (values : List value) (index : Nat)
    (error : exception) (outOfRange : values.length ≤ index) :
    mSub error index values = .failure error := by
  induction values generalizing index with
  | nil => rfl
  | cons head tail ih =>
    cases index with
    | zero => simp only [List.length_cons] at outOfRange; omega
    | succ index =>
      have bounds : tail.length ≤ index := by simpa using outOfRange
      simpa [mSub] using ih index bounds

@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mupdate_exn_eq"]
theorem mUpdateExnEq {value exception : Type} (values : List value) (index : Nat)
    (replacement : value) (error : exception) (outOfRange : values.length ≤ index) :
    mUpdate error replacement index values = .failure error := by
  induction values generalizing index with
  | nil => rfl
  | cons head tail ih =>
    cases index with
    | zero => simp only [List.length_cons] at outOfRange; omega
    | succ index =>
      have bounds : tail.length ≤ index := by simpa using outOfRange
      simp [mUpdate, ih index bounds]

end Flapjack.Translator.Monadic.MonadBase
