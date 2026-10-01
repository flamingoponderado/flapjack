import Flapjack.HolRef

namespace Flapjack.Translator.Monadic.MonadBase

@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "exc"]
inductive Exc (value exception : Type) where
  | success (result : value)
  | failure (error : exception)
  deriving Repr, DecidableEq

@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "M"]
abbrev M (state value exception : Type) := state → Exc value exception × state

/-- Failure retains the state returned by the first computation. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "st_ex_bind_def"]
def bind {state value result exception : Type}
    (x : M state value exception) (f : value → M state result exception) :
    M state result exception := fun s =>
  match x s with
  | (.success y, next) => f y next
  | (.failure error, next) => (.failure error, next)

@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "st_ex_ignore_bind_def"]
def ignoreBind {state value result exception : Type}
    (x : M state value exception) (f : M state result exception) :
    M state result exception := fun s =>
  match x s with
  | (.success _, next) => f next
  | (.failure error, next) => (.failure error, next)

@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "st_ex_return_def"]
def ret {state value exception : Type} (x : value) : M state value exception :=
  fun s => (.success x, s)

@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Marray_alloc_def"]
def arrayAlloc {state value exception : Type}
    (setArr : List value → state → state) (n : Nat) (x : value) :
    M state Unit exception :=
  fun s => (.success (), setArr (List.replicate n x) s)

@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "run_def"]
def run {state value exception : Type} (x : M state value exception) (s : state) :
    Exc value exception := (x s).1

end Flapjack.Translator.Monadic.MonadBase
