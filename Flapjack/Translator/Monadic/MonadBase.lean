module

public import Flapjack.HolRef

@[expose] public section

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

/-- Original `liftM_def`: run `op` on the state projected by `read` and write
    the resulting state back through `write`. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "liftM_def"]
def liftM {δ α β γ : Type} (read : δ → α) (write : (α → α) → δ → δ)
    (op : α → Exc β γ × α) : δ → Exc β γ × δ := fun state =>
  let (ret, new) := op (read state)
  (ret, write (fun _ => new) state)

/-- Original `otherwise_def`: `y` runs on the state where `x` failed. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "otherwise_def"]
def otherwise {α β γ : Type} (x y : M α β γ) : M α β γ := fun s =>
  match x s with
  | (.success v, s') => (.success v, s')
  | (.failure _, s') => y s'

/-- Original `can_def`: a guard that turns failure into `false`. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "can_def"]
def can {α β γ δ : Type} (f : γ → M α δ β) (x : γ) : M α Bool β :=
  otherwise (ignoreBind (f x) (ret true)) (ret false)

/-- Original `ref_bind_def`: create a reference, map its value and continue with
    the resulting monad. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "ref_bind_def"]
def refBind {α δ ε γ ζ β : Type} (create : α → Exc ε γ × δ) (f : ε → δ → ζ)
    (pop : ζ → Exc β γ × δ) : α → Exc β γ × δ := fun s =>
  match create s with
  | (.success x, s') => pop (f x s')
  | (.failure x', s') => (.failure x', s')

/-- Original `Mget_ref_def`. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mget_ref_def"]
def mGetRef {α β γ : Type} (getVar : α → β) : M α β γ := fun s => (.success (getVar s), s)

/-- Original `Mset_ref_def`. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mset_ref_def"]
def mSetRef {α β γ δ : Type} (setVar : δ → α → γ) (x : δ) : α → Exc Unit β × γ :=
  fun s => (.success (), setVar x s)

/-- Original `st_ex_bind_CONG`: the congruence rule HOL exports for the
    termination prover. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "st_ex_bind_CONG"]
theorem bindCong {α β γ δ : Type} (x x' : M α β γ) (s s' : α) (f f' : β → M α δ γ) :
    x = x' → s = s' → (∀ y s'', x' s' = (.success y, s'') → f y s'' = f' y s'') →
      bind x f s = bind x' f' s' := by
  rintro rfl rfl h
  cases hx : x s with
  | mk r s'' =>
      cases r with
      | success v =>
          simp only [bind, hx]
          exact h v s'' hx
      | failure _ => simp only [bind, hx]

/-- Original `st_ex_ignore_bind_CONG`. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "st_ex_ignore_bind_CONG"]
theorem ignoreBindCong {α β γ δ : Type} (x x' : M α β γ) (s s' : α) (f f' : M α δ γ) :
    x = x' → s = s' → (∀ y s'', x' s' = (.success y, s'') → f s'' = f' s'') →
      ignoreBind x f s = ignoreBind x' f' s' := by
  rintro rfl rfl h
  cases hx : x s with
  | mk r s'' =>
      cases r with
      | success v =>
          simp only [ignoreBind, hx]
          exact h v s'' hx
      | failure _ => simp only [ignoreBind, hx]

end Flapjack.Translator.Monadic.MonadBase
