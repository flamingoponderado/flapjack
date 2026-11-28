module

public import Flapjack.Translator.Monadic.MonadBase
public import Flapjack.Misc.ListEl

@[expose] public section

/-!
# ml_monadBase reference primitives

Ports of the reference primitives of
`cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml:222-350`. The
monad state is HOL's store, a `store_v list`; references are indices counted
from the end of that list (`LENGTH s - n - 1`). `dref` renders HOL's `EL`
through the ARB-completed `holEl`, so it carries the element type's
inhabitance instance (`total_function_inhabitants`); `ref_assign` is HOL's
`LUPDATE`, i.e. `List.set`.
-/

namespace Flapjack.Translator.Monadic.MonadBase

/-- Original `store_ref`: a reference is an index into the store. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "store_ref"]
inductive StoreRef where
  | storeRef (index : Nat)
  deriving Repr, DecidableEq

/-- Original `Mref_def`: allocate a fresh reference and push it onto the store. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mref_def"]
def mRef {α γ β : Type} (cons : γ → α) (x : γ) : List α → Exc StoreRef β × List α :=
  fun s => (.success (.storeRef s.length), cons x :: s)

/-- Original `dref_def`: read the store element a reference points at, counting
    from the end. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "dref_def"
  (total_function_inhabitants := [α])]
noncomputable def dref {α : Type} [Nonempty α] (n : Nat) : List α → α :=
  fun s => holEl (s.length - n - 1) s

/-- Original `ref_assign_def`: HOL `LUPDATE x (LENGTH s - n - 1) s`. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "ref_assign_def"]
def refAssign {α : Type} (n : Nat) (x : α) : List α → List α :=
  fun s => s.set (s.length - n - 1) x

/-- Original `Mdref_aux_def`: index the store from its head. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mdref_aux_def"]
def mDrefAux {α β : Type} (e : β) (n : Nat) : List α → Exc α β
  | [] => .failure e
  | x :: s => if n = 0 then .success x else mDrefAux e (n - 1) s

/-- Original `Mdref_def`: read through a reference, keeping the state. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mdref_def"]
def mDref {α β : Type} (e : β) : StoreRef → List α → Exc α β × List α
  | .storeRef n, s => (mDrefAux e (s.length - n - 1) s, s)

/-- Original `Mpop_ref_def`: pop the newest store element, failing on an empty
    store. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mpop_ref_def"]
def mPopRef {α β γ : Type} (e : β) : Exc α β × List γ → Exc α β × List γ
  | (_, []) => (.failure e, [])
  | (r, _ :: v1) => (r, v1)

/-- Original `Mref_assign_aux_def`: replace the element `n` positions from the
    head, failing on an out-of-range index. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mref_assign_aux_def"]
def mRefAssignAux {α β : Type} (e : β) (n : Nat) (x : α) : List α → Exc (List α) β
  | [] => .failure e
  | x' :: s' =>
    if n = 0 then .success (x :: s')
    else
      match mRefAssignAux e (n - 1) x s' with
      | .success s'' => .success (x' :: s'')
      | .failure v3 => .failure v3

/-- Original `Mref_assign_def`: write through a reference, keeping the state on
    failure. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mref_assign_def"]
def mRefAssign {α β : Type} (e : β) : StoreRef → α → List α → Exc Unit β × List α
  | .storeRef n, x, s =>
    match mRefAssignAux e (s.length - n - 1) x s with
    | .success v => (.success (), v)
    | .failure e => (.failure e, s)

/-- HOL `LUPDATE`-shaped law for `Mref_assign_aux`: an in-range index replaces
    that element and succeeds. -/
theorem mRefAssignAuxSet {α β : Type} (s : List α) (k : Nat) (x : α) (e : β)
    (h : k < s.length) : mRefAssignAux e k x s = .success (s.set k x) := by
  induction s generalizing k with
  | nil => simp at h
  | cons y s ih =>
      cases k with
      | zero => simp [mRefAssignAux]
      | succ k =>
          simp only [mRefAssignAux, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
          have hk : k < s.length := by
            simp at h
            omega
          rw [ih k hk]
          simp

/-- Original `Mref_assign_aux_eq`. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mref_assign_aux_eq"]
theorem mRefAssignAuxEq {α β : Type} (state : List α) (e : β) (n : Nat) (x : α)
    (h : n < state.length) :
    mRefAssignAux e (state.length - n - 1) x state = .success (refAssign n x state) := by
  rw [mRefAssignAuxSet state (state.length - n - 1) x e (by omega)]
  simp [refAssign]

/-- Original `Mref_assign_eq`. -/
@[hol "cakeml/translator/monadic/monad_base/ml_monadBaseScript.sml" "Mref_assign_eq"]
theorem mRefAssignEq {α β : Type} (state : List α) (e : β) (n : Nat) (x : α)
    (h : n < state.length) :
    mRefAssign e (.storeRef n) x state = (.success (), refAssign n x state) := by
  rw [mRefAssign, mRefAssignAuxEq state e n x h]

end Flapjack.Translator.Monadic.MonadBase
