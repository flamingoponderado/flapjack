module

public import Flapjack.HolRef

@[expose] public section

/-!
# Cake `mllist$mapi`

Lean counterpart of `mapi_def` in
`cakeml/basis/pure/mllistScript.sml:364-368`: apply the function to the
element together with its index, counting from `n`.
-/

namespace Flapjack.Basis.Pure.MlList

/-- Original `mapi_def`: map with an index argument.  HOL's `let y = f n h in
y :: ...` is the direct application `f n h :: ...`. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "mapi_def"]
def mapi {α β : Type} (f : Nat → β → α) : Nat → List β → List α
  | _, [] => []
  | n, h :: t => f n h :: mapi f (n + 1) t

/-- HOL core `MAPi` (in `indexedListsTheory`): the index counts from zero and
    the recursive step composes the function with `SUC`, as in `MAPi_def`. -/
@[hol "HOL/src/list/src/indexedListsScript.sml" "MAPi_def"]
def holMapi {β α : Type} (f : Nat → β → α) : List β → List α
  | [] => []
  | h :: t => f 0 h :: holMapi (fun n x => f (n + 1) x) t

/-- The shifted function form of `mapi`, used to prove `MAPI_thm`. -/
private theorem holMapi_shift {β α : Type} (f : Nat → β → α) :
    ∀ (l : List β) (n : Nat), holMapi (fun i x => f (i + n) x) l = mapi f n l
  | [], _ => rfl
  | h :: t, n => by
      have ih := holMapi_shift f t (n + 1)
      have hfun : (fun i x => f (i + 1 + n) x) = (fun i x => f (i + (n + 1)) x) := by
        funext i x
        rw [show i + 1 + n = i + (n + 1) by omega]
      simp only [holMapi, mapi, Nat.zero_add]
      rw [← ih]
      congr 1
      exact congrArg (fun g => holMapi g t) hfun

/-- Original `MAPI_thm`: HOL's `MAPi` is `mapi` started at index zero. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "MAPI_thm"]
theorem holMapi_eq_mapi {β α : Type} (f : Nat → β → α) (l : List β) :
    holMapi f l = mapi f 0 l := by
  simpa using holMapi_shift f l 0

/-- Original `MAPi_ID`: indexing with the identity function is the identity.
HOL marks this `[simp]`; Lean keeps it as a function equality, so the attribute
is not reproduced (its pointwise form is a separate rewrite). -/
@[hol "cakeml/misc/miscScript.sml" "MAPi_ID"]
theorem holMapi_id {α : Type} :
    holMapi (fun (_ : Nat) (y : α) => y) = fun (l : List α) => l := by
  funext l
  induction l with
  | nil => rfl
  | cons h t ih => simp [holMapi, ih]

/-- Original `FST_UNZIP_MAPi`: the first components of an unzipped indexed map. -/
@[hol "cakeml/misc/miscScript.sml" "FST_UNZIP_MAPi"]
theorem fst_unzip_holMapi {β α γ : Type} (f : Nat → β → α × γ) :
    ∀ (l : List β), (holMapi f l).unzip.1 = holMapi (fun n x => (f n x).1) l := by
  intro l
  induction l generalizing f with
  | nil => rfl
  | cons h t ih =>
    simp only [holMapi, List.unzip]
    rw [ih (fun n x => f (n + 1) x)]

/-- Original `SND_UNZIP_MAPi`: the second components of an unzipped indexed map. -/
@[hol "cakeml/misc/miscScript.sml" "SND_UNZIP_MAPi"]
theorem snd_unzip_holMapi {β α γ : Type} (f : Nat → β → α × γ) :
    ∀ (l : List β), (holMapi f l).unzip.2 = holMapi (fun n x => (f n x).2) l := by
  intro l
  induction l generalizing f with
  | nil => rfl
  | cons h t ih =>
    simp only [holMapi, List.unzip]
    rw [ih (fun n x => f (n + 1) x)]

/-- Original `MAPi_eq_MAP`: a `MAPi` that ignores its index is a plain `MAP`. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "MAPi_eq_MAP"]
theorem holMapi_eq_map {β α : Type} (f : β → α) (xs : List β) :
    holMapi (fun _ x => f x) xs = List.map f xs := by
  induction xs with
  | nil => simp [holMapi]
  | cons x rest ih => simp [holMapi, ih]

end Flapjack.Basis.Pure.MlList
