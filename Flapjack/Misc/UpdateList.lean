import Flapjack.HolRef

/-! `miscScript.sml` `UPDATE_LIST` (`=++`): iterated function update, and its
`ALOOKUP` characterisation. HOL `UPDATE a b f = λx. if a = x then b else f x`
is written inline with decidable key equality (HOL equality); `ALOOKUP` is
`List.lookup`. -/
namespace Flapjack.Misc.UpdateList

/-- Exact HOL `UPDATE_LIST_def`: `UPDATE_LIST = FOLDL (combin$C (UNCURRY UPDATE))`,
i.e. `f =++ ls` folds `(a =+ b)` over `ls` from the left. -/
@[hol "cakeml/misc/miscScript.sml" "UPDATE_LIST_def"]
def updateList {α β : Type} [DecidableEq α] (f : α → β) (ls : List (α × β)) : α → β :=
  ls.foldl (fun g p => fun x => if p.1 = x then p.2 else g x) f

/-- `ALOOKUP` over a list extended by one trailing pair (Flapjack
infrastructure for the proof below). -/
theorem lookup_append_singleton {α β : Type} [DecidableEq α] (l : List (α × β)) (a : α) (b : β)
    (x : α) :
    (l ++ [(a, b)]).lookup x =
      match l.lookup x with
      | none => if (x == a) then some b else none
      | some y => some y := by
  induction l with
  | nil => simp [List.lookup]; split <;> simp_all
  | cons p l ih =>
      obtain ⟨c, d⟩ := p
      by_cases hc : (x == c) = true
      · simp [List.lookup, hc]
      · simp only [List.cons_append, List.lookup, Bool.not_eq_true] at hc ⊢
        simp only [hc]
        exact ih

/-- Full original `APPLY_UPDATE_LIST_ALOOKUP`:
`∀ls f x. (f =++ ls) x = case ALOOKUP (REVERSE ls) x of NONE => f x | SOME y => y`. -/
@[hol "cakeml/misc/miscScript.sml" "APPLY_UPDATE_LIST_ALOOKUP"]
theorem applyUpdateListALookup {α β : Type} [DecidableEq α] :
    ∀ (ls : List (α × β)) (f : α → β) (x : α),
      updateList f ls x =
        match ls.reverse.lookup x with
        | none => f x
        | some y => y := by
  intro ls
  induction ls with
  | nil => intro f x; rfl
  | cons p ls ih =>
      intro f x
      obtain ⟨a, b⟩ := p
      have step : updateList f ((a, b) :: ls) x =
          updateList (fun y => if a = y then b else f y) ls x := rfl
      rw [step, ih, List.reverse_cons, lookup_append_singleton]
      cases ls.reverse.lookup x with
      | some y => rfl
      | none =>
          by_cases h : a = x
          · subst h; simp
          · have hx : (x == a) = false := by simp [Ne.symm h]
            simp [h, hx]

end Flapjack.Misc.UpdateList
