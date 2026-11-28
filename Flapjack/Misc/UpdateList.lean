module

public import Flapjack.HolRef

@[expose] public section

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

/-- Original `UPDATE_LIST_THM`: an empty update list leaves the function and a
consed one folds the head update into the tail. -/
@[hol "cakeml/misc/miscScript.sml" "UPDATE_LIST_THM"]
theorem updateList_nil_cons {α β : Type} [DecidableEq α] (f : α → β) :
    updateList f [] = f ∧
      ∀ (h : α × β) (t : List (α × β)),
        updateList f (h :: t) = updateList (fun x => if h.1 = x then h.2 else f x) t := by
  constructor
  · rfl
  · intro h t
    rfl

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

/-- Original `UPDATE_LIST_NOT_MEM`: updating at a key that is not a key of the
list leaves the function unchanged there. -/
@[hol "cakeml/misc/miscScript.sml" "UPDATE_LIST_NOT_MEM"]
theorem updateList_not_mem {α β : Type} [DecidableEq α] (ls : List (α × β)) :
    ∀ (f : α → β) (x : α), x ∉ ls.map Prod.fst → updateList f ls x = f x := by
  induction ls with
  | nil =>
    intro f x _
    rfl
  | cons hd tl ih =>
    intro f x h
    rw [List.map_cons, List.mem_cons, not_or] at h
    obtain ⟨hne, htl⟩ := h
    have hstep : updateList f (hd :: tl) =
        updateList (fun y => if hd.1 = y then hd.2 else f y) tl := rfl
    rw [hstep, ih _ x htl]
    rw [if_neg (by
      intro heq
      exact hne heq.symm)]

private theorem updateList_congr {α β : Type} [DecidableEq α] (f g : α → β) (x : α)
    (h : f x = g x) : ∀ ls : List (α × β), updateList f ls x = updateList g ls x := by
  intro ls
  induction ls generalizing f g with
  | nil => exact h
  | cons hd tl ih =>
    have hx : (fun y => if hd.1 = y then hd.2 else f y) x =
        (fun y => if hd.1 = y then hd.2 else g y) x := by
      simp only [h]
    exact ih _ _ hx

private theorem updateList_head_ne {α β : Type} [DecidableEq α] (f : α → β) (k : α) (v : β)
    (rest : List (α × β)) (k' : α) (h : k ≠ k') :
    updateList f ((k, v) :: rest) k' = updateList f rest k' := by
  have hstep : updateList f ((k, v) :: rest) =
      updateList (fun y => if k = y then v else f y) rest := rfl
  rw [hstep]
  apply updateList_congr
  rw [if_neg h]

private theorem updateList_same_head {α β : Type} [DecidableEq α] (f : α → β) (k : α) (v : β)
    (rest : List (α × β)) (h : k ∉ rest.map Prod.fst) :
    updateList f ((k, v) :: rest) k = v := by
  have hstep : updateList f ((k, v) :: rest) =
      updateList (fun y => if k = y then v else f y) rest := rfl
  rw [hstep, updateList_not_mem rest _ k h]
  rw [if_pos rfl]

/-- Original `MAP_ZIP_UPDATE_LIST_ALL_DISTINCT_same`: updating a function at the
distinct keys of a list with the paired values returns the value list. -/
@[hol "cakeml/misc/miscScript.sml" "MAP_ZIP_UPDATE_LIST_ALL_DISTINCT_same"]
theorem mapUpdateListZipSame {α β : Type} [DecidableEq α] (ks : List α) (vs : List β) :
    ∀ f : α → β, ks.length = vs.length ∧ ks.Nodup →
      ks.map (fun k => updateList f (List.zip ks vs) k) = vs := by
  induction ks generalizing vs with
  | nil =>
    intro f h
    obtain ⟨hlen, -⟩ := h
    cases vs with
    | nil => rfl
    | cons v vs => simp at hlen
  | cons k ks ih =>
    intro f h
    obtain ⟨hlen, hnodup⟩ := h
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      simp only [List.length_cons] at hlen
      have hlen' : ks.length = vs.length := by omega
      obtain ⟨hk, hnodup'⟩ := List.nodup_cons.mp hnodup
      rw [List.zip_cons_cons, List.map_cons]
      have hmap : ks.map (fun k' => updateList f ((k, v) :: List.zip ks vs) k') =
          ks.map (fun k' => updateList f (List.zip ks vs) k') := by
        apply List.map_congr_left
        intro k' hk'
        exact updateList_head_ne f k v (List.zip ks vs) k' (by
          intro heq
          exact hk (heq ▸ hk'))
      have hzip : k ∉ (List.zip ks vs).map Prod.fst := by
        rw [List.map_fst_zip (by omega)]
        exact hk
      rw [hmap, ih vs f ⟨hlen', hnodup'⟩,
        updateList_same_head f k v (List.zip ks vs) hzip]

end Flapjack.Misc.UpdateList
