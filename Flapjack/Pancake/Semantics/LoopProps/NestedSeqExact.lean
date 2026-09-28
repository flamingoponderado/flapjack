import Flapjack.Pancake.Semantics.LoopProps.EvalExact
import Flapjack.Pancake.PanCommon

/-!
# loopProps `nested_seq` evaluation lemmas over the exact evaluator

Counterparts of `cakeml/pancake/semantics/loopPropsScript.sml`'s
`evaluate_nested_seq_cases` (line 696), `evaluate_nested_seq_comb_seq` (1089)
and `loop_eval_nested_assign_distinct_eq` (190) over
`LoopSemStateFiniteExact.evaluate` and the exact `nested_seq` port
`loopNestedSeqHOL` (bead `flapjack-pxgp.12`).
-/

namespace Flapjack

theorem sptInsert_root_zero {α : Type} (v : α) (t : Spt α) :
    sptInsert 0 v t = match t with
      | .ln => .ls v | .ls _ => .ls v | .bn l r => .bs l v r | .bs l _ r => .bs l v r := by
  cases t <;> simp [sptInsert]

theorem sptInsert_root_even {α : Type} {k : Nat} (h : k ≠ 0) (he : k % 2 = 0) (v : α) (t : Spt α) :
    sptInsert k v t = match t with
      | .ln => .bn (sptInsert ((k - 1) / 2) v .ln) .ln
      | .ls e => .bs (sptInsert ((k - 1) / 2) v .ln) e .ln
      | .bn l r => .bn (sptInsert ((k - 1) / 2) v l) r
      | .bs l e r => .bs (sptInsert ((k - 1) / 2) v l) e r := by
  cases t
  · rw [sptInsert.eq_1, if_neg h, if_pos he]
  · rw [sptInsert.eq_2, if_neg h, if_pos he]
  · rw [sptInsert.eq_3, if_neg h, if_pos he]
  · rw [sptInsert.eq_4, if_neg h, if_pos he]

theorem sptInsert_root_odd {α : Type} {k : Nat} (h : k ≠ 0) (he : ¬ k % 2 = 0) (v : α) (t : Spt α) :
    sptInsert k v t = match t with
      | .ln => .bn .ln (sptInsert ((k - 1) / 2) v .ln)
      | .ls e => .bs .ln e (sptInsert ((k - 1) / 2) v .ln)
      | .bn l r => .bn l (sptInsert ((k - 1) / 2) v r)
      | .bs l e r => .bs l e (sptInsert ((k - 1) / 2) v r) := by
  cases t
  · rw [sptInsert.eq_1, if_neg h, if_neg he]
  · rw [sptInsert.eq_2, if_neg h, if_neg he]
  · rw [sptInsert.eq_3, if_neg h, if_neg he]
  · rw [sptInsert.eq_4, if_neg h, if_neg he]

/-- `sptInsert` on distinct keys commutes structurally (HOL `sptree` tries are
    order-independent; cf. HOL `insert_swap`).  Local proof support, no tag. -/
theorem sptInsert_comm {α : Type} :
    ∀ (k1 k2 : Nat) (v1 v2 : α) (t : Spt α), k1 ≠ k2 →
      sptInsert k1 v1 (sptInsert k2 v2 t) = sptInsert k2 v2 (sptInsert k1 v1 t) := by
  intro k1
  induction k1 using Nat.strongRecOn with
  | ind k1 ih =>
    intro k2 v1 v2 t hne
    by_cases h1 : k1 = 0
    · subst h1
      have h2 : k2 ≠ 0 := fun h => hne h.symm
      by_cases e2 : k2 % 2 = 0 <;> cases t <;>
        simp only [sptInsert_root_zero, sptInsert_root_even h2, sptInsert_root_odd h2, e2,
          not_false_eq_true]
    · by_cases h2 : k2 = 0
      · subst h2
        by_cases e1 : k1 % 2 = 0 <;> cases t <;>
          simp only [sptInsert_root_zero, sptInsert_root_even h1, sptInsert_root_odd h1, e1,
            not_false_eq_true]
      · have hdec : (k1 - 1) / 2 < k1 := by omega
        by_cases e1 : k1 % 2 = 0 <;> by_cases e2 : k2 % 2 = 0 <;> cases t <;>
          simp only [sptInsert_root_even h1, sptInsert_root_odd h1, sptInsert_root_even h2,
            sptInsert_root_odd h2, e1, e2, not_false_eq_true] <;>
          (try rfl) <;>
          (congr 1; exact ih _ hdec _ _ _ _ (by omega))

namespace LoopPropsNestedSeqFiniteSupport

/-- Local same-module witness for the canonical finite-support
`LoopSemStateFiniteExact` carrier used by the `fmap_as_finite_support := [globals]`
qualified ports in this module (re-exports the checked witness of
`Flapjack/Pancake/Semantics/LoopSemStateExact.lean`). -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

end LoopPropsNestedSeqFiniteSupport

namespace LoopSemStateFiniteExact

variable {width : Nat} [NeZero width] {F : Type}

/-- The `Seq` clause of `evaluate_def` with `fix_clock` removed, as HOL's
    rebound `evaluate_def` (`loopSemScript.sml:498`) states it. -/
theorem evaluate_seq (c1 c2 : HolLoopProg width) (s : LoopSemStateFiniteExact width F) :
    evaluate (.seq c1 c2) s =
      match evaluate c1 s with
      | (none, s1) => evaluate c2 s1
      | (res, s1) => (res, s1) := by
  rw [evaluate, fix_clock_evaluate]
  cases evaluate c1 s with
  | mk r s1 => cases r <;> rfl

theorem evaluate_nested_seq_append_none :
    ∀ (p : List (HolLoopProg width)) (s st : LoopSemStateFiniteExact width F)
      (q : List (HolLoopProg width)),
      evaluate (loopNestedSeqHOL p) s = (none, st) →
      evaluate (loopNestedSeqHOL (p ++ q)) s = evaluate (loopNestedSeqHOL q) st
  | [], s, st, q, h => by
      rw [loopNestedSeqHOL, evaluate] at h; cases h; rfl
  | c :: p, s, st, q, h => by
      rw [List.cons_append, loopNestedSeqHOL, evaluate_seq]
      rw [loopNestedSeqHOL, evaluate_seq] at h
      cases hc : evaluate c s with
      | mk r s1 =>
        rw [hc] at h
        cases r with
        | none => exact evaluate_nested_seq_append_none p s1 st q h
        | some v => cases h

theorem evaluate_nested_seq_append_some :
    ∀ (p : List (HolLoopProg width)) (s : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (st : LoopSemStateFiniteExact width F)
      (q : List (HolLoopProg width)),
      evaluate (loopNestedSeqHOL p) s = (res, st) → res ≠ none →
      evaluate (loopNestedSeqHOL (p ++ q)) s = evaluate (loopNestedSeqHOL p) s
  | [], s, res, st, q, h, hr => by
      rw [loopNestedSeqHOL, evaluate] at h; cases h; exact absurd rfl hr
  | c :: p, s, res, st, q, h, hr => by
      rw [List.cons_append, loopNestedSeqHOL, evaluate_seq, loopNestedSeqHOL, evaluate_seq]
      rw [loopNestedSeqHOL, evaluate_seq] at h
      cases hc : evaluate c s with
      | mk r s1 =>
        rw [hc] at h
        cases r with
        | none => exact evaluate_nested_seq_append_some p s1 res st q h hr
        | some v => rfl

/-- Exact HOL `evaluate_nested_seq_cases` (`loopPropsScript.sml:696-707`). -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "evaluate_nested_seq_cases"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluate_nested_seq_cases :
    (∀ (p q : List (HolLoopProg width)) (s st t : LoopSemStateFiniteExact width F),
      evaluate (loopNestedSeqHOL (p ++ q)) s = (none, t) ∧
      evaluate (loopNestedSeqHOL p) s = (none, st) →
      evaluate (loopNestedSeqHOL q) st = (none, t)) ∧
    (∀ (p : List (HolLoopProg width)) (s st : LoopSemStateFiniteExact width F)
      (q : List (HolLoopProg width)),
      evaluate (loopNestedSeqHOL p) s = (none, st) →
      evaluate (loopNestedSeqHOL (p ++ q)) s = evaluate (loopNestedSeqHOL q) st) ∧
    (∀ (p : List (HolLoopProg width)) (s : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (st : LoopSemStateFiniteExact width F)
      (q : List (HolLoopProg width)),
      evaluate (loopNestedSeqHOL p) s = (res, st) ∧ res ≠ none →
      evaluate (loopNestedSeqHOL (p ++ q)) s = evaluate (loopNestedSeqHOL p) s) :=
  ⟨fun p q s st t ⟨h1, h2⟩ => by rw [← evaluate_nested_seq_append_none p s st q h2]; exact h1,
   fun p s st q h => evaluate_nested_seq_append_none p s st q h,
   fun p s res st q ⟨h, hr⟩ => evaluate_nested_seq_append_some p s res st q h hr⟩

/-- Exact HOL `evaluate_nested_seq_comb_seq` (`loopPropsScript.sml:1089-1092`):
    `!p q t. evaluate (Seq (nested_seq p) (nested_seq q), t) =
      evaluate (nested_seq (p ++ q), t)`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "evaluate_nested_seq_comb_seq"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluate_nested_seq_comb_seq (p q : List (HolLoopProg width))
    (t : LoopSemStateFiniteExact width F) :
    evaluate (.seq (loopNestedSeqHOL p) (loopNestedSeqHOL q)) t =
      evaluate (loopNestedSeqHOL (p ++ q)) t := by
  rw [evaluate_seq]
  cases hp : evaluate (loopNestedSeqHOL p) t with
  | mk r st =>
    cases r with
    | none => exact (evaluate_nested_seq_append_none p t st q hp).symm
    | some v =>
      rw [evaluate_nested_seq_append_some p t (some v) st q hp (by simp), hp]

theorem sptAlistInsert_sptInsert_comm {α : Type} (n : Nat) (v : α) :
    ∀ (ns : List Nat) (vs : List α) (l : Spt α), n ∉ ns →
      sptAlistInsert ns vs (sptInsert n v l) = sptInsert n v (sptAlistInsert ns vs l)
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | m :: ns, w :: vs, l, hn => by
      simp only [sptAlistInsert]
      rw [sptAlistInsert_sptInsert_comm n v ns vs l (fun h => hn (List.mem_cons_of_mem _ h))]
      exact sptInsert_comm m n w v _ (fun h => hn (h ▸ List.mem_cons_self))

/-- Exact HOL `loop_eval_nested_assign_distinct_eq` (`loopPropsScript.sml:190-197`):
    `!es ns t ev. MAP (eval t) es = MAP SOME ev /\
      distinct_lists ns (FLAT (MAP locals_touched es)) /\ ALL_DISTINCT ns /\
      LENGTH ns = LENGTH es ==>
      evaluate (nested_seq (MAP2 Assign ns es),t) =
      (NONE, t with locals := (alist_insert ns ev t.locals))`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "loop_eval_nested_assign_distinct_eq"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loop_eval_nested_assign_distinct_eq :
    ∀ (es : List (HolLoopExp width)) (ns : List Nat) (t : LoopSemStateFiniteExact width F)
      (ev : List (WordLocW width)),
      es.map (eval t) = ev.map some ∧
      distinctListsHol ns (es.map holLoopLocalsTouched).flatten = true ∧
      ns.Nodup ∧ ns.length = es.length →
      evaluate (loopNestedSeqHOL (List.zipWith HolLoopProg.assign ns es)) t =
        (none, { t with locals := sptAlistInsert ns ev t.locals })
  | [], ns, t, ev, ⟨hmap, _, _, hl⟩ => by
      have hns : ns = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
      have hev : ev = [] := by
        cases ev with
        | nil => rfl
        | cons _ _ => simp at hmap
      subst hns hev
      simp only [List.zipWith_nil_left, loopNestedSeqHOL, sptAlistInsert]
      rw [evaluate]
  | _ :: _, [], _, _, ⟨_, _, _, hl⟩ => by simp at hl
  | e :: es, n :: ns, t, ev, ⟨hmap, hdist, hnd, hl⟩ => by
      cases ev with
      | nil => simp at hmap
      | cons v ev =>
        simp only [List.map_cons, List.cons.injEq] at hmap
        obtain ⟨he, hes⟩ := hmap
        have hdist' := (distinctListsHol_eq_true_iff_listDisjoint _ _).1 hdist
        have hnt : ∀ e' ∈ es, n ∉ holLoopLocalsTouched e' := fun e' he' hm =>
          hdist' n List.mem_cons_self (by
            simp only [List.map_cons, List.flatten_cons, List.mem_append, List.mem_flatten,
              List.mem_map]
            exact Or.inr ⟨_, ⟨e', he', rfl⟩, hm⟩)
        have hn : n ∉ ns := (List.nodup_cons.mp hnd).1
        simp only [List.zipWith_cons_cons, loopNestedSeqHOL]
        rw [evaluate_seq, evaluate]
        simp only [he]
        have hes' : es.map (eval (setVar n v t)) = ev.map some := by
          rw [← hes]
          apply List.map_congr_left
          intro e' he'
          apply locals_touched_eq_eval_eq
          refine ⟨rfl, rfl, rfl, rfl, rfl, fun m hm => ?_⟩
          simp only [setVar]
          rw [sptLookup_sptInsert, if_neg (show ¬ m = n from fun h => hnt e' he' (h ▸ hm))]
        have hdist2 : distinctListsHol ns (es.map holLoopLocalsTouched).flatten = true := by
          rw [distinctListsHol_eq_true_iff_listDisjoint]
          intro x hx hy
          exact hdist' x (List.mem_cons_of_mem _ hx) (by
            simp only [List.map_cons, List.flatten_cons, List.mem_append]; exact Or.inr hy)
        rw [loop_eval_nested_assign_distinct_eq es ns (setVar n v t) ev
          ⟨hes', hdist2, (List.nodup_cons.mp hnd).2, by simpa using hl⟩]
        simp only [setVar, sptAlistInsert, sptAlistInsert_sptInsert_comm n v ns ev t.locals hn]

end LoopSemStateFiniteExact
end Flapjack
