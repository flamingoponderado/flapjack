import Flapjack.Pancake.Semantics.LoopProps.EvaluateClockExact

namespace Flapjack

/-- HOL `sptree$lookup_insert`: `lookup k (insert k2 v t) = if k = k2 then SOME v
    else lookup k t`.  Local proof support (HOL library `sptree`, no tag). -/
theorem sptLookup_sptInsert {α : Type} :
    ∀ (k2 k : Nat) (v : α) (t : Spt α),
      sptLookup k (sptInsert k2 v t) = if k = k2 then some v else sptLookup k t := by
  intro k2
  induction k2 using Nat.strongRecOn with
  | ind k2 ih =>
    intro k v t
    by_cases h0 : k2 = 0
    · subst h0
      cases t
      · rw [sptInsert.eq_1, if_pos rfl]; by_cases hk : k = 0 <;> simp [sptLookup, hk]
      · rw [sptInsert.eq_2, if_pos rfl]; by_cases hk : k = 0 <;> simp [sptLookup, hk]
      · rw [sptInsert.eq_3, if_pos rfl]; by_cases hk : k = 0 <;> simp [sptLookup, hk]
      · rw [sptInsert.eq_4, if_pos rfl]; by_cases hk : k = 0 <;> simp [sptLookup, hk]
    · have hdec : (k2 - 1) / 2 < k2 := by omega
      have ihk := fun k => ih _ hdec k v
      by_cases he : k2 % 2 = 0
      · cases t
        all_goals first
          | rw [sptInsert.eq_1, if_neg h0, if_pos he]
          | rw [sptInsert.eq_2, if_neg h0, if_pos he]
          | rw [sptInsert.eq_3, if_neg h0, if_pos he]
          | rw [sptInsert.eq_4, if_neg h0, if_pos he]
        all_goals
          by_cases hk : k = 0
          · subst hk; simp [sptLookup, Ne.symm h0]
          · by_cases hke : k % 2 = 0
            · simp only [sptLookup, if_neg hk, if_pos hke, ihk]
              by_cases hkk : k = k2
              · subst hkk; simp
              · have : (k - 1) / 2 ≠ (k2 - 1) / 2 := by omega
                simp [this, hkk]
            · have hkk : k ≠ k2 := by omega
              simp [sptLookup, hk, hke, hkk]
      · cases t
        all_goals first
          | rw [sptInsert.eq_1, if_neg h0, if_neg he]
          | rw [sptInsert.eq_2, if_neg h0, if_neg he]
          | rw [sptInsert.eq_3, if_neg h0, if_neg he]
          | rw [sptInsert.eq_4, if_neg h0, if_neg he]
        all_goals
          by_cases hk : k = 0
          · subst hk; simp [sptLookup, Ne.symm h0]
          · by_cases hke : k % 2 = 0
            · have hkk : k ≠ k2 := by omega
              simp [sptLookup, hk, hke, hkk]
            · simp only [sptLookup, if_neg hk, if_neg hke, ihk]
              by_cases hkk : k = k2
              · subst hkk; simp
              · have : (k - 1) / 2 ≠ (k2 - 1) / 2 := by omega
                simp [this, hkk]

namespace LoopPropsEvalFiniteSupport

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

end LoopPropsEvalFiniteSupport

namespace LoopSemStateFiniteExact

variable {width : Nat} [NeZero width] {F : Type}

theorem getVars_congr (ns : List Nat) (s t : LoopSemStateFiniteExact width F)
    (h : ∀ n ∈ ns, sptLookup n s.locals = sptLookup n t.locals) :
    getVars ns s = getVars ns t := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simp only [getVars]
    rw [h n (List.mem_cons_self), ih (fun m hm => h m (List.mem_cons_of_mem _ hm))]

/-- Exact HOL `get_vars_clock_upd_eq` (`loopPropsScript.sml:269-272`):
    `!ns st l ck. get_vars ns (st with clock := ck) = get_vars ns st`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "get_vars_clock_upd_eq"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem get_vars_clock_upd_eq (ns : List Nat) (st : LoopSemStateFiniteExact width F)
    (_l : Spt (WordLocW width)) (ck : Nat) :
    getVars ns { st with clock := ck } = getVars ns st :=
  getVars_congr ns _ _ (fun _ _ => rfl)

/-- Exact HOL `get_vars_local_clock_upd_eq` (`loopPropsScript.sml:260-263`):
    `!ns st l ck. get_vars ns (st with <|locals := l; clock := ck|>) =
      get_vars ns (st with locals := l)`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "get_vars_local_clock_upd_eq"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem get_vars_local_clock_upd_eq (ns : List Nat) (st : LoopSemStateFiniteExact width F)
    (l : Spt (WordLocW width)) (ck : Nat) :
    getVars ns { st with locals := l, clock := ck } = getVars ns { st with locals := l } :=
  getVars_congr ns _ _ (fun _ _ => rfl)

/-- Exact HOL `eval_upd_locals_clock_eq` (`loopPropsScript.sml:959-960`):
    `!t e l ck. eval (t with <|locals := l; clock := ck|>) e = eval (t with locals := l) e`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "eval_upd_locals_clock_eq"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem eval_upd_locals_clock_eq (t : LoopSemStateFiniteExact width F) (e : HolLoopExp width)
    (l : Spt (WordLocW width)) (ck : Nat) :
    eval { t with locals := l, clock := ck } e = eval { t with locals := l } e :=
  eval_upd_clock_eq { t with locals := l } e ck

theorem sptLookup_sptAlistInsert_not_mem (n : Nat) :
    ∀ (ns : List Nat) (vs : List (WordLocW width)) (l : Spt (WordLocW width)), n ∉ ns →
      sptLookup n (sptAlistInsert ns vs l) = sptLookup n l
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | m :: ns, v :: vs, l, hn => by
      simp only [sptAlistInsert]
      rw [sptLookup_sptInsert, if_neg (show ¬ n = m from fun h => hn (h ▸ List.mem_cons_self)),
        sptLookup_sptAlistInsert_not_mem n ns vs l (fun h => hn (List.mem_cons_of_mem _ h))]

/-- Exact HOL `get_vars_local_update_some_eq` (`loopPropsScript.sml:278-281`):
    `!ns vs st. ALL_DISTINCT ns /\ LENGTH ns = LENGTH vs ==>
      get_vars ns (st with locals := alist_insert ns vs st.locals) = SOME vs`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "get_vars_local_update_some_eq"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem get_vars_local_update_some_eq :
    ∀ (ns : List Nat) (vs : List (WordLocW width)) (st : LoopSemStateFiniteExact width F),
      ns.Nodup → ns.length = vs.length →
      getVars ns { st with locals := sptAlistInsert ns vs st.locals } = some vs
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | n :: ns, v :: vs, st, hd, hl => by
      have hn : n ∉ ns := (List.nodup_cons.mp hd).1
      have ih := get_vars_local_update_some_eq ns vs st (List.nodup_cons.mp hd).2
        (by simpa using hl)
      simp only [getVars, sptAlistInsert]
      rw [sptLookup_sptInsert, if_pos rfl]
      simp only [Option.bind_some]
      rw [getVars_congr ns _ { st with locals := sptAlistInsert ns vs st.locals }
        (fun m hm => by
          simp only
          rw [sptLookup_sptInsert, if_neg (show ¬ m = n from fun h => hn (h ▸ hm))]), ih]
      rfl

/-- Exact HOL `locals_touched_eq_eval_eq` (`loopPropsScript.sml:174-179`):
    `!s e t. s.globals = t.globals /\ s.memory = t.memory /\ s.mdomain = t.mdomain /\
      s.base_addr = t.base_addr ∧ s.top_addr = t.top_addr ∧
      (!n. MEM n (locals_touched e) ==> lookup n s.locals = lookup n t.locals) ==>
      eval t e = eval s e`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "locals_touched_eq_eval_eq"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem locals_touched_eq_eval_eq (s : LoopSemStateFiniteExact width F) :
    ∀ (e : HolLoopExp width) (t : LoopSemStateFiniteExact width F),
      s.globals = t.globals ∧ s.memory = t.memory ∧ s.mdomain = t.mdomain ∧
      s.baseAddr = t.baseAddr ∧ s.topAddr = t.topAddr ∧
      (∀ n, n ∈ holLoopLocalsTouched e → sptLookup n s.locals = sptLookup n t.locals) →
      eval t e = eval s e
  | .const _, _, _ => by simp only [eval]
  | .var v, t, ⟨_, _, _, _, _, hl⟩ => by
      simp only [eval]; exact (hl v (by simp [holLoopLocalsTouched])).symm
  | .lookup _, t, ⟨hg, _⟩ => by simp only [eval, hg]
  | .load a, t, ⟨hg, hm, hd, hb, ht, hl⟩ => by
      simp only [eval]
      rw [locals_touched_eq_eval_eq s a t ⟨hg, hm, hd, hb, ht,
        fun n hn => hl n (by simpa [holLoopLocalsTouched] using hn)⟩]
      simp only [memLoad, hm, hd]
  | .op o args, t, ⟨hg, hm, hd, hb, ht, hl⟩ => by
      simp only [eval]
      have hmap : ∀ e ∈ args, eval t e = eval s e := fun e he =>
        locals_touched_eq_eval_eq s e t ⟨hg, hm, hd, hb, ht, fun n hn => hl n (by
          simp only [holLoopLocalsTouched, List.mem_flatten, List.mem_map]
          exact ⟨_, ⟨⟨e, he⟩, List.mem_attach _ _, rfl⟩, hn⟩)⟩
      simp only [List.attach_map_val (f := eval t), List.attach_map_val (f := eval s),
        List.map_congr_left hmap]
  | .shift sh a b, t, ⟨hg, hm, hd, hb, ht, hl⟩ => by
      simp only [eval]
      rw [locals_touched_eq_eval_eq s a t ⟨hg, hm, hd, hb, ht,
          fun n hn => hl n (by simp [holLoopLocalsTouched, hn])⟩,
        locals_touched_eq_eval_eq s b t ⟨hg, hm, hd, hb, ht,
          fun n hn => hl n (by simp [holLoopLocalsTouched, hn])⟩]
  | .baseAddr, t, ⟨_, _, _, hb, _⟩ => by simp only [eval, hb]
  | .topAddr, t, ⟨_, _, _, _, ht, _⟩ => by simp only [eval, ht]

end LoopSemStateFiniteExact

end Flapjack
