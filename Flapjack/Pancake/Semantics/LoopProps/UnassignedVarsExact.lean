import Flapjack.Pancake.Semantics.LoopProps.NestedSeqExact
import Flapjack.Pancake.LoopLang.AssignedVars

/-!
# loopProps `unassigned_vars_evaluate_same` over the exact evaluator

Counterpart of `cakeml/pancake/semantics/loopPropsScript.sml`'s
`unassigned_vars_evaluate_same` (line 332) over `LoopSemStateFiniteExact.evaluate`,
`holLoopAssignedVars` and `survivesHOLExact` (bead `flapjack-pxgp.14`).
-/

namespace Flapjack

theorem sptLookup_sptMkBN {α : Type} (k : Nat) (l r : Spt α) :
    sptLookup k (sptMkBN l r) = sptLookup k (.bn l r) := by
  unfold sptMkBN; split <;> simp_all [sptLookup]

theorem sptLookup_sptMkBS {α : Type} (k : Nat) (l : Spt α) (v : α) (r : Spt α) :
    sptLookup k (sptMkBS l v r) = sptLookup k (.bs l v r) := by
  unfold sptMkBS; split <;> simp_all [sptLookup]

/-- HOL `sptree$lookup_inter`-style fact for the heterogeneous `inter`:
    `lookup k (inter t1 t2) = if lookup k t2 <> NONE then lookup k t1 else NONE`.
    Local proof support (HOL library `sptree`, no tag). -/
theorem sptLookup_sptInter {α β : Type} :
    ∀ (t1 : Spt α) (t2 : Spt β) (k : Nat),
      sptLookup k (sptInter t1 t2) = if (sptLookup k t2).isSome then sptLookup k t1 else none
  | .ln, t2, k => by simp [sptInter]
  | .ls v, t2, k => by
      cases t2 <;> simp only [sptInter] <;> by_cases hk : k = 0 <;> simp [sptLookup, hk]
  | .bn l r, t2, k => by
      cases t2 with
      | ln => simp [sptInter]
      | ls _ => simp only [sptInter]; by_cases hk : k = 0 <;> simp [sptLookup, hk]
      | bn l' r' =>
        simp only [sptInter, sptLookup_sptMkBN]
        by_cases hk : k = 0
        · simp [sptLookup, hk]
        · by_cases he : k % 2 = 0
          · simp only [sptLookup, hk, he, if_false, if_true, sptLookup_sptInter l l']
          · simp only [sptLookup, hk, he, if_false, sptLookup_sptInter r r']
      | bs l' _ r' =>
        simp only [sptInter, sptLookup_sptMkBN]
        by_cases hk : k = 0
        · simp [sptLookup, hk]
        · by_cases he : k % 2 = 0
          · simp only [sptLookup, hk, he, if_false, if_true, sptLookup_sptInter l l']
          · simp only [sptLookup, hk, he, if_false, sptLookup_sptInter r r']
  | .bs l v r, t2, k => by
      cases t2 with
      | ln => simp [sptInter]
      | ls _ => simp only [sptInter]; by_cases hk : k = 0 <;> simp [sptLookup, hk]
      | bn l' r' =>
        simp only [sptInter, sptLookup_sptMkBN]
        by_cases hk : k = 0
        · simp [sptLookup, hk]
        · by_cases he : k % 2 = 0
          · simp only [sptLookup, hk, he, if_false, if_true, sptLookup_sptInter l l']
          · simp only [sptLookup, hk, he, if_false, sptLookup_sptInter r r']
      | bs l' _ r' =>
        simp only [sptInter, sptLookup_sptMkBS]
        by_cases hk : k = 0
        · simp [sptLookup, hk]
        · by_cases he : k % 2 = 0
          · simp only [sptLookup, hk, he, if_false, if_true, sptLookup_sptInter l l']
          · simp only [sptLookup, hk, he, if_false, sptLookup_sptInter r r']

namespace LoopPropsUnassignedFiniteSupport

/-- Local same-module witness for the canonical finite-support
`LoopSemStateFiniteExact` carrier used by the `fmap_as_finite_support := [globals]`
qualified port in this module (re-exports the checked witness of
`Flapjack/Pancake/Semantics/LoopSemStateExact.lean`). -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

end LoopPropsUnassignedFiniteSupport

namespace LoopSemStateFiniteExact

variable {width : Nat} [NeZero width] {F : Type}

/-- The HOL result condition `res = NONE ∨ (∃n. res = SOME (Continue n)) ∨
    (∃n. res = SOME (Break n))` of `unassigned_vars_evaluate_same`. -/
def UnassignedGoodRes (res : Option (LoopResultExact width)) : Prop :=
  res = none ∨ (∃ k, res = some (.continue k)) ∨ (∃ k, res = some (.break k))

theorem cutState_lookup {live : NumSet} {s s' : LoopSemStateFiniteExact width F} {n : Nat}
    (h : cutState live s = some s') (hn : (sptLookup n live).isSome = true) :
    sptLookup n s'.locals = sptLookup n s.locals := by
  unfold cutState at h
  split at h
  · cases h; simp only; rw [sptLookup_sptInter, if_pos hn]
  · cases h

theorem cutRes_lookup {live : NumSet} {r r' : Option (LoopResultExact width)}
    {s s' : LoopSemStateFiniteExact width F} {n : Nat}
    (h : cutRes live (r, s) = (r', s')) (hg : UnassignedGoodRes r')
    (hn : (sptLookup n live).isSome = true) :
    sptLookup n s'.locals = sptLookup n s.locals := by
  unfold cutRes at h
  cases r with
  | some x => simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl
  | none =>
    simp only at h
    cases hc : cutState live s with
    | none =>
      rw [hc] at h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      simp [UnassignedGoodRes] at hg
    | some cut =>
      rw [hc] at h; simp only at h
      split at h
      · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        simp [UnassignedGoodRes] at hg
      · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
        simp only [decClock]; exact cutState_lookup hc hn

theorem cutRes_good {live : NumSet} {r r' : Option (LoopResultExact width)}
    {s s' : LoopSemStateFiniteExact width F}
    (h : cutRes live (r, s) = (r', s')) (hg : UnassignedGoodRes r') : UnassignedGoodRes r := by
  cases r with
  | some x => unfold cutRes at h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact hg
  | none => exact Or.inl rfl

theorem cutRes_none_bad {live : NumSet} {r : Option (LoopResultExact width)}
    {s s' : LoopSemStateFiniteExact width F}
    (h : cutRes live (none, s) = (r, s')) (hg : UnassignedGoodRes r) : r = none := by
  unfold cutRes at h
  simp only at h
  cases hc : cutState live s with
  | none => rw [hc] at h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
            simp [UnassignedGoodRes] at hg
  | some cut =>
    rw [hc] at h; simp only at h
    split at h
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp [UnassignedGoodRes] at hg
    · simp only [Prod.mk.injEq] at h; exact h.1.symm

theorem exitLoop_good {r : Option (LoopResultExact width)}
    (hg : UnassignedGoodRes (exitLoop r)) : UnassignedGoodRes r := by
  rcases r with _ | (_ | _ | k | k | _ | _ | _) <;> simp [exitLoop, UnassignedGoodRes] at hg ⊢

theorem sptLookup_setVar_ne {m n : Nat} (hmn : n ≠ m) (w : WordLocW width)
    (s : LoopSemStateFiniteExact width F) :
    sptLookup n (setVar m w s).locals = sptLookup n s.locals := by
  simp only [setVar]; rw [sptLookup_sptInsert, if_neg hmn]

theorem memStore_locals {a : BitVec width} {w : WordLocW width}
    {s st : LoopSemStateFiniteExact width F} (h : memStore a w s = some st) :
    st.locals = s.locals := by
  unfold memStore at h; split at h <;> simp at h; subst h; rfl

theorem loopArith_lookup {op : LoopArith} {s st : LoopSemStateFiniteExact width F} {n : Nat}
    (h : loopArith s op = some st) (hna : n ∉ holLoopAssignedVars (.arith op : HolLoopProg width)) :
    sptLookup n st.locals = sptLookup n s.locals := by
  cases op <;> simp only [holLoopAssignedVars, List.mem_cons, not_or,
    List.not_mem_nil, or_false] at hna <;> simp only [loopArith] at h <;> split at h <;>
    (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp only [sptLookup_setVar_ne, hna, ne_eq, not_false_eq_true]

theorem shMemOp_lookup (op : CrepMemOp) (v : Nat) (a : BitVec width)
    (s : LoopSemStateFiniteExact width F) {n : Nat} (hnv : n ≠ v)
    (hg : UnassignedGoodRes (shMemOp op v a s).1) :
    sptLookup n (shMemOp op v a s).2.locals = sptLookup n s.locals := by
  revert hg
  cases op <;> simp only [shMemOp, shMemLoad, shMemStore] <;> (repeat' split) <;>
    simp [UnassignedGoodRes, sptLookup_setVar_ne hnv]

/-- Exact HOL `unassigned_vars_evaluate_same` (`loopPropsScript.sml:332-338`):
    `!p s res t n v. evaluate (p,s) = (res,t) /\
      (res = NONE ∨ (∃n. res = SOME (Continue n)) ∨ (∃n. res = SOME (Break n))) /\
      lookup n s.locals = SOME v /\ ~MEM n (assigned_vars p) /\ survives n p ==>
      lookup n t.locals = lookup n s.locals`. HOL's `survives n p` (a `bool`) is
    `survivesHOLExact n p = true`, `assigned_vars` is `holLoopAssignedVars`, and
    the result condition is spelled out by `UnassignedGoodRes`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "unassigned_vars_evaluate_same"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem unassigned_vars_evaluate_same (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (res : Option (LoopResultExact width)) (t : LoopSemStateFiniteExact width F) (n : Nat)
    (v : WordLocW width) :
    evaluate p s = (res, t) ∧ UnassignedGoodRes res ∧ sptLookup n s.locals = some v ∧
      n ∉ holLoopAssignedVars p ∧ survivesHOLExact n p = true →
      sptLookup n t.locals = sptLookup n s.locals := by
  have key : ∀ (x : Nat × Nat) (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F),
      (s.clock, sizeOf p) = x → ∀ res t, evaluate p s = (res, t) → UnassignedGoodRes res →
      sptLookup n s.locals = some v → n ∉ holLoopAssignedVars p → survivesHOLExact n p = true →
      sptLookup n t.locals = sptLookup n s.locals := by
    intro x
    induction x using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
    | h x ih0 =>
      intro p s hx
      have ih : ∀ (p' : HolLoopProg width) (s' : LoopSemStateFiniteExact width F),
          Prod.Lex (· < ·) (· < ·) (s'.clock, sizeOf p') (s.clock, sizeOf p) →
          ∀ res t, evaluate p' s' = (res, t) → UnassignedGoodRes res →
          sptLookup n s'.locals = some v → n ∉ holLoopAssignedVars p' →
          survivesHOLExact n p' = true → sptLookup n t.locals = sptLookup n s'.locals :=
        fun p' s' hlt => ih0 _ (hx ▸ hlt) p' s' rfl
      clear ih0 hx
      intro res t h hg hv hna hsv
      cases p
      case seq c1 c2 =>
        simp only [holLoopAssignedVars, List.mem_append, not_or] at hna
        simp only [survivesHOLExact, Bool.and_eq_true] at hsv
        rw [evaluate_seq] at h
        cases he : evaluate c1 s with
        | mk r1 s1 =>
          rw [he] at h
          cases r1 with
          | none =>
            simp only at h
            have e1 := ih c1 s (lexLt (Nat.le_refl _) (by simp +arith)) _ _ he (Or.inl rfl) hv hna.1 hsv.1
            rw [← e1] at hv ⊢
            exact ih c2 s1 (lexLt (evaluate_clock _ _ _ _ he) (by simp +arith)) _ _ h hg hv hna.2 hsv.2
          | some x =>
            simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            exact ih c1 s (lexLt (Nat.le_refl _) (by simp +arith)) _ _ he hg hv hna.1 hsv.1
      case ite cmp r1 ri c1 c2 live =>
        simp only [holLoopAssignedVars, List.mem_append, not_or] at hna
        simp only [survivesHOLExact, Bool.and_eq_true] at hsv
        rw [evaluate] at h
        have step : ∀ c, Prod.Lex (· < ·) (· < ·) (s.clock, sizeOf c)
              (s.clock, sizeOf (HolLoopProg.ite cmp r1 ri c1 c2 live)) →
            n ∉ holLoopAssignedVars c → survivesHOLExact n c = true →
            cutRes live (evaluate c s) = (res, t) →
            sptLookup n t.locals = sptLookup n s.locals := by
          intro c hlex hnac hsvc hcut
          cases he : evaluate c s with
          | mk rr ss =>
            rw [he] at hcut
            rw [cutRes_lookup hcut hg hsv.2]
            exact ih c s hlex _ _ he (cutRes_good hcut hg) hv hnac hsvc
        split at h
        · split at h
          · exact step c1 (lexLt (Nat.le_refl _) (by simp +arith)) hna.1 hsv.1.1 h
          · exact step c2 (lexLt (Nat.le_refl _) (by simp +arith)) hna.2 hsv.1.2 h
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp [UnassignedGoodRes] at hg
      case mark q =>
        simp only [holLoopAssignedVars] at hna
        simp only [survivesHOLExact] at hsv
        rw [evaluate] at h
        exact ih q s (lexLt (Nat.le_refl _) (by simp +arith)) _ _ h hg hv hna hsv
      case loop li body lo =>
        simp only [holLoopAssignedVars] at hna
        simp only [survivesHOLExact, Bool.and_eq_true] at hsv
        obtain ⟨⟨hli, hlo⟩, hsb⟩ := hsv
        rw [evaluate] at h
        split at h
        · rename_i s1 hc
          have hs1 := cutRes_none_clock hc
          have e1 := cutRes_lookup hc (Or.inl rfl) hli
          rw [fix_clock_evaluate] at h
          rw [← e1] at hv ⊢
          cases hb : evaluate body s1 with
          | mk rb s2 =>
            rw [hb] at h
            have hs2 : s2.clock < s.clock := Nat.lt_of_le_of_lt (evaluate_clock _ _ _ _ hb) hs1
            have ihb := fun hgb => ih body s1 (lexLtClock hs1) _ _ hb hgb hv hna hsb
            rcases rb with _ | (vs | e | k | k | _ | o | _)
            · simp only at h
              rw [← ihb (Or.inl rfl)] at hv ⊢
              exact ih _ s2 (lexLtClock hs2) _ _ h hg hv hna (by simp [survivesHOLExact, hli, hlo, hsb])
            · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              exact ihb (exitLoop_good hg)
            · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              exact ihb (exitLoop_good hg)
            · cases k with
              | zero =>
                simp only at h
                rw [cutRes_lookup h hg hlo]
                exact ihb (Or.inr (Or.inr ⟨0, rfl⟩))
              | succ k =>
                simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                exact ihb (Or.inr (Or.inr ⟨k + 1, rfl⟩))
            · cases k with
              | zero =>
                simp only at h
                rw [← ihb (Or.inr (Or.inl ⟨0, rfl⟩))] at hv ⊢
                exact ih _ s2 (lexLtClock hs2) _ _ h hg hv hna
                  (by simp [survivesHOLExact, hli, hlo, hsb])
              | succ k =>
                simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                exact ihb (Or.inr (Or.inl ⟨k + 1, rfl⟩))
            · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              simp [exitLoop, UnassignedGoodRes] at hg
            · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              simp [exitLoop, UnassignedGoodRes] at hg
            · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              simp [exitLoop, UnassignedGoodRes] at hg
        · rename_i hnot
          have := cutRes_none_bad h hg
          subst this
          exact (hnot t h).elim
      case call ret dest args handler =>
        rw [evaluate] at h
        split at h
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp [UnassignedGoodRes] at hg
        rename_i argvals _
        split at h
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp [UnassignedGoodRes] at hg
        rename_i env prog _
        cases ret with
        | none =>
          simp only at h
          split at h
          · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp [UnassignedGoodRes] at hg
          split at h
          · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp [UnassignedGoodRes] at hg
          split at h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, -⟩ := h <;>
            simp_all [UnassignedGoodRes]
        | some nl =>
          obtain ⟨ns, live⟩ := nl
          simp only at h
          split at h
          · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp [UnassignedGoodRes] at hg
          have hlive : (sptLookup n live).isSome = true := by
            cases handler with
            | none => simpa [survivesHOLExact] using hsv
            | some hd =>
              obtain ⟨_, _, _, _⟩ := hd
              simp only [survivesHOLExact, Bool.and_eq_true] at hsv; exact hsv.1.1.1
          have hns : n ∉ ns := by
            cases handler with
            | none => simpa [holLoopAssignedVars] using hna
            | some hd =>
              obtain ⟨_, _, _, _⟩ := hd
              simp only [holLoopAssignedVars, List.mem_append, List.mem_cons, not_or] at hna
              exact hna.1.1
          split at h
          · rename_i s1 hc
            have hs1 := cutRes_none_clock hc
            have e1 := cutRes_lookup hc (Or.inl rfl) hlive
            rw [fix_clock_evaluate] at h
            cases he : evaluate prog { s1 with locals := env } with
            | mk rc st =>
              rw [he] at h
              have hst : st.clock < s.clock :=
                Nat.lt_of_le_of_lt (evaluate_clock _ _ _ _ he) hs1
              rcases rc with _ | (vs | exn | k | k | _ | o | _)
              · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
                simp [UnassignedGoodRes] at hg
              · simp only at h
                split at h
                · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
                  simp [UnassignedGoodRes] at hg
                cases handler with
                | none =>
                  simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                  simp only [setVars]
                  rw [sptLookup_sptAlistInsert_not_mem n _ _ _ hns, e1]
                | some hd =>
                  obtain ⟨m, hp, r, lo⟩ := hd
                  simp only [survivesHOLExact, Bool.and_eq_true] at hsv
                  simp only [holLoopAssignedVars, List.mem_append, List.mem_cons, not_or] at hna
                  simp only at h
                  cases he2 : evaluate r (setVars ns vs { st with locals := s1.locals }) with
                  | mk rr ss =>
                    rw [he2] at h
                    rw [cutRes_lookup h hg hsv.1.1.2, ← e1]
                    have hvU : sptLookup n (setVars ns vs { st with locals := s1.locals }).locals =
                        some v := by
                      simp only [setVars]; rw [sptLookup_sptAlistInsert_not_mem n _ _ _ hns, e1, hv]
                    have := ih r _ (lexLtClock (by simp only [setVars]; omega)) _ _ he2
                      (cutRes_good h hg) hvU hna.2 hsv.2
                    rw [this]; simp only [setVars]; rw [sptLookup_sptAlistInsert_not_mem n _ _ _ hns]
              · cases handler with
                | none =>
                  simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
                  simp [UnassignedGoodRes] at hg
                | some hd =>
                  obtain ⟨m, hp, r, lo⟩ := hd
                  simp only [survivesHOLExact, Bool.and_eq_true] at hsv
                  simp only [holLoopAssignedVars, List.mem_append, List.mem_cons, not_or] at hna
                  simp only at h
                  cases he2 : evaluate hp (setVar m exn { st with locals := s1.locals }) with
                  | mk rr ss =>
                    rw [he2] at h
                    rw [cutRes_lookup h hg hsv.1.1.2, ← e1]
                    have hvU : sptLookup n (setVar m exn { st with locals := s1.locals }).locals =
                        some v := by
                      rw [sptLookup_setVar_ne hna.1.2.1]; simp only; rw [e1, hv]
                    have := ih hp _ (lexLtClock (by simp only [setVar]; omega)) _ _ he2
                      (cutRes_good h hg) hvU hna.1.2.2 hsv.1.2
                    rw [this, sptLookup_setVar_ne hna.1.2.1]
              all_goals (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
                         simp [UnassignedGoodRes] at hg)
          · rename_i hnot
            have := cutRes_none_bad h hg
            subst this
            exact (hnot t h).elim
      case ffi idx p1 l1 p2 l2 cutset =>
        simp only [survivesHOLExact] at hsv
        rw [evaluate] at h
        revert h; repeat' split
        all_goals intro h
        all_goals (try (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h))
        all_goals (try (simp [UnassignedGoodRes] at hg; done))
        have hcl := cutState_lookup ‹cutState cutset s = some _› hsv
        exact hcl
      all_goals (rw [evaluate] at h)
      all_goals (revert h; repeat' split)
      all_goals intro h
      all_goals (try (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h))
      all_goals (try (simp [UnassignedGoodRes] at hg; done))
      all_goals (try rfl)
      all_goals (try (simp only [holLoopAssignedVars, List.mem_singleton] at hna
                      exact sptLookup_setVar_ne hna _ _))
      all_goals (try (simp only [holLoopAssignedVars] at hna; simp only [setVars]
                      exact sptLookup_sptAlistInsert_not_mem n _ _ _ hna))
      all_goals (try (rw [memStore_locals ‹memStore _ _ _ = some _›]))
      all_goals (try (exact loopArith_lookup ‹loopArith _ _ = some _› hna))
      all_goals (try (have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
                      simp only at h1 h2; rw [← h1] at hg; rw [← h2]
                      simp only [holLoopAssignedVars, List.mem_singleton] at hna
                      exact shMemOp_lookup _ _ _ _ hna hg))
  intro ⟨h, hg, hv, hna, hsv⟩
  exact key _ p s rfl res t h hg hv hna hsv

end LoopSemStateFiniteExact

end Flapjack
