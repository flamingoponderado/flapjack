import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Leaves
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.MoveStoreConsts

/-!
# `evaluate_remove_dead` Move case

The `Move` case of `word_allocProofScript.sml:3900-4472` `evaluate_remove_dead`
(Resume block 3958): `remove_dead` keeps only the moves whose destination is live,
and replaces an empty filtered move by `Skip`.
-/

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

namespace EvaluateRemoveDeadMoveWitnesses
/-- Roundtrip for the evaluator's actual imported canonical state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end EvaluateRemoveDeadMoveWitnesses

/-- Looking up a destination after a parallel move whose values are computed from
the sources: the first move to that destination decides (Flapjack infrastructure
for HOL's `lookup_alist_insert`/`ALOOKUP_ZIP` reasoning). -/
theorem sptLookup_alistInsertMoves {α : Type} (g : Nat → α) (m : Spt α) (k : Nat) :
    ∀ l : List (Nat × Nat),
      sptLookup k (LoopSemStateFiniteExact.sptAlistInsert (l.map Prod.fst)
          ((l.map Prod.snd).map g) m) =
        match l.find? (fun x => x.1 == k) with
        | some x => some (g x.2)
        | none => sptLookup k m
  | [] => by simp [LoopSemStateFiniteExact.sptAlistInsert]
  | (a, b) :: l => by
      simp only [List.map_cons, LoopSemStateFiniteExact.sptAlistInsert, List.find?_cons]
      by_cases h : a = k
      · subst h; simp [sptLookup_sptInsert_same]
      · have h' : (a == k) = false := by simpa using h
        rw [sptLookup_sptInsert_ne a k _ _ (Ne.symm h), h']
        exact sptLookup_alistInsertMoves g m k l

/-- Filtering a move list by a predicate that holds for every move to `k` keeps the
first move to `k` (Flapjack infrastructure). -/
theorem find?_filter_moves (q : Nat × Nat → Bool) (k : Nat) (hq : ∀ x, x.1 = k → q x = true) :
    ∀ l : List (Nat × Nat),
      (l.filter q).find? (fun x => x.1 == k) = l.find? (fun x => x.1 == k)
  | [] => rfl
  | x :: l => by
      have ih := find?_filter_moves q k hq l
      by_cases h : x.1 = k
      · simp [hq x h, h]
      · by_cases hx : q x = true
        · simp [hx, h, ih]
        · simp [hx, h, ih]

/-- `get_vars` reads only the locals (Flapjack infrastructure). -/
theorem getVarsLocalsEq {width : Nat} [NeZero width] {C F : Type}
    (s s' : WordSemStateFiniteExact width C F) (h : s.locals = s'.locals) :
    ∀ ls : List Nat, WordSemStateFiniteExact.getVars ls s = WordSemStateFiniteExact.getVars ls s'
  | [] => rfl
  | x :: xs => by
      simp only [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, h,
        getVarsLocalsEq s s' h xs]

/-- HOL `evaluate_remove_dead`, `Move` case (Resume 3958). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_Move {width : Nat} [NeZero width] {C F : Type} (pri : Nat)
    (moves : List (Nat × Nat)) :
    removeDeadGoal C F (.move pri moves : WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, -, hrd, herr⟩
  rw [evaluate] at hev
  by_cases hnd : (moves.map Prod.fst).Nodup
  case neg =>
    rw [if_neg hnd] at hev; simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  rw [if_pos hnd] at hev
  cases hgv : WordSemStateFiniteExact.getVars (moves.map Prod.snd) st with
  | none => rw [hgv] at hev; simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  | some vs =>
  rw [hgv] at hev
  simp only [Prod.mk.injEq] at hev
  obtain ⟨rfl, rfl⟩ := hev
  have hdomall : ∀ x, x ∈ moves.map Prod.snd → sptDomain st.locals x :=
    (getVarsExists st _).mp ⟨vs, hgv⟩
  obtain ⟨z, hz, hzeq⟩ := getVarsEq _ st hdomall
  rw [hgv, Option.some.injEq] at hz
  subst hz
  subst hzeq
  -- every move to a live destination survives the filter
  have hq : ∀ k, sptDomain live k → ∀ x : Nat × Nat, x.1 = k →
      decide (sptLookup x.1 live = some ()) = true := by
    intro k hk x hx
    subst hx
    simp only [decide_eq_true_eq]
    cases h : sptLookup x.1 live with
    | none => simp [sptDomain, h] at hk
    | some u => rfl
  simp only [removeDead] at hrd
  split at hrd
  · rename_i hemp
    simp only [Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    refine ⟨t, tstore, by rw [evaluate]; rfl, ?_, hs⟩
    intro k v ⟨hk, hv⟩
    simp only [WordSemStateFiniteExact.setVars] at hv
    rw [sptLookup_alistInsertMoves] at hv
    cases hf : moves.find? (fun x => x.1 == k) with
    | some x =>
      have hx := List.mem_of_find?_eq_some hf
      have hxk : x.1 = k := by simpa using List.find?_some hf
      have : x ∈ moves.filter (fun p => decide (sptLookup p.1 live = some ())) :=
        List.mem_filter.mpr ⟨hx, hq k hk x hxk⟩
      rw [hemp] at this
      cases this
    | none => rw [hf] at hv; exact hl k v ⟨hk, hv⟩
  · rename_i hne
    simp only [Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    generalize hF : moves.filter (fun p => decide (sptLookup p.1 live = some ())) = mv at hne hl ⊢
    have hsub : mv.Sublist moves := hF ▸ List.filter_sublist
    have hndF : (mv.map Prod.fst).Nodup := hnd.sublist (hsub.map _)
    have hgvF : WordSemStateFiniteExact.getVars (mv.map Prod.snd) st =
        some ((mv.map Prod.snd).map fun x => holThe (sptLookup x st.locals)) := by
      obtain ⟨z, hz, rfl⟩ := getVarsEq (mv.map Prod.snd) st
        (fun x hx => hdomall x ((hsub.map _).subset hx))
      exact hz
    have hgvT : WordSemStateFiniteExact.getVars (mv.map Prod.snd) ({ st with locals := t, store := tstore } :
        WordSemStateFiniteExact width C F) =
        some ((mv.map Prod.snd).map fun x => holThe (sptLookup x st.locals)) :=
      (getVarsLocalsEq { st with locals := t, store := tstore } { st with locals := t } rfl _).trans <| strongLocalsRelIGetVars' (mv.map Prod.snd) _ st t _
        ⟨fun x hx => (sptDomain_numsetIns _ _ _).mpr (Or.inr hx), hl, hgvF⟩
    refine ⟨LoopSemStateFiniteExact.sptAlistInsert (mv.map Prod.fst)
        ((mv.map Prod.snd).map fun x => holThe (sptLookup x st.locals)) t, tstore, ?_, ?_, hs⟩
    · rw [evaluate, if_pos hndF, hgvT]; rfl
    · intro k v ⟨hk, hv⟩
      simp only [WordSemStateFiniteExact.setVars] at hv
      simp only [id]
      rw [sptLookup_alistInsertMoves] at hv ⊢
      rw [← hF, find?_filter_moves _ k (hq k hk) moves]
      cases hf : moves.find? (fun x => x.1 == k) with
      | some x => rw [hf] at hv; exact hv
      | none =>
        rw [hf] at hv
        have hnm : k ∉ mv.map Prod.fst := by
          intro hm
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
          have := List.find?_eq_none.mp hf x ((hsub).subset hx)
          simp at this
        exact hl k v ⟨(sptDomain_numsetIns _ _ _).mpr
          (Or.inl ((sptDomain_foldr_sptDelete _ _ _).mpr ⟨hk, hnm⟩)), hv⟩

end Flapjack.WordAlloc
