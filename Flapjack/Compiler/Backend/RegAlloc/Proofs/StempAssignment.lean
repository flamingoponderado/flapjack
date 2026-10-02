import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.StempColouring
import Flapjack.Compiler.Backend.RegAlloc.Proofs.AtempAssignment
import Flapjack.Basis.Pure.MlList.SortPerm

/-!
# reg_allocProof: `Stemp` assignment and negative preferences

Ports of `reg_allocProofScript.sml:537-716` and `3207-3232`: `unbound_colour` returns an
unused colour at least `k`, assigning the `Stemp` tags gives every `Stemp` node a fixed
colour at least `k` while keeping the state invariant and `no_clash`, and the negative
move-preference oracle `neg_biased_pref` is a `good_neg_pref`. Renderings as in
`AtempAssignment`; HOL `SORTED (λx y. x ≤ y)` is `holSorted (· ≤ ·)` and the mllist sort's
Bool relation `fun x y => decide (x ≤ y)` is the same order.
-/

namespace Flapjack.RegAlloc

open Flapjack Flapjack.Translator.Monadic.MonadBase

private theorem le_transitive : holTransitive (fun x y : Nat => x ≤ y) :=
  fun _ _ _ ⟨h1, h2⟩ => Nat.le_trans h1 h2

/-- Exact HOL `SORTED_HEAD_LT` (`reg_allocProofScript.sml:537-548`); `col` and `h` are free
in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "SORTED_HEAD_LT"]
theorem sortedHeadLt (col h : Nat) :
    ∀ (ls : List Nat), col < h ∧ holSorted (fun x y : Nat => x ≤ y) (h :: ls) → col ∉ ls := by
  intro ls ⟨hlt, hs⟩ hm
  have := ((holSortedEq _ _ _ le_transitive).mp hs).2 col hm
  omega

/-- Exact HOL `unbound_colour_correct` (`reg_allocProofScript.sml:551-569`). HOL binds a
`k'` that occurs nowhere in the statement; its kernel type is a free type variable and it
is kept as the vacuous binder `(_k' : α)`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "unbound_colour_correct"]
theorem unboundColourCorrect {α : Type} :
    ∀ (ls : List Nat) (k : Nat) (_k' : α),
      holSorted (fun x y : Nat => x ≤ y) ls →
      k ≤ unboundColour k ls ∧ unboundColour k ls ∉ ls := by
  intro ls
  induction ls with
  | nil => intro k _ _; exact ⟨Nat.le_refl k, fun h => by cases h⟩
  | cons x xs ih =>
      intro k u hs
      have hxs := holSortedTl _ x xs hs
      by_cases hkx : k < x
      · simp only [unboundColour, if_pos hkx]
        refine ⟨Nat.le_refl k, fun hm => ?_⟩
        rcases List.mem_cons.mp hm with h | h
        · omega
        · exact sortedHeadLt k x xs ⟨hkx, hs⟩ h
      · by_cases hxk : x = k
        · simp only [unboundColour, if_neg hkx, if_pos hxk]
          obtain ⟨h1, h2⟩ := ih (k + 1) u hxs
          refine ⟨by omega, fun hm => ?_⟩
          rcases List.mem_cons.mp hm with h | h
          · omega
          · exact h2 h
        · simp only [unboundColour, if_neg hkx, if_neg hxk]
          obtain ⟨h1, h2⟩ := ih k u hxs
          refine ⟨h1, fun hm => ?_⟩
          rcases List.mem_cons.mp hm with h | h
          · omega
          · exact h2 h

/-- Exact HOL `assign_Stemp_tag_correct` (`reg_allocProofScript.sml:586-645`); `s`, `n`, `k`
and `prefs` are free in HOL, with `prefs` at its kernel type
`num -> num list -> ra_state -> (num option, state_exn) exc # ra_state`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "assign_Stemp_tag_correct"]
theorem assignStempTagCorrect (s : State) (n k : Nat)
    (prefs : Nat → List Nat → M State (Option Nat) StateException) :
    goodRaState s ∧ noClash s.adj_ls s.node_tag ∧ n < s.dim ∧ goodNegPref k prefs →
    ∃ s', assignStempTag k prefs n s = (.success (), s') ∧
      (∀ m, if n = m ∧ holEl n s.node_tag = .Stemp then
          ∃ k', holEl n s'.node_tag = .Fixed k' ∧ k ≤ k'
        else holEl m s'.node_tag = holEl m s.node_tag) ∧
      noClash s'.adj_ls s'.node_tag ∧ goodRaState s' ∧
      s' = { s with node_tag := s'.node_tag } := by
  intro ⟨hg, hnc, hn, hpref⟩
  have hnl : n < s.node_tag.length := by rw [hg.2.1]; exact hn
  have hal : n < s.adj_ls.length := by rw [hg.1]; exact hn
  have hadjd : ∀ v ∈ holEl n s.adj_ls, v < s.dim := fun v hv => by
    refine hg.2.2.2.2.2.2.1 _ ?_ v hv
    rw [holEl_eq_getElem _ _ hal]; exact List.getElem_mem _
  have hadj : ∀ v ∈ holEl n s.adj_ls, v < s.node_tag.length := fun v hv => by
    rw [hg.2.1]; exact hadjd v hv
  have hgset : ∀ t : Tag, goodRaState { s with node_tag := s.node_tag.set n t } := fun t => by
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩ := hg
    exact ⟨g1, (List.length_set ..).trans g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13,
      g14⟩
  have hother : ∀ t : Tag, ∀ m, n ≠ m → holEl m (s.node_tag.set n t) = holEl m s.node_tag :=
    fun t m hnm => by rw [holEl_set _ _ _ _ hnl, if_neg hnm]
  simp only [assignStempTag, Translator.Monadic.MonadBase.bind, nodeTagSubEqn, if_pos hnl]
  generalize ht : holEl n s.node_tag = t
  have hkeep : t ≠ .Stemp → ∃ s', (ret () : M State Unit StateException) s =
      (.success (), s') ∧
      (∀ m, if n = m ∧ t = .Stemp then ∃ k', holEl n s'.node_tag = .Fixed k' ∧ k ≤ k'
        else holEl m s'.node_tag = holEl m s.node_tag) ∧
      noClash s'.adj_ls s'.node_tag ∧ goodRaState s' ∧
      s' = { s with node_tag := s'.node_tag } := fun hne =>
    ⟨s, rfl, fun m => by rw [if_neg (fun h => hne h.2)], hnc, hg, rfl⟩
  cases t with
  | Fixed c => exact hkeep (by simp)
  | Atemp => exact hkeep (by simp)
  | Stemp =>
      simp only [Translator.Monadic.MonadBase.bind, adjLsSubEqn, if_pos hal,
        stExMapNodeTagSub _ s hadj]
      have hsorted : holSorted (fun x y : Nat => x ≤ y) (Basis.Pure.MlList.sort
          (fun x y => decide (x ≤ y))
          (((holEl n s.adj_ls).map fun i => holEl i s.node_tag).map tagCol)) := by
        have h := Basis.Pure.MlList.sortSorted (fun x y : Nat => decide (x ≤ y))
          (((holEl n s.adj_ls).map fun i => holEl i s.node_tag).map tagCol)
          ⟨fun a b c ⟨h1, h2⟩ => by simp only [decide_eq_true_eq] at *; omega,
           fun a b => by simp only [decide_eq_true_eq]; omega⟩
        simp only [decide_eq_true_eq] at h
        exact h
      have hbad : ∀ m, m ∈ holEl n s.adj_ls → ∀ c, holEl m s.node_tag = .Fixed c →
          c ∈ Basis.Pure.MlList.sort (fun x y => decide (x ≤ y))
            (((holEl n s.adj_ls).map fun i => holEl i s.node_tag).map tagCol) :=
        fun m hm c hc => by
          refine (Basis.Pure.MlList.sortMem c _ _).mpr ?_
          refine List.mem_map.mpr ⟨.Fixed c, List.mem_map.mpr ⟨m, hm, hc⟩, rfl⟩
      generalize Basis.Pure.MlList.sort (fun x y => decide (x ≤ y))
        (((holEl n s.adj_ls).map fun i => holEl i s.node_tag).map tagCol) = bads at hsorted hbad ⊢
      obtain ⟨res, hres, hp⟩ := hpref n bads s hg
      simp only [hres]
      have key : ∀ col, col ∉ bads → k ≤ col → ∃ s', updateNodeTag n (.Fixed col) s =
          (.success (), s') ∧
          (∀ m, if n = m ∧ True then ∃ k', holEl n s'.node_tag = .Fixed k' ∧ k ≤ k'
            else holEl m s'.node_tag = holEl m s.node_tag) ∧
          noClash s'.adj_ls s'.node_tag ∧ goodRaState s' ∧
          s' = { s with node_tag := s'.node_tag } := fun col hcol hk => by
        refine ⟨{ s with node_tag := s.node_tag.set n (.Fixed col) },
          by simp only [updateNodeTagEqn, if_pos hnl], fun m => ?_, ?_, hgset _, rfl⟩
        · by_cases hnm : n = m
          · rw [if_pos (by simp [hnm])]
            refine ⟨col, ?_, hk⟩
            show holEl n (s.node_tag.set n (.Fixed col)) = .Fixed col
            rw [holEl_set _ _ _ _ hnl, if_pos rfl]
          · rw [if_neg (fun h => hnm h.1)]
            exact hother _ m hnm
        · refine noClashLupdateFixed _ _ n col ⟨hg.2.2.2.2.2.2.2.2.2.2.2.2.2,
            fun ls hls v hv => ?_, hal, fun m ⟨hm, _⟩ hfx => hcol (hbad m hm col hfx), hnc⟩
          rw [hg.2.1]; exact hg.2.2.2.2.2.2.1 ls hls v hv
      cases res with
      | none =>
          obtain ⟨h1, h2⟩ := unboundColourCorrect bads k () hsorted
          exact key _ h2 h1
      | some y => exact key y hp.1 hp.2

/-- Exact HOL `assign_Stemps_FOREACH_lem` (`reg_allocProofScript.sml:648-685`); `prefs` is
free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "assign_Stemps_FOREACH_lem"]
theorem assignStempsForeachLem (prefs : Nat → List Nat → M State (Option Nat) StateException) :
    ∀ (ls : List Nat) (s : State) (k : Nat),
      goodRaState s ∧ noClash s.adj_ls s.node_tag ∧ (∀ v ∈ ls, v < s.dim) ∧
        goodNegPref k prefs →
      ∃ s', stExForeach ls (assignStempTag k prefs) s = (.success (), s') ∧
        noClash s'.adj_ls s'.node_tag ∧ goodRaState s' ∧
        (∀ m, if m ∈ ls ∧ holEl m s.node_tag = .Stemp then
            ∃ k', holEl m s'.node_tag = .Fixed k' ∧ k ≤ k'
          else holEl m s'.node_tag = holEl m s.node_tag) ∧
        s' = { s with node_tag := s'.node_tag } := by
  intro ls
  induction ls with
  | nil =>
      intro s k ⟨hg, hnc, _, _⟩
      exact ⟨s, rfl, hnc, hg, fun m => by rw [if_neg (fun h => by cases h.1)], rfl⟩
  | cons h t ih =>
      intro s k ⟨hg, hnc, hb, hpref⟩
      obtain ⟨s1, h1, hm1, hnc1, hg1, hs1⟩ :=
        assignStempTagCorrect s h k prefs ⟨hg, hnc, hb h List.mem_cons_self, hpref⟩
      obtain ⟨T1, rfl⟩ : ∃ T, s1 = { s with node_tag := T } := ⟨_, hs1⟩
      obtain ⟨s2, h2, hnc2, hg2, hm2, hs2⟩ := ih _ k
        ⟨hg1, hnc1, fun v hv => hb v (List.mem_cons_of_mem _ hv), hpref⟩
      obtain ⟨T2, rfl⟩ : ∃ T, s2 = { ({ s with node_tag := T1 } : State) with node_tag := T } :=
        ⟨_, hs2⟩
      refine ⟨_, ?_, hnc2, hg2, fun m => ?_, rfl⟩
      · simp only [stExForeach, ignoreBind, h1]
        exact h2
      have e1 := hm1 m
      have e2 := hm2 m
      change (if h = m ∧ holEl h s.node_tag = .Stemp then
          ∃ k', holEl h T1 = .Fixed k' ∧ k ≤ k'
        else holEl m T1 = holEl m s.node_tag) at e1
      change (if m ∈ t ∧ holEl m T1 = .Stemp then ∃ k', holEl m T2 = .Fixed k' ∧ k ≤ k'
        else holEl m T2 = holEl m T1) at e2
      change (if m ∈ h :: t ∧ holEl m s.node_tag = .Stemp then
          ∃ k', holEl m T2 = .Fixed k' ∧ k ≤ k'
        else holEl m T2 = holEl m s.node_tag)
      by_cases hc : m ∈ h :: t ∧ holEl m s.node_tag = .Stemp
      · rw [if_pos hc]
        by_cases hhm : h = m
        · subst hhm
          rw [if_pos ⟨rfl, hc.2⟩] at e1
          obtain ⟨k1, hk1, hkk⟩ := e1
          rw [if_neg (fun h' => by rw [hk1] at h'; cases h'.2)] at e2
          exact ⟨k1, e2.trans hk1, hkk⟩
        · rw [if_neg (fun h' => hhm h'.1)] at e1
          have hmt : m ∈ t := by
            rcases List.mem_cons.mp hc.1 with h' | h'
            · exact absurd h'.symm hhm
            · exact h'
          rw [if_pos ⟨hmt, e1.trans hc.2⟩] at e2
          exact e2
      · rw [if_neg hc]
        have hn1 : ¬ (h = m ∧ holEl h s.node_tag = .Stemp) := fun ⟨hhm, ha⟩ =>
          hc ⟨hhm ▸ List.mem_cons_self, hhm ▸ ha⟩
        rw [if_neg hn1] at e1
        have hn2 : ¬ (m ∈ t ∧ holEl m T1 = .Stemp) := fun ⟨hmt, ha⟩ =>
          hc ⟨List.mem_cons_of_mem _ hmt, e1 ▸ ha⟩
        rw [if_neg hn2] at e2
        exact e2.trans e1

/-- Exact HOL `assign_Stemps_correct` (`reg_allocProofScript.sml:687-716`); `s`, `k` and
`prefs` are free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "assign_Stemps_correct"]
theorem assignStempsCorrect (s : State) (k : Nat)
    (prefs : Nat → List Nat → M State (Option Nat) StateException) :
    goodRaState s ∧ noClash s.adj_ls s.node_tag ∧ goodNegPref k prefs →
    ∃ s', assignStemps k prefs s = (.success (), s') ∧
      noClash s'.adj_ls s'.node_tag ∧ goodRaState s' ∧
      s' = { s with node_tag := s'.node_tag } ∧
      ∀ m, m < s.node_tag.length →
        if holEl m s.node_tag = .Stemp then ∃ k', holEl m s'.node_tag = .Fixed k' ∧ k ≤ k'
        else holEl m s'.node_tag = holEl m s.node_tag := by
  intro ⟨hg, hnc, hpref⟩
  obtain ⟨s', h, hnc', hg', hm, hs'⟩ := assignStempsForeachLem prefs (List.range s.dim) s k
    ⟨hg, hnc, fun v hv => List.mem_range.mp hv, hpref⟩
  refine ⟨s', ?_, hnc', hg', hs', fun m hml => ?_⟩
  · simp only [assignStemps, Translator.Monadic.MonadBase.bind, getDim, ret]
    exact h
  · have hmd : m < s.dim := hg.2.1 ▸ hml
    have e := hm m
    by_cases hst : holEl m s.node_tag = .Stemp
    · rw [if_pos ⟨List.mem_range.mpr hmd, hst⟩] at e
      rw [if_pos hst]; exact e
    · rw [if_neg (fun h => hst h.2)] at e
      rw [if_neg hst]; exact e

/-- Exact HOL `neg_first_match_col_correct` (`reg_allocProofScript.sml:3207-3219`); `k` is
free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "neg_first_match_col_correct"]
theorem negFirstMatchColCorrect (k : Nat) :
    ∀ (x ks : List Nat) (s : State),
      ∃ res, negFirstMatchCol k ks x s = (res, s) ∧
        match res with
        | .failure v => v = .Subscript
        | .success (some c) => c ∉ ks ∧ k ≤ c
        | _ => True := by
  intro x
  induction x with
  | nil => intro ks s; exact ⟨.success none, rfl, trivial⟩
  | cons y ys ih =>
      intro ks s
      by_cases hy : y < s.node_tag.length
      · simp only [negFirstMatchCol, Translator.Monadic.MonadBase.bind, nodeTagSubEqn, if_pos hy]
        cases holEl y s.node_tag with
        | Fixed m =>
            by_cases hm : m ∈ ks ∨ m < k
            · simp only [if_pos hm]
              exact ih ks s
            · simp only [if_neg hm]
              exact ⟨.success (some m), rfl, fun h => hm (Or.inl h), by omega⟩
        | Atemp => exact ih ks s
        | Stemp => exact ih ks s
      · exact ⟨.failure .Subscript, by simp only [negFirstMatchCol,
          Translator.Monadic.MonadBase.bind, nodeTagSubEqn, if_neg hy], rfl⟩

/-- Exact HOL `good_neg_pref_neg_biased_pref` (`reg_allocProofScript.sml:3221-3232`); `k`
and `t` are free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "good_neg_pref_neg_biased_pref"]
theorem goodNegPrefNegBiasedPref (k : Nat) (t : Spt (List Nat)) :
    goodNegPref k (negBiasedPref k t) := by
  intro n bads s hg
  by_cases hn : n < s.dim
  · have key : ∀ vs, ∃ res, handleSubscript (negFirstMatchCol k bads vs)
        (ret none : M State (Option Nat) StateException) s = (.success res, s) ∧
        match res with
        | none => True
        | some c => c ∉ bads ∧ k ≤ c := fun vs => by
      obtain ⟨res, hres, hp⟩ := negFirstMatchColCorrect k vs bads s
      simp only [handleSubscript, hres]
      cases res with
      | success r =>
          refine ⟨r, rfl, ?_⟩
          cases r with
          | none => trivial
          | some c => exact hp
      | failure e =>
          cases hp
          exact ⟨none, rfl, trivial⟩
    simp only [negBiasedPref, Translator.Monadic.MonadBase.bind, getDim, if_pos hn]
    cases sptLookup n t with
    | none =>
        obtain ⟨res, h1, h2⟩ := key []
        refine ⟨res, h1, ?_⟩
        cases res
        · trivial
        · exact h2
    | some vs =>
        obtain ⟨res, h1, h2⟩ := key vs
        refine ⟨res, h1, ?_⟩
        cases res
        · trivial
        · exact h2
  · exact ⟨none, by simp only [negBiasedPref, Translator.Monadic.MonadBase.bind, getDim,
      if_neg hn, ret], trivial⟩

end Flapjack.RegAlloc
