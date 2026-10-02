import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.Colouring
import Flapjack.Compiler.Backend.RegAlloc.Proofs.AccessorEqns
import Flapjack.Compiler.Backend.RegAlloc.Proofs.Invariants
import Flapjack.Compiler.Backend.RegAlloc.Allocator

/-!
# reg_allocProof: colour removal and `Atemp` assignment

Ports of `reg_allocProofScript.sml:295-536` and `721-768`: `remove_colours` never changes
the state and returns the colours not used by fixed neighbours; updating a tag to `Stemp`,
or to a colour no neighbour uses, keeps `no_clash`; assigning the `Atemp` tags succeeds,
keeps the state invariant and `no_clash`, and leaves no `Atemp` node; and the biased
move-preference oracle `biased_pref` is a `good_pref`. HOL `EL` is the exact `holEl`,
`LUPDATE` is `List.set`, `set l ⊆ set l'` is pointwise list-membership implication, and
HOL `Abbrev P` is `P` (`markerTheory.Abbrev_def`).
-/

namespace Flapjack.RegAlloc

open Flapjack Flapjack.Translator.Monadic.MonadBase

private theorem good_adj' {s : State} (h : goodRaState s) {n : Nat} (hn : n < s.dim) :
    ∀ v ∈ holEl n s.adj_ls, v < s.dim := by
  have hmem : holEl n s.adj_ls ∈ s.adj_ls := by
    rw [holEl_eq_getElem _ _ (by rw [h.1]; exact hn)]; exact List.getElem_mem _
  exact h.2.2.2.2.2.2.1 _ hmem

/-- `remove_colours` returns without changing the state (Flapjack infrastructure). -/
private theorem removeColours_state :
    ∀ (adjs ks : List Nat) (s : State), ∃ r, removeColours adjs ks s = (r, s)
  | _, [], s => by cases ‹List Nat› <;> exact ⟨_, rfl⟩
  | [], _ :: _, s => ⟨_, rfl⟩
  | x :: xs, k :: ks, s => by
      by_cases hx : x < s.node_tag.length
      · simp only [removeColours, Translator.Monadic.MonadBase.bind, nodeTagSubEqn, if_pos hx]
        cases holEl x s.node_tag with
        | Fixed c =>
            obtain ⟨r, hr⟩ := removeColours_state xs ((k :: ks).filter fun y => y ≠ c) s
            simp only [hr]
            cases r <;> exact ⟨_, rfl⟩
        | Atemp =>
            obtain ⟨r, hr⟩ := removeColours_state xs (k :: ks) s
            simp only [hr]
            cases r <;> exact ⟨_, rfl⟩
        | Stemp =>
            obtain ⟨r, hr⟩ := removeColours_state xs (k :: ks) s
            simp only [hr]
            cases r <;> exact ⟨_, rfl⟩
      · exact ⟨.failure .Subscript, by simp only [removeColours,
          Translator.Monadic.MonadBase.bind, nodeTagSubEqn, if_neg hx]⟩

/-- Exact HOL `remove_colours_frame` (`reg_allocProofScript.sml:295-306`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "remove_colours_frame"]
theorem removeColoursFrame :
    ∀ (adjs ks : List Nat) (s : State) (res : Exc (List Nat) StateException) (s' : State),
      removeColours adjs ks s = (res, s') → s = s' := by
  intro adjs ks s res s' h
  obtain ⟨r, hr⟩ := removeColours_state adjs ks s
  rw [hr] at h
  exact (Prod.mk.inj h).2

/-- Exact HOL `remove_colours_success` (`reg_allocProofScript.sml:308-340`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "remove_colours_success"]
theorem removeColoursSuccess :
    ∀ (adjs ks : List Nat) (s : State) (ls : List Nat) (s' : State),
      removeColours adjs ks s = (.success ls, s') →
      (∀ x, x ∈ ls → x ∈ ks) ∧
        ∀ n, n ∈ adjs ∧ n < s'.node_tag.length →
          match holEl n s.node_tag with
          | .Fixed c => c ∉ ls
          | _ => True
  | adjs, [], s, ls, s', h => by
      cases adjs <;>
      · simp only [removeColours, ret, Prod.mk.injEq, Exc.success.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨(fun x hx => by cases hx), fun n _ => ?_⟩
        split
        · exact fun h => by cases h
        · trivial
  | [], k :: ks, s, ls, s', h => by
      simp only [removeColours, ret, Prod.mk.injEq, Exc.success.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun x hx => hx, fun n ⟨hn, _⟩ => by cases hn⟩
  | x :: xs, k :: ks, s, ls, s', h => by
      have hs := removeColoursFrame _ _ s _ s' h
      subst hs
      by_cases hx : x < s.node_tag.length
      · simp only [removeColours, Translator.Monadic.MonadBase.bind, nodeTagSubEqn,
          if_pos hx] at h
        generalize ht : holEl x s.node_tag = t at h
        cases t with
        | Fixed c =>
            obtain ⟨r, hr⟩ := removeColours_state xs ((k :: ks).filter fun y => y ≠ c) s
            simp only [hr] at h
            cases r with
            | failure e => simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h
            | success r =>
                simp only [ret, Prod.mk.injEq, Exc.success.injEq] at h
                obtain ⟨rfl, -⟩ := h
                obtain ⟨hsub, hfix⟩ := removeColoursSuccess xs _ s r s hr
                refine ⟨fun y hy => (List.mem_filter.mp (hsub y hy)).1, fun n ⟨hn, hnl⟩ => ?_⟩
                by_cases hnx : n ∈ xs
                · exact hfix n ⟨hnx, hnl⟩
                · rcases List.mem_cons.mp hn with rfl | hn
                  · rw [ht]
                    intro hc
                    have := (List.mem_filter.mp (hsub c hc)).2
                    simp at this
                  · exact absurd hn hnx
        | Atemp =>
            obtain ⟨r, hr⟩ := removeColours_state xs (k :: ks) s
            simp only [hr] at h
            cases r with
            | failure e => simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h
            | success r =>
                simp only [ret, Prod.mk.injEq, Exc.success.injEq] at h
                obtain ⟨rfl, -⟩ := h
                obtain ⟨hsub, hfix⟩ := removeColoursSuccess xs _ s r s hr
                refine ⟨hsub, fun n ⟨hn, hnl⟩ => ?_⟩
                by_cases hnx : n ∈ xs
                · exact hfix n ⟨hnx, hnl⟩
                · rcases List.mem_cons.mp hn with rfl | hn
                  · rw [ht]; trivial
                  · exact absurd hn hnx
        | Stemp =>
            obtain ⟨r, hr⟩ := removeColours_state xs (k :: ks) s
            simp only [hr] at h
            cases r with
            | failure e => simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h
            | success r =>
                simp only [ret, Prod.mk.injEq, Exc.success.injEq] at h
                obtain ⟨rfl, -⟩ := h
                obtain ⟨hsub, hfix⟩ := removeColoursSuccess xs _ s r s hr
                refine ⟨hsub, fun n ⟨hn, hnl⟩ => ?_⟩
                by_cases hnx : n ∈ xs
                · exact hfix n ⟨hnx, hnl⟩
                · rcases List.mem_cons.mp hn with rfl | hn
                  · rw [ht]; trivial
                  · exact absurd hn hnx
      · simp only [removeColours, Translator.Monadic.MonadBase.bind, nodeTagSubEqn,
          if_neg hx, Prod.mk.injEq, reduceCtorEq, false_and] at h

/-- `EL` of a `LUPDATE` without a range premise (Flapjack infrastructure). -/
private theorem holEl_set' {α : Type} [Nonempty α] (l : List α) (i j : Nat) (v : α) :
    holEl j (l.set i v) = if i = j ∧ i < l.length then v else holEl j l := by
  by_cases hi : i < l.length
  · rw [holEl_set _ _ _ _ hi]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos ⟨hij, hi⟩]
    · rw [if_neg hij, if_neg (fun h => hij h.1)]
  · rw [List.set_eq_of_length_le (by omega)]
    simp [hi]

/-- Exact HOL `no_clash_LUPDATE_Stemp` (`reg_allocProofScript.sml:342-352`); `adjls`, `tags`
and `n` are free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "no_clash_LUPDATE_Stemp"]
theorem noClashLupdateStemp (adjls : List (List Nat)) (tags : List Tag) (n : Nat) :
    noClash adjls tags → noClash adjls (tags.set n .Stemp) := by
  intro h x y he
  have hxy := h x y he
  rw [holEl_set', holEl_set']
  by_cases hx : n = x ∧ n < tags.length
  · rw [if_pos hx]; split <;> trivial
  · rw [if_neg hx]
    by_cases hy : n = y ∧ n < tags.length
    · rw [if_pos hy]; split <;> trivial
    · rw [if_neg hy]; exact hxy

/-- Exact HOL `no_clash_LUPDATE_Fixed` (`reg_allocProofScript.sml:354-387`); `adjls`, `tags`,
`n` and `x` are free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "no_clash_LUPDATE_Fixed"]
theorem noClashLupdateFixed (adjls : List (List Nat)) (tags : List Tag) (n x : Nat) :
    undirected adjls ∧ (∀ ls ∈ adjls, ∀ v ∈ ls, v < tags.length) ∧ n < adjls.length ∧
      (∀ m, m ∈ holEl n adjls ∧ m < tags.length → holEl m tags ≠ .Fixed x) ∧
      noClash adjls tags →
    noClash adjls (tags.set n (.Fixed x)) := by
  intro ⟨hu, hb, hn, hnb, h⟩ a b he
  have hab := h a b he
  have hinb : ∀ m, m ∈ holEl n adjls → m < tags.length := fun m hm => by
    refine hb _ ?_ m hm
    rw [holEl_eq_getElem _ _ hn]
    exact List.getElem_mem _
  rw [holEl_set', holEl_set']
  by_cases ha : n = a ∧ n < tags.length
  · obtain ⟨rfl, hnl⟩ := ha
    rw [if_pos ⟨rfl, hnl⟩]
    by_cases hb' : n = b ∧ n < tags.length
    · obtain ⟨rfl, -⟩ := hb'
      rw [if_pos ⟨rfl, hnl⟩]
      exact fun _ => rfl
    · rw [if_neg hb']
      have hbm : b ∈ holEl n adjls := he.2.2
      have hne := hnb b ⟨hbm, hinb b hbm⟩
      split
      · next c d h1 h2 =>
          cases h1
          intro hcd
          exact absurd (hcd ▸ h2) hne
      · trivial
  · rw [if_neg ha]
    by_cases hb' : n = b ∧ n < tags.length
    · obtain ⟨rfl, hnl⟩ := hb'
      rw [if_pos ⟨rfl, hnl⟩]
      have hea := hu a n he
      have ham : a ∈ holEl n adjls := hea.2.2
      have hne := hnb a ⟨ham, hinb a ham⟩
      split
      · next c d h1 h2 =>
          cases h2
          intro hcd
          exact absurd (hcd ▸ h1) hne
      · trivial
    · rw [if_neg hb']
      exact hab

/-- Exact HOL `remove_colours_succeeds` (`reg_allocProofScript.sml:389-400`). HOL binds `s`
twice (`∀adj ks s s.`): the kernel term is `∀adj ks (s:α) (s:ra_state)`, whose outer
`s : α` is shadowed and vacuous; it is kept as `(_s : α)`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "remove_colours_succeeds"]
theorem removeColoursSucceeds {α : Type} :
    ∀ (adj ks : List Nat) (_s : α) (s : State),
      (∀ v ∈ adj, v < s.node_tag.length) →
      ∃ ls, removeColours adj ks s = (.success ls, s)
  | _, [], _, s, _ => by cases ‹List Nat› <;> exact ⟨_, rfl⟩
  | [], _ :: _, _, s, _ => ⟨_, rfl⟩
  | x :: xs, k :: ks, u, s, hb => by
      have hx := hb x List.mem_cons_self
      have hxs : ∀ v ∈ xs, v < s.node_tag.length := fun v hv => hb v (List.mem_cons_of_mem _ hv)
      simp only [removeColours, Translator.Monadic.MonadBase.bind, nodeTagSubEqn, if_pos hx]
      cases holEl x s.node_tag with
      | Fixed c =>
          obtain ⟨r, hr⟩ := removeColoursSucceeds xs ((k :: ks).filter fun y => y ≠ c) u s hxs
          exact ⟨r, by simp only [hr, ret]⟩
      | Atemp =>
          obtain ⟨r, hr⟩ := removeColoursSucceeds xs (k :: ks) u s hxs
          exact ⟨r, by simp only [hr, ret]⟩
      | Stemp =>
          obtain ⟨r, hr⟩ := removeColoursSucceeds xs (k :: ks) u s hxs
          exact ⟨r, by simp only [hr, ret]⟩

/-- Exact HOL `assign_Atemp_tag_correct` (`reg_allocProofScript.sml:402-446`); `s`, `pref`,
`n` and `ks` are free in HOL, with `pref` at its kernel type
`num -> num list -> ra_state -> (num option, state_exn) exc # ra_state`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "assign_Atemp_tag_correct"]
theorem assignAtempTagCorrect (s : State)
    (pref : Nat → List Nat → M State (Option Nat) StateException) (n : Nat) (ks : List Nat) :
    goodRaState s ∧ noClash s.adj_ls s.node_tag ∧ goodPref pref ∧ n < s.dim →
    ∃ s', assignAtempTag ks pref n s = (.success (), s') ∧
      (∀ m, if n = m ∧ holEl n s.node_tag = .Atemp then holEl n s'.node_tag ≠ .Atemp
        else holEl m s'.node_tag = holEl m s.node_tag) ∧
      noClash s'.adj_ls s'.node_tag ∧ goodRaState s' ∧
      s' = { s with node_tag := s'.node_tag } := by
  intro ⟨hg, hnc, hpref, hn⟩
  have hnl : n < s.node_tag.length := by rw [hg.2.1]; exact hn
  have hal : n < s.adj_ls.length := by rw [hg.1]; exact hn
  have hadj : ∀ v ∈ holEl n s.adj_ls, v < s.node_tag.length := fun v hv => by
    rw [hg.2.1]; exact good_adj' hg hn v hv
  have hgset : ∀ t : Tag, goodRaState { s with node_tag := s.node_tag.set n t } := fun t => by
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩ := hg
    exact ⟨g1, (List.length_set ..).trans g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13,
      g14⟩
  have hother : ∀ t : Tag, ∀ m, n ≠ m → holEl m (s.node_tag.set n t) = holEl m s.node_tag :=
    fun t m hnm => by rw [holEl_set _ _ _ _ hnl, if_neg hnm]
  simp only [assignAtempTag, Translator.Monadic.MonadBase.bind, nodeTagSubEqn, if_pos hnl]
  generalize ht : holEl n s.node_tag = t
  have hkeep : t ≠ .Atemp → ∃ s', (ret () : M State Unit StateException) s =
      (.success (), s') ∧
      (∀ m, if n = m ∧ t = .Atemp then holEl n s'.node_tag ≠ .Atemp
        else holEl m s'.node_tag = holEl m s.node_tag) ∧
      noClash s'.adj_ls s'.node_tag ∧ goodRaState s' ∧
      s' = { s with node_tag := s'.node_tag } := fun hne =>
    ⟨s, rfl, fun m => by rw [if_neg (fun h => hne h.2)], hnc, hg, rfl⟩
  cases t with
  | Fixed c => exact hkeep (by simp)
  | Stemp => exact hkeep (by simp)
  | Atemp =>
      simp only [Translator.Monadic.MonadBase.bind, adjLsSubEqn, if_pos hal]
      obtain ⟨ls, hrc⟩ := removeColoursSucceeds (holEl n s.adj_ls) ks () s hadj
      obtain ⟨hsub, hfix⟩ := removeColoursSuccess _ _ s ls s hrc
      simp only [hrc]
      cases ls with
      | nil =>
          refine ⟨_, by simp only [updateNodeTagEqn, if_pos hnl], fun m => ?_,
            noClashLupdateStemp _ _ n hnc, hgset _, rfl⟩
          by_cases hnm : n = m
          · rw [if_pos (by simp [hnm])]
            show holEl n (s.node_tag.set n .Stemp) ≠ .Atemp
            rw [holEl_set _ _ _ _ hnl, if_pos rfl]
            simp
          · rw [if_neg (fun h => hnm h.1)]
            exact hother _ m hnm
      | cons c cs =>
          obtain ⟨res, hres, hmem⟩ := hpref n (c :: cs) s hg
          simp only [Translator.Monadic.MonadBase.bind, hres]
          have key : ∀ col, col ∈ c :: cs → ∃ s', updateNodeTag n (.Fixed col) s =
              (.success (), s') ∧
              (∀ m, if n = m ∧ True then holEl n s'.node_tag ≠ .Atemp
                else holEl m s'.node_tag = holEl m s.node_tag) ∧
              noClash s'.adj_ls s'.node_tag ∧ goodRaState s' ∧
              s' = { s with node_tag := s'.node_tag } := fun col hcol => by
            refine ⟨{ s with node_tag := s.node_tag.set n (.Fixed col) },
              by simp only [updateNodeTagEqn, if_pos hnl], fun m => ?_, ?_, hgset _, rfl⟩
            · by_cases hnm : n = m
              · rw [if_pos (by simp [hnm])]
                show holEl n (s.node_tag.set n (.Fixed col)) ≠ .Atemp
                rw [holEl_set _ _ _ _ hnl, if_pos rfl]
                simp
              · rw [if_neg (fun h => hnm h.1)]
                exact hother _ m hnm
            · refine noClashLupdateFixed _ _ n col ⟨hg.2.2.2.2.2.2.2.2.2.2.2.2.2,
                fun ls hls v hv => ?_, hal, fun m ⟨hm, hml⟩ hfx => ?_, hnc⟩
              · rw [hg.2.1]; exact hg.2.2.2.2.2.2.1 ls hls v hv
              · have := hfix m ⟨hm, hml⟩
                rw [hfx] at this
                exact this hcol
          cases res with
          | none => exact key c List.mem_cons_self
          | some y => exact key y hmem

/-- Exact HOL `assign_Atemps_FOREACH_lem` (`reg_allocProofScript.sml:448-488`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "assign_Atemps_FOREACH_lem"]
theorem assignAtempsForeachLem :
    ∀ (ls : List Nat) (s : State) (ks : List Nat)
      (prefs : Nat → List Nat → M State (Option Nat) StateException),
      goodRaState s ∧ noClash s.adj_ls s.node_tag ∧ goodPref prefs ∧ (∀ v ∈ ls, v < s.dim) →
      ∃ s', stExForeach ls (assignAtempTag ks prefs) s = (.success (), s') ∧
        noClash s'.adj_ls s'.node_tag ∧ goodRaState s' ∧
        s' = { s with node_tag := s'.node_tag } ∧
        ∀ m, if m ∈ ls ∧ holEl m s.node_tag = .Atemp then holEl m s'.node_tag ≠ .Atemp
          else holEl m s'.node_tag = holEl m s.node_tag := by
  intro ls
  induction ls with
  | nil =>
      intro s ks prefs ⟨hg, hnc, _, _⟩
      exact ⟨s, rfl, hnc, hg, rfl, fun m => by rw [if_neg (fun h => by cases h.1)]⟩
  | cons h t ih =>
      intro s ks prefs ⟨hg, hnc, hpref, hb⟩
      obtain ⟨s1, h1, hm1, hnc1, hg1, hs1⟩ :=
        assignAtempTagCorrect s prefs h ks ⟨hg, hnc, hpref, hb h List.mem_cons_self⟩
      obtain ⟨T1, rfl⟩ : ∃ T, s1 = { s with node_tag := T } := ⟨_, hs1⟩
      obtain ⟨s2, h2, hnc2, hg2, hs2, hm2⟩ := ih _ ks prefs
        ⟨hg1, hnc1, hpref, fun v hv => hb v (List.mem_cons_of_mem _ hv)⟩
      obtain ⟨T2, rfl⟩ : ∃ T, s2 = { ({ s with node_tag := T1 } : State) with node_tag := T } :=
        ⟨_, hs2⟩
      refine ⟨_, ?_, hnc2, hg2, rfl, fun m => ?_⟩
      · simp only [stExForeach, ignoreBind, h1]
        exact h2
      have e1 := hm1 m
      have e2 := hm2 m
      change (if h = m ∧ holEl h s.node_tag = .Atemp then holEl h T1 ≠ .Atemp
        else holEl m T1 = holEl m s.node_tag) at e1
      change (if m ∈ t ∧ holEl m T1 = .Atemp then holEl m T2 ≠ .Atemp
        else holEl m T2 = holEl m T1) at e2
      change (if m ∈ h :: t ∧ holEl m s.node_tag = .Atemp then holEl m T2 ≠ .Atemp
        else holEl m T2 = holEl m s.node_tag)
      by_cases hc : m ∈ h :: t ∧ holEl m s.node_tag = .Atemp
      · rw [if_pos hc]
        by_cases hhm : h = m
        · subst hhm
          rw [if_pos ⟨rfl, hc.2⟩] at e1
          rw [if_neg (fun h' => e1 h'.2)] at e2
          rw [e2]; exact e1
        · rw [if_neg (fun h' => hhm h'.1)] at e1
          have hmt : m ∈ t := by
            rcases List.mem_cons.mp hc.1 with h' | h'
            · exact absurd h'.symm hhm
            · exact h'
          rw [if_pos ⟨hmt, e1.trans hc.2⟩] at e2
          exact e2
      · rw [if_neg hc]
        have hn1 : ¬ (h = m ∧ holEl h s.node_tag = .Atemp) := fun ⟨hhm, ha⟩ =>
          hc ⟨hhm ▸ List.mem_cons_self, hhm ▸ ha⟩
        rw [if_neg hn1] at e1
        have hn2 : ¬ (m ∈ t ∧ holEl m T1 = .Atemp) := fun ⟨hmt, ha⟩ =>
          hc ⟨List.mem_cons_of_mem _ hmt, e1 ▸ ha⟩
        rw [if_neg hn2] at e2
        exact e2.trans e1

/-- Exact HOL `assign_Atemps_correct` (`reg_allocProofScript.sml:490-535`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "assign_Atemps_correct"]
theorem assignAtempsCorrect :
    ∀ (k : Nat) (ls : List Nat) (prefs : Nat → List Nat → M State (Option Nat) StateException)
      (s : State),
      goodRaState s ∧ goodPref prefs ∧ noClash s.adj_ls s.node_tag →
      ∃ s', assignAtemps k ls prefs s = (.success (), s') ∧
        noClash s'.adj_ls s'.node_tag ∧ goodRaState s' ∧
        s' = { s with node_tag := s'.node_tag } ∧
        (∀ n ∈ s'.node_tag, n ≠ .Atemp) ∧
        ∀ m, m < s.node_tag.length ∧ holEl m s.node_tag ≠ .Atemp →
          holEl m s'.node_tag = holEl m s.node_tag := by
  intro k ls prefs s ⟨hg, hpref, hnc⟩
  obtain ⟨s1, h1, hnc1, hg1, hs1, hm1⟩ := assignAtempsForeachLem (ls.filter fun n => n < s.dim)
    s (List.range k) prefs
    ⟨hg, hnc, hpref, fun v hv => by simpa using (List.mem_filter.mp hv).2⟩
  obtain ⟨T1, rfl⟩ : ∃ T, s1 = { s with node_tag := T } := ⟨_, hs1⟩
  obtain ⟨s2, h2, hnc2, hg2, hs2, hm2⟩ := assignAtempsForeachLem (List.range s.dim) _
    (List.range k) prefs ⟨hg1, hnc1, hpref, fun v hv => List.mem_range.mp hv⟩
  obtain ⟨T2, rfl⟩ : ∃ T, s2 = { ({ s with node_tag := T1 } : State) with node_tag := T } :=
    ⟨_, hs2⟩
  have hT2 : T2.length = s.dim := hg2.2.1
  refine ⟨_, ?_, hnc2, hg2, rfl, fun e he => ?_, fun m ⟨hml, hma⟩ => ?_⟩
  · simp only [assignAtemps, Translator.Monadic.MonadBase.bind, getDim, ret, ignoreBind, h1]
    exact h2
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hid : i < s.dim := hT2 ▸ hi
    have e2 := hm2 i
    change (if i ∈ List.range s.dim ∧ holEl i T1 = .Atemp then holEl i T2 ≠ .Atemp
      else holEl i T2 = holEl i T1) at e2
    rw [← holEl_eq_getElem _ _ hi]
    by_cases ha : holEl i T1 = .Atemp
    · rw [if_pos ⟨List.mem_range.mpr hid, ha⟩] at e2
      exact e2
    · rw [if_neg (fun h => ha h.2)] at e2
      rw [e2]; exact ha
  · have e1 := hm1 m
    have e2 := hm2 m
    change (if m ∈ ls.filter (fun n => n < s.dim) ∧ holEl m s.node_tag = .Atemp then
      holEl m T1 ≠ .Atemp else holEl m T1 = holEl m s.node_tag) at e1
    change (if m ∈ List.range s.dim ∧ holEl m T1 = .Atemp then holEl m T2 ≠ .Atemp
      else holEl m T2 = holEl m T1) at e2
    rw [if_neg (fun h => hma h.2)] at e1
    rw [if_neg (fun h => hma (e1 ▸ h.2))] at e2
    exact e2.trans e1

/-- Exact HOL `first_match_col_correct` (`reg_allocProofScript.sml:721-733`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "first_match_col_correct"]
theorem firstMatchColCorrect :
    ∀ (x ks : List Nat) (s : State),
      ∃ res, firstMatchCol ks x s = (res, s) ∧
        match res with
        | .failure v => v = .Subscript
        | .success (some k) => k ∈ ks
        | _ => True := by
  intro x
  induction x with
  | nil => intro ks s; exact ⟨.success none, rfl, trivial⟩
  | cons y ys ih =>
      intro ks s
      by_cases hy : y < s.node_tag.length
      · simp only [firstMatchCol, Translator.Monadic.MonadBase.bind, nodeTagSubEqn, if_pos hy]
        cases holEl y s.node_tag with
        | Fixed m =>
            by_cases hm : m ∈ ks
            · exact ⟨.success (some m), by simp only [if_pos hm, ret], hm⟩
            · simp only [if_neg hm]
              exact ih ks s
        | Atemp => exact ih ks s
        | Stemp => exact ih ks s
      · exact ⟨.failure .Subscript, by simp only [firstMatchCol, Translator.Monadic.MonadBase.bind,
          nodeTagSubEqn, if_neg hy], rfl⟩

/-- Exact HOL `coalesce_root_success` (`reg_allocProofScript.sml:735-751`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "coalesce_root_success"]
theorem coalesceRootSuccess :
    ∀ (n : Nat) (s : State), goodRaState s ∧ n < s.dim →
      ∃ v, coalesceRoot n s = (.success v, s) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro s ⟨hg, hn⟩
  have hcl : n < s.coalesced.length := by rw [hg.2.2.2.1]; exact hn
  have hnt : holEl n s.coalesced < s.dim := by
    apply hg.2.2.2.2.2.1
    rw [holEl_eq_getElem _ _ hcl]; exact List.getElem_mem _
  have htl : holEl n s.coalesced < s.node_tag.length := by rw [hg.2.1]; exact hnt
  obtain ⟨bx, hbx⟩ : ∃ b, isFixed (holEl n s.coalesced) s = (.success b, s) := by
    refine ⟨match holEl (holEl n s.coalesced) s.node_tag with | .Fixed _ => true | _ => false, ?_⟩
    simp only [isFixed, Translator.Monadic.MonadBase.bind, nodeTagSubEqn, if_pos htl, ret]
    rfl
  rw [coalesceRoot]
  simp only [Translator.Monadic.MonadBase.bind, coalescedSubEqn, if_pos hcl, hbx]
  by_cases hb : bx = true
  · exact ⟨holEl n s.coalesced, by simp only [if_pos hb, ret]⟩
  · rw [if_neg hb]
    by_cases hle : n ≤ holEl n s.coalesced
    · exact ⟨n, by simp only [dif_pos hle, ret]⟩
    · rw [dif_neg hle]
      exact ih _ (by omega) s ⟨hg, hnt⟩

/-- Exact HOL `good_pref_biased_pref` (`reg_allocProofScript.sml:753-766`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "good_pref_biased_pref"]
theorem goodPrefBiasedPref : ∀ (t : Spt (List Nat)), goodPref (biasedPref t) := by
  intro t n ks s hg
  by_cases hn : n < s.dim
  · obtain ⟨v, hv⟩ := coalesceRootSuccess n s ⟨hg, hn⟩
    have key : ∀ vs, ∃ res, handleSubscript (firstMatchCol ks (v :: vs))
        (ret none : M State (Option Nat) StateException) s = (.success res, s) ∧
        match res with
        | none => True
        | some k => k ∈ ks := fun vs => by
      obtain ⟨res, hres, hp⟩ := firstMatchColCorrect (v :: vs) ks s
      simp only [handleSubscript, hres]
      cases res with
      | success r =>
          refine ⟨r, rfl, ?_⟩
          cases r with
          | none => trivial
          | some k => exact hp
      | failure e =>
          cases hp
          exact ⟨none, rfl, trivial⟩
    simp only [biasedPref, Translator.Monadic.MonadBase.bind, getDim, if_pos hn, hv]
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
  · exact ⟨none, by simp only [biasedPref, Translator.Monadic.MonadBase.bind, getDim, if_neg hn,
      ret], trivial⟩

end Flapjack.RegAlloc
