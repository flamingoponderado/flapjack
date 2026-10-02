import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.Proofs.EdgeInsertion
import Flapjack.Compiler.Backend.RegAlloc.Proofs
import Flapjack.Misc.Sptree.ToAList
import Flapjack.Compiler.Backend.RegAlloc

/-!
# reg_allocProof: clique insertion and graph construction success

Ports of `reg_allocProofScript.sml:1168-2028`: on a `good_ra_state` inserting a clique,
extending a clique, building the interference graph of a clash tree and adding the forced
edges succeed, keep every component except the adjacency lists, make the live sets cliques
and only add edges; tagging the nodes keeps every component except the node tags and
follows the register-number conventions.
Renderings as in `EdgeInsertion`; HOL `ALL_DISTINCT` is `List.Nodup`, HOL sets are
predicates (`set l` list membership, `{x | P x}` the predicate `P`, `count n` the bound
`· < n`, `IMAGE f s` the existential `∃ x, s x ∧ f x = y`, `∪` disjunction and `SUBSET`
pointwise implication), a set equality `set l = set l'` is the equality of the membership
predicates, and `INJ f s t` is expanded as HOL `INJ_DEF`.
-/

namespace Flapjack.RegAlloc

open Flapjack Flapjack.Translator.Monadic.MonadBase

/-- Exact HOL `clique_insert_edge_succeeds` (`reg_allocProofScript.sml:1168-1194`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "clique_insert_edge_succeeds"]
theorem cliqueInsertEdgeSucceeds :
    ∀ (ls : List Nat) (s : State),
      goodRaState s ∧ (∀ y ∈ ls, y < s.dim) →
      ∃ s', cliqueInsertEdge ls s = (.success (), s') ∧ goodRaState s' ∧
        s' = { s with adj_ls := s'.adj_ls } ∧ isClique ls s'.adj_ls ∧
        isSubgraph s.adj_ls s'.adj_ls := by
  intro ls
  induction ls with
  | nil =>
      intro s ⟨hg, _⟩
      exact ⟨s, rfl, hg, rfl, (fun _ _ ⟨h, _⟩ => by cases h), isSubgraphRefl _⟩
  | cons x xs ih =>
      intro s ⟨hg, hb⟩
      have hx := hb x List.mem_cons_self
      have hxs : ∀ y ∈ xs, y < s.dim := fun y hy => hb y (List.mem_cons_of_mem _ hy)
      obtain ⟨s1, h1, hg1, hs1, he1⟩ := listInsertEdgeSucceeds xs x s ⟨hg, hx, hxs⟩
      obtain ⟨A1, rfl⟩ : ∃ A, s1 = { s with adj_ls := A } := ⟨_, hs1⟩
      obtain ⟨s2, h2, hg2, hs2, hc2, hsub2⟩ := ih _ ⟨hg1, hxs⟩
      obtain ⟨A2, rfl⟩ : ∃ A, s2 = { ({ s with adj_ls := A1 } : State) with adj_ls := A } :=
        ⟨_, hs2⟩
      refine ⟨_, ?_, hg2, rfl, ?_, fun a b h => hsub2 a b ((he1 a b).2 (Or.inr (Or.inr h)))⟩
      · simp only [cliqueInsertEdge, ignoreBind, h1]
        exact h2
      · intro a b ⟨ha, hb', hab⟩
        rcases List.mem_cons.mp ha with rfl | ha1 <;> rcases List.mem_cons.mp hb' with rfl | hb1
        · exact absurd rfl hab
        · exact hsub2 _ _ ((he1 _ _).2 (Or.inl ⟨rfl, hb1⟩))
        · exact hsub2 _ _ ((he1 _ _).2 (Or.inr (Or.inl ⟨rfl, ha1⟩)))
        · exact hc2 a b ⟨ha1, hb1, hab⟩

/-- Exact HOL `extend_clique_succeeds` (`reg_allocProofScript.sml:1196-1231`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "extend_clique_succeeds"]
theorem extendCliqueSucceeds :
    ∀ (ls cli : List Nat) (s : State),
      goodRaState s ∧ isClique cli s.adj_ls ∧ (∀ y ∈ ls, y < s.dim) ∧ cli.Nodup ∧
        (∀ y ∈ cli, y < s.dim) →
      ∃ cli' s', extendClique ls cli s = (.success cli', s') ∧ goodRaState s' ∧ cli'.Nodup ∧
        s' = { s with adj_ls := s'.adj_ls } ∧
        (fun x => x ∈ cli') = (fun x => x ∈ cli ++ ls) ∧ isClique cli' s'.adj_ls ∧
        isSubgraph s.adj_ls s'.adj_ls := by
  intro ls
  induction ls with
  | nil =>
      intro cli s ⟨hg, hc, _, hd, _⟩
      exact ⟨cli, s, rfl, hg, hd, rfl, by simp, hc, isSubgraphRefl _⟩
  | cons x xs ih =>
      intro cli s ⟨hg, hc, hb, hd, hcb⟩
      have hx := hb x List.mem_cons_self
      have hxs : ∀ y ∈ xs, y < s.dim := fun y hy => hb y (List.mem_cons_of_mem _ hy)
      by_cases hm : x ∈ cli
      · obtain ⟨cli', s', hr, hg', hd', hs', hset, hc', hsub⟩ := ih cli s ⟨hg, hc, hxs, hd, hcb⟩
        refine ⟨cli', s', by simp only [extendClique, if_pos hm]; exact hr, hg', hd', hs', ?_,
          hc', hsub⟩
        rw [hset]
        funext y
        simp only [List.mem_append, List.mem_cons, eq_iff_iff]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | rfl | h)
          · exact Or.inl h
          · exact Or.inl hm
          · exact Or.inr h
      · obtain ⟨s1, h1, hg1, hs1, he1⟩ := listInsertEdgeSucceeds cli x s ⟨hg, hx, hcb⟩
        obtain ⟨A1, rfl⟩ : ∃ A, s1 = { s with adj_ls := A } := ⟨_, hs1⟩
        have hc1 : isClique (x :: cli) A1 := by
          intro a b ⟨ha, hb', hab⟩
          rcases List.mem_cons.mp ha with rfl | ha1 <;>
            rcases List.mem_cons.mp hb' with rfl | hb1
          · exact absurd rfl hab
          · exact (he1 _ _).2 (Or.inl ⟨rfl, hb1⟩)
          · exact (he1 _ _).2 (Or.inr (Or.inl ⟨rfl, ha1⟩))
          · exact (he1 a b).2 (Or.inr (Or.inr (hc a b ⟨ha1, hb1, hab⟩)))
        obtain ⟨cli', s', hr, hg', hd', hs', hset, hc', hsub⟩ := ih (x :: cli) _
          ⟨hg1, hc1, hxs, List.nodup_cons.mpr ⟨hm, hd⟩, fun y hy => by
            rcases List.mem_cons.mp hy with rfl | hy
            · exact hx
            · exact hcb y hy⟩
        obtain ⟨A2, rfl⟩ : ∃ A, s' = { ({ s with adj_ls := A1 } : State) with adj_ls := A } :=
          ⟨_, hs'⟩
        refine ⟨cli', _, ?_, hg', hd', rfl, ?_, hc',
          fun a b h => hsub a b ((he1 a b).2 (Or.inr (Or.inr h)))⟩
        · simp only [extendClique, if_neg hm, ignoreBind, h1]
          exact hr
        · rw [hset]
          funext y
          simp only [List.mem_append, List.mem_cons, eq_iff_iff]
          constructor
          · rintro ((rfl | h) | h)
            · exact Or.inr (Or.inl rfl)
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
          · rintro (h | rfl | h)
            · exact Or.inl (Or.inr h)
            · exact Or.inl (Or.inl rfl)
            · exact Or.inr h

/-- Exact HOL `is_clique_FILTER` (`reg_allocProofScript.sml:1334-1344`); `G` and `P` are free
in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "is_clique_FILTER"]
theorem isCliqueFilter (G : List (List Nat)) (P : Nat → Bool) :
    ∀ (ls : List Nat), isClique ls G → isClique (ls.filter P) G :=
  fun _ h x y ⟨hx, hy, hxy⟩ => h x y ⟨(List.mem_filter.mp hx).1, (List.mem_filter.mp hy).1, hxy⟩

/-- Exact HOL `is_clique_subgraph` (`reg_allocProofScript.sml:1346-1352`); `ls`, `s` and
`s'` are free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "is_clique_subgraph"]
theorem isCliqueSubgraph (ls : List Nat) (s s' : List (List Nat)) :
    isClique ls s ∧ isSubgraph s s' → isClique ls s' :=
  fun ⟨hc, hs⟩ x y h => hs x y (hc x y h)

/-- `MAP f` keeps a list distinct when `f` is injective on its members. -/
private theorem nodup_map_on {f : Nat → Nat} :
    ∀ {l : List Nat}, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hf, hd => by
      rw [List.map_cons, List.nodup_cons]
      obtain ⟨ha, hl⟩ := List.nodup_cons.mp hd
      refine ⟨fun hm => ?_, nodup_map_on (fun x hx y hy => hf x (List.mem_cons_of_mem _ hx) y
        (List.mem_cons_of_mem _ hy)) hl⟩
      obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
      exact ha (hf b (List.mem_cons_of_mem _ hb) a List.mem_cons_self hfb ▸ hb)

/-- The coloured names of a `set`/`branch` clash node form a distinct, in-range clique. -/
private theorem names_clique (ta : Nat → Nat) (t : NumSet) (s : State) (hg : goodRaState s)
    (hb : ∀ k, sptDomain t k → ta k < s.dim)
    (hinj : ∀ x y, sptDomain t x → sptDomain t y → ta x = ta y → x = y) :
    ∃ s', cliqueInsertEdge (((sptToAList t).map Prod.fst).map ta) s = (.success (), s') ∧
      goodRaState s' ∧ s' = { s with adj_ls := s'.adj_ls } ∧
      isClique (((sptToAList t).map Prod.fst).map ta) s'.adj_ls ∧
      isSubgraph s.adj_ls s'.adj_ls ∧
      (∀ y ∈ ((sptToAList t).map Prod.fst).map ta, y < s.dim) ∧
      (((sptToAList t).map Prod.fst).map ta).Nodup ∧
      (∀ y ∈ ((sptToAList t).map Prod.fst).map ta, ∃ k, sptDomain t k ∧ ta k = y) := by
  have hmem : ∀ y ∈ ((sptToAList t).map Prod.fst).map ta, ∃ k, sptDomain t k ∧ ta k = y :=
    fun y hy => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hy
      exact ⟨k, (sptMemMapFstToAList t k).mp hk, rfl⟩
  have hbd : ∀ y ∈ ((sptToAList t).map Prod.fst).map ta, y < s.dim := fun y hy => by
    obtain ⟨k, hk, rfl⟩ := hmem y hy
    exact hb k hk
  obtain ⟨s', h, hg', hs', hc, hsub⟩ := cliqueInsertEdgeSucceeds _ s ⟨hg, hbd⟩
  exact ⟨s', h, hg', hs', hc, hsub, hbd,
    nodup_map_on (fun x hx y hy => hinj x y ((sptMemMapFstToAList t x).mp hx)
      ((sptMemMapFstToAList t y).mp hy)) (sptAllDistinctMapFstToAList t), hmem⟩

/-- Exact HOL `mk_graph_succeeds` (`reg_allocProofScript.sml:1365-1481`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "mk_graph_succeeds"]
theorem mkGraphSucceeds :
    ∀ (ct : ClashTree) (ta : Nat → Nat) (liveout : List Nat) (s : State),
      goodRaState s ∧ (∀ x, inClashTree ct x → ta x < s.dim) ∧
        ((∀ x, inClashTree ct x → ta x < s.adj_ls.length) ∧
          (∀ x y, inClashTree ct x → inClashTree ct y → ta x = ta y → x = y)) ∧
        isClique liveout s.adj_ls ∧ liveout.Nodup ∧ (∀ y ∈ liveout, y < s.dim) →
      ∃ livein s', mkGraph ta ct liveout s = (.success livein, s') ∧ goodRaState s' ∧
        isClique livein s'.adj_ls ∧ s' = { s with adj_ls := s'.adj_ls } ∧
        (∀ y ∈ livein, y < s.dim) ∧ livein.Nodup ∧
        (∀ x, x ∈ livein → x ∈ liveout ∨ ∃ y, inClashTree ct y ∧ ta y = x) ∧
        isSubgraph s.adj_ls s'.adj_ls := by
  intro ct
  induction ct with
  | delta w r =>
      intro ta liveout s ⟨hg, hb, _, hcl, hnd, hlb⟩
      have hwb : ∀ y ∈ w.map ta, y < s.dim := fun y hy => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        exact hb x (Or.inl hx)
      have hrb : ∀ y ∈ r.map ta, y < s.dim := fun y hy => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        exact hb x (Or.inr hx)
      obtain ⟨live1, s1, h1, hg1, hnd1, hs1, hset1, hc1, hsub1⟩ :=
        extendCliqueSucceeds (w.map ta) liveout s ⟨hg, hcl, hwb, hnd, hlb⟩
      obtain ⟨A1, rfl⟩ : ∃ A, s1 = { s with adj_ls := A } := ⟨_, hs1⟩
      have hm1 : ∀ x, x ∈ live1 ↔ x ∈ liveout ++ w.map ta := fun x => by
        have := congrFun hset1 x
        simp only [eq_iff_iff] at this
        exact this
      have hl1b : ∀ y ∈ live1, y < s.dim := fun y hy => by
        rcases List.mem_append.mp ((hm1 y).mp hy) with h | h
        · exact hlb y h
        · exact hwb y h
      let live2 := live1.filter (fun x => decide (x ∉ w.map ta))
      have hl2 : ∀ y ∈ live2, y ∈ live1 := fun y hy => (List.mem_filter.mp hy).1
      obtain ⟨livein, s2, h2, hg2, hnd2, hs2, hset2, hc2, hsub2⟩ :=
        extendCliqueSucceeds (r.map ta) live2 { s with adj_ls := A1 }
          ⟨hg1, isCliqueFilter _ _ live1 hc1, hrb, hnd1.filter _, fun y hy => hl1b y (hl2 y hy)⟩
      obtain ⟨A2, rfl⟩ : ∃ A, s2 = { ({ s with adj_ls := A1 } : State) with adj_ls := A } :=
        ⟨_, hs2⟩
      have hm2 : ∀ x, x ∈ livein ↔ x ∈ live2 ++ r.map ta := fun x => by
        have := congrFun hset2 x
        simp only [eq_iff_iff] at this
        exact this
      refine ⟨livein, _, ?_, hg2, hc2, rfl, ?_, hnd2, ?_,
        fun a b h => hsub2 a b (hsub1 a b h)⟩
      · have h2' := h2
        simp only [live2] at h2'
        simp only [mkGraph, Translator.Monadic.MonadBase.bind, ret, h1, h2']
      · intro y hy
        rcases List.mem_append.mp ((hm2 y).mp hy) with h | h
        · exact hl1b y (hl2 y h)
        · exact hrb y h
      · intro x hx
        rcases List.mem_append.mp ((hm2 x).mp hx) with h | h
        · rcases List.mem_append.mp ((hm1 x).mp (hl2 x h)) with h | h
          · exact Or.inl h
          · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
            exact Or.inr ⟨y, Or.inl hy, rfl⟩
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
          exact Or.inr ⟨y, Or.inr hy, rfl⟩
  | set t =>
      intro ta liveout s ⟨hg, hb, ⟨_, hinj⟩, _, _, _⟩
      obtain ⟨s', h, hg', hs', hc, hsub, hbd, hnd, hmem⟩ := names_clique ta t s hg
        (fun k hk => hb k hk) (fun x y hx hy => hinj x y hx hy)
      refine ⟨_, s', ?_, hg', hc, hs', hbd, hnd, fun x hx => Or.inr (hmem x hx), hsub⟩
      simp only [mkGraph, Translator.Monadic.MonadBase.bind, ret, ignoreBind, h]
  | branch topt t1 t2 ih1 ih2 =>
      intro ta liveout s ⟨hg, hb, ⟨hr, hinj⟩, hcl, hnd, hlb⟩
      obtain ⟨l1, s1, h1, hg1, hc1, hs1, hb1, hnd1, hm1, hsub1⟩ := ih1 ta liveout s
        ⟨hg, fun x hx => hb x (Or.inl hx), ⟨fun x hx => hr x (Or.inl hx),
          fun x y hx hy => hinj x y (Or.inl hx) (Or.inl hy)⟩, hcl, hnd, hlb⟩
      obtain ⟨A1, rfl⟩ : ∃ A, s1 = { s with adj_ls := A } := ⟨_, hs1⟩
      have hA1 : A1.length = s.dim := hg1.1
      obtain ⟨l2, s2, h2, hg2, hc2, hs2, hb2, hnd2, hm2, hsub2⟩ := ih2 ta liveout
        { s with adj_ls := A1 }
        ⟨hg1, fun x hx => hb x (Or.inr (Or.inl hx)),
          ⟨fun x hx => by show ta x < A1.length; rw [hA1]; exact hb x (Or.inr (Or.inl hx)),
            fun x y hx hy => hinj x y (Or.inr (Or.inl hx)) (Or.inr (Or.inl hy))⟩,
          isCliqueSubgraph _ _ _ ⟨hcl, hsub1⟩, hnd, hlb⟩
      obtain ⟨A2, rfl⟩ : ∃ A, s2 = { ({ s with adj_ls := A1 } : State) with adj_ls := A } :=
        ⟨_, hs2⟩
      have hsub12 : isSubgraph s.adj_ls A2 := fun a b h => hsub2 a b (hsub1 a b h)
      cases topt with
      | none =>
          obtain ⟨livein, s3, h3, hg3, hnd3, hs3, hset3, hc3, hsub3⟩ :=
            extendCliqueSucceeds l1 l2 { s with adj_ls := A2 } ⟨hg2, hc2, hb1, hnd2, hb2⟩
          obtain ⟨A3, rfl⟩ : ∃ A, s3 = { ({ s with adj_ls := A2 } : State) with adj_ls := A } :=
            ⟨_, hs3⟩
          have hm3 : ∀ x, x ∈ livein ↔ x ∈ l2 ++ l1 := fun x => by
            have := congrFun hset3 x
            simp only [eq_iff_iff] at this
            exact this
          refine ⟨livein, _, ?_, hg3, hc3, rfl, ?_, hnd3, ?_,
            fun a b h => hsub3 a b (hsub12 a b h)⟩
          · simp only [mkGraph, Translator.Monadic.MonadBase.bind, ret, h1, h2, h3]
          · intro y hy
            rcases List.mem_append.mp ((hm3 y).mp hy) with h | h
            · exact hb2 y h
            · exact hb1 y h
          · intro x hx
            rcases List.mem_append.mp ((hm3 x).mp hx) with h | h
            · rcases hm2 x h with h | ⟨y, hy, rfl⟩
              · exact Or.inl h
              · exact Or.inr ⟨y, Or.inr (Or.inl hy), rfl⟩
            · rcases hm1 x h with h | ⟨y, hy, rfl⟩
              · exact Or.inl h
              · exact Or.inr ⟨y, Or.inl hy, rfl⟩
      | some t =>
          obtain ⟨s3, h3, hg3, hs3, hc3, hsub3, hbd, hnd3, hmem⟩ := names_clique ta t
            { s with adj_ls := A2 } hg2
            (fun k hk => hb k (Or.inr (Or.inr hk)))
            (fun x y hx hy => hinj x y (Or.inr (Or.inr hx)) (Or.inr (Or.inr hy)))
          obtain ⟨A3, rfl⟩ : ∃ A, s3 = { ({ s with adj_ls := A2 } : State) with adj_ls := A } :=
            ⟨_, hs3⟩
          refine ⟨_, _, ?_, hg3, hc3, rfl, hbd, hnd3, fun x hx => ?_,
            fun a b h => hsub3 a b (hsub12 a b h)⟩
          · simp only [mkGraph, Translator.Monadic.MonadBase.bind, ret, h1, h2, ignoreBind, h3]
          · obtain ⟨y, hy, rfl⟩ := hmem x hx
            exact Or.inr ⟨y, Or.inr (Or.inr hy), rfl⟩
  | seq t1 t2 ih1 ih2 =>
      intro ta liveout s ⟨hg, hb, ⟨hr, hinj⟩, hcl, hnd, hlb⟩
      obtain ⟨l2, s1, h1, hg1, hc1, hs1, hb1, hnd1, hm1, hsub1⟩ := ih2 ta liveout s
        ⟨hg, fun x hx => hb x (Or.inr hx), ⟨fun x hx => hr x (Or.inr hx),
          fun x y hx hy => hinj x y (Or.inr hx) (Or.inr hy)⟩, hcl, hnd, hlb⟩
      obtain ⟨A1, rfl⟩ : ∃ A, s1 = { s with adj_ls := A } := ⟨_, hs1⟩
      have hA1 : A1.length = s.dim := hg1.1
      obtain ⟨livein, s2, h2, hg2, hc2, hs2, hb2, hnd2, hm2, hsub2⟩ := ih1 ta l2
        { s with adj_ls := A1 }
        ⟨hg1, fun x hx => hb x (Or.inl hx),
          ⟨fun x hx => by show ta x < A1.length; rw [hA1]; exact hb x (Or.inl hx),
            fun x y hx hy => hinj x y (Or.inl hx) (Or.inl hy)⟩, hc1, hnd1, hb1⟩
      obtain ⟨A2, rfl⟩ : ∃ A, s2 = { ({ s with adj_ls := A1 } : State) with adj_ls := A } :=
        ⟨_, hs2⟩
      refine ⟨livein, _, ?_, hg2, hc2, rfl, hb2, hnd2, fun x hx => ?_,
        fun a b h => hsub2 a b (hsub1 a b h)⟩
      · simp only [mkGraph, Translator.Monadic.MonadBase.bind, h1]
        exact h2
      · rcases hm2 x hx with h | ⟨y, hy, rfl⟩
        · rcases hm1 x h with h | ⟨y, hy, rfl⟩
          · exact Or.inl h
          · exact Or.inr ⟨y, Or.inr hy, rfl⟩
        · exact Or.inr ⟨y, Or.inl hy, rfl⟩

/-- Exact HOL `extend_graph_succeeds` (`reg_allocProofScript.sml:1924-1949`); the forced
edges are a `(num, num) alist`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "extend_graph_succeeds"]
theorem extendGraphSucceeds :
    ∀ (forced : List (Nat × Nat)) (f : Nat → Nat) (s : State),
      goodRaState s ∧ (∀ m ∈ forced, f m.1 < s.dim ∧ f m.2 < s.dim) →
      ∃ s', extendGraph f forced s = (.success (), s') ∧ goodRaState s' ∧
        s' = { s with adj_ls := s'.adj_ls } ∧
        ∀ a b, (hasEdge s'.adj_ls a b ↔
          (∃ x y, f x = a ∧ f y = b ∧ (y, x) ∈ forced) ∨
          (∃ x y, f x = a ∧ f y = b ∧ (x, y) ∈ forced) ∨ hasEdge s.adj_ls a b) := by
  intro forced
  induction forced with
  | nil =>
      intro f s ⟨hg, _⟩
      refine ⟨s, rfl, hg, rfl, fun a b => ?_⟩
      constructor
      · exact fun h => Or.inr (Or.inr h)
      · rintro (⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | h)
        · cases h
        · cases h
        · exact h
  | cons m ms ih =>
      intro f s ⟨hg, hb⟩
      obtain ⟨p, q⟩ := m
      obtain ⟨hp, hq⟩ := hb (p, q) List.mem_cons_self
      obtain ⟨s1, h1, hg1, hs1, he1⟩ := insertEdgeSucceeds s (f p) (f q) ⟨hg, hq, hp⟩
      obtain ⟨A1, rfl⟩ : ∃ A, s1 = { s with adj_ls := A } := ⟨_, hs1⟩
      obtain ⟨s2, h2, hg2, hs2, he2⟩ := ih f _ ⟨hg1, fun m hm => hb m (List.mem_cons_of_mem _ hm)⟩
      obtain ⟨A2, rfl⟩ : ∃ A, s2 = { ({ s with adj_ls := A1 } : State) with adj_ls := A } :=
        ⟨_, hs2⟩
      refine ⟨_, ?_, hg2, rfl, fun a b => ?_⟩
      · simp only [extendGraph, ignoreBind, h1]
        exact h2
      rw [he2 a b, he1 a b]
      constructor
      · rintro (⟨x, y, rfl, rfl, h⟩ | ⟨x, y, rfl, rfl, h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h)
        · exact Or.inl ⟨x, y, rfl, rfl, List.mem_cons_of_mem _ h⟩
        · exact Or.inr (Or.inl ⟨x, y, rfl, rfl, List.mem_cons_of_mem _ h⟩)
        · exact Or.inr (Or.inl ⟨p, q, rfl, rfl, List.mem_cons_self⟩)
        · exact Or.inl ⟨q, p, rfl, rfl, List.mem_cons_self⟩
        · exact Or.inr (Or.inr h)
      · rintro (⟨x, y, rfl, rfl, h⟩ | ⟨x, y, rfl, rfl, h⟩ | h)
        · rcases List.mem_cons.mp h with h | h
          · simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
          · exact Or.inl ⟨x, y, rfl, rfl, h⟩
        · rcases List.mem_cons.mp h with h | h
          · simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
          · exact Or.inr (Or.inl ⟨x, y, rfl, rfl, h⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- Exact HOL `mk_tags_st_ex_FOREACH_lem` (`reg_allocProofScript.sml:1953-2007`); `fs` is
free in HOL, and the traversal body is HOL's lambda with the `let`s of `mk_tags` inlined, as
in the source statement. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "mk_tags_st_ex_FOREACH_lem"]
theorem mkTagsStExForeachLem (fs : NumSet) :
    ∀ (ls : List Nat) (s : State) (fa : Nat → Nat),
      goodRaState s ∧ (∀ v ∈ ls, v < s.dim) →
      ∃ s', stExForeach ls (fun i =>
          if fa i % 4 = 1 then
            (match sptLookup (fa i) fs with
              | none => updateNodeTag i .Atemp
              | some () => updateNodeTag i .Stemp)
          else if fa i % 4 = 3 then updateNodeTag i .Stemp
          else updateNodeTag i (.Fixed (fa i / 2))) s = (.success (), s') ∧
        goodRaState s' ∧ s' = { s with node_tag := s'.node_tag } ∧
        ∀ x, x < s.dim →
          if x ∈ ls then
            (if isPhyVar (fa x) then holEl x s'.node_tag = .Fixed (fa x / 2)
             else if isStackVar (fa x) then holEl x s'.node_tag = .Stemp
             else holEl x s'.node_tag = .Atemp ∨ holEl x s'.node_tag = .Stemp)
          else holEl x s'.node_tag = holEl x s.node_tag := by
  intro ls
  induction ls with
  | nil =>
      intro s fa ⟨hg, _⟩
      exact ⟨s, rfl, hg, rfl, fun x _ => by simp⟩
  | cons h t ih =>
      intro s fa ⟨hg, hb⟩
      have hh := hb h List.mem_cons_self
      have hl : h < s.node_tag.length := by rw [hg.2.1]; exact hh
      obtain ⟨tg, hrun, htg⟩ : ∃ tg,
          (if fa h % 4 = 1 then
            (match sptLookup (fa h) fs with
              | none => updateNodeTag h .Atemp
              | some () => updateNodeTag h .Stemp)
          else if fa h % 4 = 3 then updateNodeTag h .Stemp
          else updateNodeTag h (.Fixed (fa h / 2))) s =
            (.success (), { s with node_tag := s.node_tag.set h tg }) ∧
          (if isPhyVar (fa h) then tg = .Fixed (fa h / 2)
           else if isStackVar (fa h) then tg = .Stemp
           else tg = .Atemp ∨ tg = .Stemp) := by
        by_cases h1 : fa h % 4 = 1
        · have hp : isPhyVar (fa h) = false := by
            simp only [isPhyVar, decide_eq_false_iff_not]; omega
          have hs : isStackVar (fa h) = false := by
            simp only [isStackVar, decide_eq_false_iff_not]; omega
          cases hlk : sptLookup (fa h) fs with
          | none =>
              exact ⟨.Atemp, by simp only [if_pos h1, updateNodeTagEqn, if_pos hl],
                by simp only [hp, hs, Bool.false_eq_true, ↓reduceIte, true_or]⟩
          | some u =>
              cases u
              exact ⟨.Stemp, by simp only [if_pos h1, updateNodeTagEqn, if_pos hl],
                by simp only [hp, hs, Bool.false_eq_true, ↓reduceIte, or_true]⟩
        · by_cases h3 : fa h % 4 = 3
          · have hp : isPhyVar (fa h) = false := by
              simp only [isPhyVar, decide_eq_false_iff_not]; omega
            have hs : isStackVar (fa h) = true := by
              simp only [isStackVar, decide_eq_true_eq]; omega
            exact ⟨.Stemp, by simp only [if_neg h1, if_pos h3, updateNodeTagEqn, if_pos hl],
              by simp only [hp, hs, Bool.false_eq_true, ↓reduceIte]⟩
          · have hp : isPhyVar (fa h) = true := by
              simp only [isPhyVar, decide_eq_true_eq]; omega
            exact ⟨.Fixed (fa h / 2), by simp only [if_neg h1, if_neg h3, updateNodeTagEqn,
              if_pos hl], by simp only [hp, ↓reduceIte]⟩
      have hg1 : goodRaState { s with node_tag := s.node_tag.set h tg } := by
        obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩ := hg
        exact ⟨g1, (List.length_set ..).trans g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13,
          g14⟩
      obtain ⟨s2, h2, hg2, hs2, hx2⟩ := ih _ fa ⟨hg1, fun v hv => hb v (List.mem_cons_of_mem _ hv)⟩
      obtain ⟨T2, rfl⟩ : ∃ T, s2 = { ({ s with node_tag := s.node_tag.set h tg } : State) with
                                     node_tag := T } := ⟨_, hs2⟩
      refine ⟨_, ?_, hg2, rfl, fun x hx => ?_⟩
      · simp only [stExForeach, ignoreBind, hrun]
        exact h2
      have hx2 := hx2 x hx
      by_cases ht : x ∈ t
      · rw [if_pos ht] at hx2
        rw [if_pos (List.mem_cons_of_mem _ ht)]
        exact hx2
      · rw [if_neg ht] at hx2
        change holEl x T2 = holEl x (s.node_tag.set h tg) at hx2
        rw [holEl_set _ _ _ _ hl] at hx2
        by_cases hxh : x = h
        · subst hxh
          rw [if_pos List.mem_cons_self, hx2, if_pos rfl]
          exact htg
        · rw [if_neg (fun hm => by
            rcases List.mem_cons.mp hm with hm | hm
            · exact hxh hm
            · exact ht hm), hx2, if_neg (Ne.symm hxh)]

/-- Exact HOL `mk_tags_succeeds` (`reg_allocProofScript.sml:2009-2028`); `s`, `n`, `fs` and
`fa` are free in HOL, and `GENLIST (λx. x) n` is `List.range n` in the tagged `mkTags`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "mk_tags_succeeds"]
theorem mkTagsSucceeds (s : State) (n : Nat) (fs : NumSet) (fa : Nat → Nat) :
    goodRaState s ∧ n = s.dim →
    ∃ s', mkTags n fs fa s = (.success (), s') ∧ goodRaState s' ∧
      s' = { s with node_tag := s'.node_tag } ∧
      ∀ x y, x < n ∧ y = fa x →
        if isPhyVar y then holEl x s'.node_tag = .Fixed (y / 2)
        else if isStackVar y then holEl x s'.node_tag = .Stemp
        else holEl x s'.node_tag = .Atemp ∨ holEl x s'.node_tag = .Stemp := by
  intro ⟨hg, hn⟩
  subst hn
  obtain ⟨s', h, hg', hs', hx⟩ := mkTagsStExForeachLem fs (List.range s.dim) s fa
    ⟨hg, fun v hv => List.mem_range.mp hv⟩
  refine ⟨s', ?_, hg', hs', fun x y ⟨hx', hy⟩ => ?_⟩
  · simp only [mkTags, Translator.Monadic.MonadBase.bind, ret]
    exact h
  · subst hy
    have := hx x hx'
    rw [if_pos (List.mem_range.mpr hx')] at this
    exact this

end Flapjack.RegAlloc
