import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.Proofs
import Flapjack.Compiler.Backend.RegAlloc.Proofs.ClashTreeDomain
import Flapjack.Compiler.Backend.RegAlloc.Proofs.CliqueSuccess
import Flapjack.Compiler.Backend.RegAlloc.Proofs.ColouringTransport

/-!
# reg_allocProof: the interference graph certifies the clash tree

Port of `reg_allocProofScript.sml:1565-1920`, `mk_graph_check_clash_tree`: any colouring
that is satisfactory for the graph built by `mk_graph` passes the `check_clash_tree`
oracle, with the live sets tracking the images of the clash tree's live lists. HOL sets
are predicates (`domain` is `sptDomain`, `set l` list membership, `{x | P x}` the
predicate `P`, `∪` disjunction, `IMAGE f s` the existential `∃ x, s x ∧ f x = y`,
`count n` the bound `· < n`), `INJ f s t` is expanded as HOL `INJ_DEF`, and
`ALL_DISTINCT` is `List.Nodup`.
-/

namespace Flapjack.RegAlloc

open Flapjack Flapjack.Translator.Monadic.MonadBase

/-- A satisfactory colouring is injective on a clique (Flapjack infrastructure, from
`colouring_satisfactory_cliques` and `ALL_DISTINCT_set_INJ`). -/
private theorem colInjClique {col : Nat → Nat} {g : List (List Nat)} {l : List Nat}
    (hnd : l.Nodup) (hb : ∀ x ∈ l, x < g.length) (hc : colouringSatisfactory col g)
    (hcl : isClique l g) : ∀ x y, x ∈ l → y ∈ l → col x = col y → x = y :=
  allDistinctSetInj l col (colouringSatisfactoryCliques l g col ⟨hnd, hb, hc, hcl⟩)

/-- `MAP f` keeps a list distinct when `f` is injective on its members. -/
private theorem nodupMapOn {f : Nat → Nat} :
    ∀ {l : List Nat}, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hf, hd => by
      rw [List.map_cons, List.nodup_cons]
      obtain ⟨ha, hl⟩ := List.nodup_cons.mp hd
      refine ⟨fun hm => ?_, nodupMapOn (fun x hx y hy => hf x (List.mem_cons_of_mem _ hx) y
        (List.mem_cons_of_mem _ hy)) hl⟩
      obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
      exact ha (hf b (List.mem_cons_of_mem _ hb) a List.mem_cons_self hfb ▸ hb)

/-- `check_col` succeeds on a name set its colouring is injective on, returning the set
and the image of its colours (Flapjack infrastructure). -/
private theorem checkColOk (f : Nat → Nat) (t : NumSet)
    (hinj : ∀ x y, sptDomain t x → sptDomain t y → f x = f y → x = y) :
    ∃ ft, checkCol f t = some (t, ft) ∧ sptDomain ft = fun y => ∃ x, sptDomain t x ∧ f x = y := by
  have hmap : (sptToAList t).map (fun entry => f entry.1) =
      ((sptToAList t).map Prod.fst).map f := by rw [List.map_map]; rfl
  have hnd : ((sptToAList t).map fun entry => f entry.1).Nodup := by
    rw [hmap]
    exact nodupMapOn (fun x hx y hy => hinj x y ((sptMemMapFstToAList t x).mp hx)
      ((sptMemMapFstToAList t y).mp hy)) (sptAllDistinctMapFstToAList t)
  refine ⟨_, by
    simp only [checkCol]
    rw [if_pos (show List.Pairwise (fun x1 x2 => x1 ≠ x2) _ from hnd)], ?_⟩
  rw [sptDomainFromAList]
  funext y
  apply propext
  rw [List.map_map]
  simp only [Function.comp_def, List.map_id', hmap]
  constructor
  · intro hy
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hy
    exact ⟨k, (sptMemMapFstToAList t k).mp hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact List.mem_map.mpr ⟨k, (sptMemMapFstToAList t k).mpr hk, rfl⟩

/-- Exact HOL `mk_graph_check_clash_tree` (`reg_allocProofScript.sml:1565-1920`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "mk_graph_check_clash_tree"]
theorem mkGraphCheckClashTree :
    ∀ (ct : ClashTree) (ta : Nat → Nat) (livelist : List Nat) (s : State)
      (livelist' : List Nat) (s' : State) (col : Nat → Nat) (live flive : NumSet),
      mkGraph ta ct livelist s = (.success livelist', s') ∧
        colouringSatisfactory col s'.adj_ls ∧
        ((∀ x, (inClashTree ct x ∨ sptDomain live x) → ta x < s.adj_ls.length) ∧
          (∀ x y, (inClashTree ct x ∨ sptDomain live x) →
            (inClashTree ct y ∨ sptDomain live y) → ta x = ta y → x = y)) ∧
        (fun y => ∃ x, sptDomain live x ∧ ta x = y) = (fun y => y ∈ livelist) ∧
        livelist.Nodup ∧ (∀ y ∈ livelist, y < s.dim) ∧ isClique livelist s.adj_ls ∧
        goodRaState s ∧
        sptDomain flive = (fun y => ∃ x, sptDomain live x ∧ (col ∘ ta) x = y) →
      ∃ livein flivein,
        checkClashTree (col ∘ ta) ct live flive = some (livein, flivein) ∧
        (fun y => ∃ x, sptDomain livein x ∧ ta x = y) = (fun y => y ∈ livelist') ∧
        sptDomain flivein = (fun y => ∃ x, sptDomain livein x ∧ (col ∘ ta) x = y) := by
  intro ct
  induction ct with
  | delta w r =>
      intro ta livelist s livelist' s' col live flive
        ⟨hmk, hcs, ⟨hr, hinj⟩, himg, hnd, hlb, hcl, hg, hfl⟩
      have hdim : s.adj_ls.length = s.dim := hg.1
      have himg' : ∀ y, (∃ x, sptDomain live x ∧ ta x = y) ↔ y ∈ livelist := fun y => by
        have := congrFun himg y; simp only [eq_iff_iff] at this; exact this
      have hwb : ∀ y ∈ w.map ta, y < s.dim := fun y hy => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        rw [← hdim]; exact hr x (Or.inl (Or.inl hx))
      have hrb : ∀ y ∈ r.map ta, y < s.dim := fun y hy => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        rw [← hdim]; exact hr x (Or.inl (Or.inr hx))
      obtain ⟨live1, s1, h1, hg1, hnd1, hs1, hset1, hc1, hsub1⟩ :=
        extendCliqueSucceeds (w.map ta) livelist s ⟨hg, hcl, hwb, hnd, hlb⟩
      obtain ⟨A1, rfl⟩ : ∃ A, s1 = { s with adj_ls := A } := ⟨_, hs1⟩
      have hm1 : ∀ y, y ∈ live1 ↔ y ∈ livelist ++ w.map ta := fun y => by
        have := congrFun hset1 y; simp only [eq_iff_iff] at this; exact this
      have hl1b : ∀ y ∈ live1, y < s.dim := fun y hy => by
        rcases List.mem_append.mp ((hm1 y).mp hy) with h | h
        · exact hlb y h
        · exact hwb y h
      have hl2 : ∀ y, y ∈ live1.filter (fun x => decide (x ∉ w.map ta)) ↔
          y ∈ live1 ∧ y ∉ w.map ta := fun y => by simp [List.mem_filter]
      obtain ⟨livein, s2, h2, hg2, hnd2, hs2, hset2, hc2, hsub2⟩ :=
        extendCliqueSucceeds (r.map ta) (live1.filter (fun x => decide (x ∉ w.map ta)))
          { s with adj_ls := A1 }
          ⟨hg1, isCliqueFilter _ _ live1 hc1, hrb, hnd1.filter _,
            fun y hy => hl1b y ((hl2 y).mp hy).1⟩
      obtain ⟨A2, rfl⟩ : ∃ A, s2 = { ({ s with adj_ls := A1 } : State) with adj_ls := A } :=
        ⟨_, hs2⟩
      have hm2 : ∀ y, y ∈ livein ↔
          y ∈ live1.filter (fun x => decide (x ∉ w.map ta)) ++ r.map ta := fun y => by
        have := congrFun hset2 y; simp only [eq_iff_iff] at this; exact this
      have hrun : mkGraph ta (.delta w r) livelist s =
          (.success livein, { ({ s with adj_ls := A1 } : State) with adj_ls := A2 }) := by
        simp only [mkGraph, Translator.Monadic.MonadBase.bind, ret, h1, h2]
      rw [hrun] at hmk
      simp only [Prod.mk.injEq, Exc.success.injEq] at hmk
      obtain ⟨rfl, rfl⟩ := hmk
      have hA2 : A2.length = s.dim := hg2.1
      have hinj1 : ∀ x y, x ∈ live1 → y ∈ live1 → col x = col y → x = y :=
        colInjClique hnd1 (fun y hy => hA2 ▸ hl1b y hy) hcs (isCliqueSubgraph _ _ _ ⟨hc1, hsub2⟩)
      have hinb : ∀ y ∈ livein, y < s.dim := fun y hy => by
        rcases List.mem_append.mp ((hm2 y).mp hy) with h | h
        · exact hl1b y ((hl2 y).mp h).1
        · exact hrb y h
      have hinj2 : ∀ x y, x ∈ livein → y ∈ livein → col x = col y → x = y :=
        colInjClique hnd2 (fun y hy => hA2 ▸ hinb y hy) hcs hc2
      -- membership of the live images
      have hta1 : ∀ x, (x ∈ w ∨ sptDomain live x) → ta x ∈ live1 := fun x hx => by
        rcases hx with hx | hx
        · exact (hm1 _).mpr (List.mem_append_right _ (List.mem_map_of_mem hx))
        · exact (hm1 _).mpr (List.mem_append_left _ ((himg' _).mp ⟨x, hx, rfl⟩))
      have hdel : ∀ x, sptDomain live x → x ∉ w → ta x ∉ w.map ta := fun x hx hxw hm => by
        obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hm
        exact hxw (hinj z x (Or.inl (Or.inl hz)) (Or.inr hx) hzx ▸ hz)
      have hta2 : ∀ x, (x ∈ r ∨ (sptDomain live x ∧ x ∉ w)) → ta x ∈ livein := fun x hx => by
        rcases hx with hx | ⟨hx, hxw⟩
        · exact (hm2 _).mpr (List.mem_append_right _ (List.mem_map_of_mem hx))
        · exact (hm2 _).mpr (List.mem_append_left _
            ((hl2 _).mpr ⟨hta1 x (Or.inr hx), hdel x hx hxw⟩))
      -- the write check
      have hinjw : ∀ x y, (x ∈ w ∨ sptDomain live x) → (y ∈ w ∨ sptDomain live y) →
          (col ∘ ta) x = (col ∘ ta) y → x = y := fun x y hx hy hf => by
        have e := hinj1 _ _ (hta1 x hx) (hta1 y hy) hf
        refine hinj x y ?_ ?_ e
        · rcases hx with hx | hx
          · exact Or.inl (Or.inl hx)
          · exact Or.inr hx
        · rcases hy with hy | hy
          · exact Or.inl (Or.inl hy)
          · exact Or.inr hy
      obtain ⟨L1, F1, hpc1, -⟩ := checkPartialColSuccess w live flive (col ∘ ta) ⟨hfl, hinjw⟩
      -- the read check
      have hdomdel : ∀ x, sptDomain (numsetListDelete w live) x ↔ sptDomain live x ∧ x ∉ w :=
        fun x => by rw [domainNumsetListDelete]
      have hfl2 : sptDomain (numsetListDelete (w.map (col ∘ ta)) flive) =
          fun y => ∃ x, sptDomain (numsetListDelete w live) x ∧ (col ∘ ta) x = y := by
        rw [domainNumsetListDelete, hfl]
        funext y
        apply propext
        constructor
        · rintro ⟨⟨x, hx, rfl⟩, hn⟩
          exact ⟨x, (hdomdel x).mpr ⟨hx, fun hxw => hn (List.mem_map_of_mem hxw)⟩, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          obtain ⟨hx, hxw⟩ := (hdomdel x).mp hx
          refine ⟨⟨x, hx, rfl⟩, fun hm => ?_⟩
          obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hm
          exact hxw (hinjw z x (Or.inl hz) (Or.inr hx) hzx ▸ hz)
      have hinjr : ∀ x y, (x ∈ r ∨ sptDomain (numsetListDelete w live) x) →
          (y ∈ r ∨ sptDomain (numsetListDelete w live) y) →
          (col ∘ ta) x = (col ∘ ta) y → x = y := fun x y hx hy hf => by
        rw [hdomdel] at hx hy
        have e := hinj2 _ _ (hta2 x hx) (hta2 y hy) hf
        refine hinj x y ?_ ?_ e
        · rcases hx with hx | ⟨hx, -⟩
          · exact Or.inl (Or.inr hx)
          · exact Or.inr hx
        · rcases hy with hy | ⟨hy, -⟩
          · exact Or.inl (Or.inr hy)
          · exact Or.inr hy
      obtain ⟨L2, F2, hpc2, hF2⟩ := checkPartialColSuccess r (numsetListDelete w live)
        (numsetListDelete (w.map (col ∘ ta)) flive) (col ∘ ta) ⟨hfl2, hinjr⟩
      refine ⟨L2, F2, ?_, ?_, hF2⟩
      · simp only [checkClashTree, hpc1, hpc2]
      · have hdom2 := checkPartialColDomain r (col ∘ ta) _ _ (L2, F2) hpc2
        rw [hdom2]
        funext y
        apply propext
        constructor
        · rintro ⟨x, hx, rfl⟩
          rw [hdomdel] at hx
          exact hta2 x hx
        · intro hy
          rcases List.mem_append.mp ((hm2 y).mp hy) with h | h
          · obtain ⟨hy1, hyw⟩ := (hl2 y).mp h
            rcases List.mem_append.mp ((hm1 y).mp hy1) with h | h
            · obtain ⟨x, hx, rfl⟩ := (himg' y).mpr h
              refine ⟨x, Or.inr ((hdomdel x).mpr ⟨hx, fun hxw => hyw ?_⟩), rfl⟩
              exact List.mem_map_of_mem hxw
            · exact absurd h hyw
          · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
            exact ⟨x, Or.inl hx, rfl⟩
  | set t =>
      intro ta livelist s livelist' s' col live flive
        ⟨hmk, hcs, ⟨hr, hinj⟩, _, _, _, _, hg, _⟩
      have hdim : s.adj_ls.length = s.dim := hg.1
      have hkeys : ∀ k, k ∈ (sptToAList t).map Prod.fst ↔ sptDomain t k :=
        sptMemMapFstToAList t
      have hmemn : ∀ y, y ∈ ((sptToAList t).map Prod.fst).map ta ↔
          ∃ k, sptDomain t k ∧ ta k = y := fun y => by
        rw [List.mem_map]
        exact ⟨fun ⟨k, hk, e⟩ => ⟨k, (hkeys k).mp hk, e⟩,
          fun ⟨k, hk, e⟩ => ⟨k, (hkeys k).mpr hk, e⟩⟩
      have hbd : ∀ y ∈ ((sptToAList t).map Prod.fst).map ta, y < s.dim := fun y hy => by
        obtain ⟨k, hk, rfl⟩ := (hmemn y).mp hy
        rw [← hdim]; exact hr k (Or.inl hk)
      obtain ⟨s1, h1, hg1, hs1, hc1, _⟩ := cliqueInsertEdgeSucceeds _ s ⟨hg, hbd⟩
      obtain ⟨A1, rfl⟩ : ∃ A, s1 = { s with adj_ls := A } := ⟨_, hs1⟩
      have hrun : mkGraph ta (.set t) livelist s =
          (.success (((sptToAList t).map Prod.fst).map ta), { s with adj_ls := A1 }) := by
        simp only [mkGraph, Translator.Monadic.MonadBase.bind, ret, ignoreBind, h1]
      rw [hrun] at hmk
      simp only [Prod.mk.injEq, Exc.success.injEq] at hmk
      obtain ⟨rfl, rfl⟩ := hmk
      have hA1 : A1.length = s.dim := hg1.1
      have hnd1 : (((sptToAList t).map Prod.fst).map ta).Nodup :=
        nodupMapOn (fun x hx y hy => hinj x y (Or.inl ((hkeys x).mp hx))
          (Or.inl ((hkeys y).mp hy))) (sptAllDistinctMapFstToAList t)
      have hci := colInjClique hnd1 (fun y hy => hA1 ▸ hbd y hy) hcs hc1
      obtain ⟨ft, hcc, hft⟩ := checkColOk (col ∘ ta) t (fun x y hx hy hf =>
        hinj x y (Or.inl hx) (Or.inl hy)
          (hci _ _ ((hmemn _).mpr ⟨x, hx, rfl⟩) ((hmemn _).mpr ⟨y, hy, rfl⟩) hf))
      refine ⟨t, ft, by simp only [checkClashTree, hcc], ?_, hft⟩
      funext y
      apply propext
      exact (hmemn y).symm
  | branch topt t1 t2 ih1 ih2 =>
      intro ta livelist s livelist' s' col live flive
        ⟨hmk, hcs, ⟨hr, hinj⟩, himg, hnd, hlb, hcl, hg, hfl⟩
      have hdim : s.adj_ls.length = s.dim := hg.1
      have hin1 : ∀ x, inClashTree t1 x → inClashTree (.branch topt t1 t2) x :=
        fun x hx => Or.inl hx
      have hin2 : ∀ x, inClashTree t2 x → inClashTree (.branch topt t1 t2) x :=
        fun x hx => Or.inr (Or.inl hx)
      obtain ⟨l1, s1, h1, hg1, hc1, hs1, hb1, hnd1, hm1, hsub1⟩ := mkGraphSucceeds t1 ta livelist s
        ⟨hg, fun x hx => hdim ▸ hr x (Or.inl (hin1 x hx)),
          ⟨fun x hx => hr x (Or.inl (hin1 x hx)),
            fun x y hx hy => hinj x y (Or.inl (hin1 x hx)) (Or.inl (hin1 y hy))⟩,
          hcl, hnd, hlb⟩
      obtain ⟨A1, rfl⟩ : ∃ A, s1 = { s with adj_ls := A } := ⟨_, hs1⟩
      have hA1 : A1.length = s.dim := hg1.1
      obtain ⟨l2, s2, h2, hg2, hc2, hs2, hb2, hnd2, hm2, hsub2⟩ := mkGraphSucceeds t2 ta livelist
        { s with adj_ls := A1 }
        ⟨hg1, fun x hx => hdim ▸ hr x (Or.inl (hin2 x hx)),
          ⟨fun x hx => by show ta x < A1.length; rw [hA1, ← hdim]; exact hr x (Or.inl (hin2 x hx)),
            fun x y hx hy => hinj x y (Or.inl (hin2 x hx)) (Or.inl (hin2 y hy))⟩,
          isCliqueSubgraph _ _ _ ⟨hcl, hsub1⟩, hnd, hlb⟩
      obtain ⟨A2, rfl⟩ : ∃ A, s2 = { ({ s with adj_ls := A1 } : State) with adj_ls := A } :=
        ⟨_, hs2⟩
      have hA2 : A2.length = s.dim := hg2.1
      have him1 : ∀ y, (∃ x, sptDomain live x ∧ ta x = y) ↔ y ∈ livelist := fun y => by
        have := congrFun himg y; simp only [eq_iff_iff] at this; exact this
      -- the two subtree checks, given the final graph contains `A2`
      have sub : ∀ (A3 : List (List Nat)), isSubgraph A2 A3 → colouringSatisfactory col A3 →
          (∃ lo lc, checkClashTree (col ∘ ta) t1 live flive = some (lo, lc) ∧
            (fun y => ∃ x, sptDomain lo x ∧ ta x = y) = (fun y => y ∈ l1) ∧
            sptDomain lc = (fun y => ∃ x, sptDomain lo x ∧ (col ∘ ta) x = y)) ∧
          (∃ ro rc, checkClashTree (col ∘ ta) t2 live flive = some (ro, rc) ∧
            (fun y => ∃ x, sptDomain ro x ∧ ta x = y) = (fun y => y ∈ l2) ∧
            sptDomain rc = (fun y => ∃ x, sptDomain ro x ∧ (col ∘ ta) x = y)) := by
        intro A3 hsub3 hcs3
        refine ⟨ih1 ta livelist s l1 _ col live flive ⟨h1,
            colouringSatisfactorySubgraph col A3 A1
              ⟨hcs3, isSubgraphTrans _ _ _ ⟨hsub2, hsub3⟩⟩,
            ⟨fun x hx => hr x (hx.imp_left (hin1 x)),
              fun x y hx hy => hinj x y (hx.imp_left (hin1 x)) (hy.imp_left (hin1 y))⟩,
            himg, hnd, hlb, hcl, hg, hfl⟩,
          ih2 ta livelist _ l2 _ col live flive ⟨h2,
            colouringSatisfactorySubgraph col A3 A2 ⟨hcs3, hsub3⟩,
            ⟨fun x hx => by
                show ta x < A1.length
                rw [hA1, ← hdim]; exact hr x (hx.imp_left (hin2 x)),
              fun x y hx hy => hinj x y (hx.imp_left (hin2 x)) (hy.imp_left (hin2 y))⟩,
            himg, hnd, hlb, isCliqueSubgraph _ _ _ ⟨hcl, hsub1⟩, hg1, hfl⟩⟩
      cases topt with
      | none =>
          obtain ⟨livein, s3, h3, hg3, hnd3, hs3, hset3, hc3, hsub3⟩ :=
            extendCliqueSucceeds l1 l2 { ({ s with adj_ls := A1 } : State) with adj_ls := A2 }
              ⟨hg2, hc2, hb1, hnd2, hb2⟩
          obtain ⟨A3, rfl⟩ : ∃ A, s3 = { ({ s with adj_ls := A2 } : State) with adj_ls := A } :=
            ⟨_, hs3⟩
          have hrun : mkGraph ta (.branch none t1 t2) livelist s = (.success livein,
              { ({ s with adj_ls := A2 } : State) with adj_ls := A3 }) := by
            simp only [mkGraph, Translator.Monadic.MonadBase.bind, ret, h1, h2, h3]
          rw [hrun] at hmk
          simp only [Prod.mk.injEq, Exc.success.injEq] at hmk
          obtain ⟨rfl, rfl⟩ := hmk
          obtain ⟨⟨lo, lc, hcc1, himg1, hlc⟩, ⟨ro, rc, hcc2, himg2, _⟩⟩ := sub A3 hsub3 hcs
          have hm3 : ∀ y, y ∈ livein ↔ y ∈ l2 ++ l1 := fun y => by
            have := congrFun hset3 y; simp only [eq_iff_iff] at this; exact this
          have hi1 : ∀ y, (∃ x, sptDomain lo x ∧ ta x = y) ↔ y ∈ l1 := fun y => by
            have := congrFun himg1 y; simp only [eq_iff_iff] at this; exact this
          have hi2 : ∀ y, (∃ x, sptDomain ro x ∧ ta x = y) ↔ y ∈ l2 := fun y => by
            have := congrFun himg2 y; simp only [eq_iff_iff] at this; exact this
          have hA3 : A3.length = s.dim := hg3.1
          have hci := colInjClique hnd3 (fun y hy => by
            rw [hA3]
            rcases List.mem_append.mp ((hm3 y).mp hy) with h | h
            · exact hb2 y h
            · exact hb1 y h) hcs hc3
          have hdiff : ∀ x, x ∈ (sptToAList (sptDifference ro lo)).map Prod.fst ↔
              sptDomain ro x ∧ ¬ sptDomain lo x := fun x => by
            rw [sptMemMapFstToAList, sptDomainDifference]
          have hro := checkClashTreeDomain t2 (col ∘ ta) live flive ro _ hcc2
          have hlo := checkClashTreeDomain t1 (col ∘ ta) live flive lo _ hcc1
          have hct : ∀ x, (x ∈ (sptToAList (sptDifference ro lo)).map Prod.fst ∨ sptDomain lo x) →
              (inClashTree (.branch none t1 t2) x ∨ sptDomain live x) ∧ ta x ∈ livein :=
            fun x hx => by
              rcases hx with hx | hx
              · have hxr := ((hdiff x).mp hx).1
                refine ⟨?_, (hm3 _).mpr (List.mem_append_left _ ((hi2 _).mp ⟨x, hxr, rfl⟩))⟩
                rcases hro x hxr with h | h
                · exact Or.inr h
                · exact Or.inl (hin2 x h)
              · refine ⟨?_, (hm3 _).mpr (List.mem_append_right _ ((hi1 _).mp ⟨x, hx, rfl⟩))⟩
                rcases hlo x hx with h | h
                · exact Or.inr h
                · exact Or.inl (hin1 x h)
          obtain ⟨L, F, hpc, hF⟩ := checkPartialColSuccess
            ((sptToAList (sptDifference ro lo)).map Prod.fst) lo lc (col ∘ ta)
            ⟨hlc, fun x y hx hy hf => hinj x y (hct x hx).1 (hct y hy).1
              (hci _ _ (hct x hx).2 (hct y hy).2 hf)⟩
          refine ⟨L, F, by simp only [checkClashTree, hcc1, hcc2, hpc], ?_, hF⟩
          rw [checkPartialColDomain _ (col ∘ ta) _ _ (L, F) hpc]
          funext y
          apply propext
          constructor
          · rintro ⟨x, hx, rfl⟩
            exact (hct x hx).2
          · intro hy
            rcases List.mem_append.mp ((hm3 y).mp hy) with h | h
            · obtain ⟨x, hx, rfl⟩ := (hi2 y).mpr h
              by_cases hxl : sptDomain lo x
              · exact ⟨x, Or.inr hxl, rfl⟩
              · exact ⟨x, Or.inl ((hdiff x).mpr ⟨hx, hxl⟩), rfl⟩
            · obtain ⟨x, hx, rfl⟩ := (hi1 y).mpr h
              exact ⟨x, Or.inr hx, rfl⟩
      | some tt =>
          have hin3 : ∀ x, sptDomain tt x → inClashTree (.branch (some tt) t1 t2) x :=
            fun x hx => Or.inr (Or.inr hx)
          have hkeys : ∀ k, k ∈ (sptToAList tt).map Prod.fst ↔ sptDomain tt k :=
            sptMemMapFstToAList tt
          have hmemn : ∀ y, y ∈ ((sptToAList tt).map Prod.fst).map ta ↔
              ∃ k, sptDomain tt k ∧ ta k = y := fun y => by
            rw [List.mem_map]
            exact ⟨fun ⟨k, hk, e⟩ => ⟨k, (hkeys k).mp hk, e⟩,
              fun ⟨k, hk, e⟩ => ⟨k, (hkeys k).mpr hk, e⟩⟩
          have hbd : ∀ y ∈ ((sptToAList tt).map Prod.fst).map ta, y < s.dim := fun y hy => by
            obtain ⟨k, hk, rfl⟩ := (hmemn y).mp hy
            rw [← hdim]; exact hr k (Or.inl (hin3 k hk))
          obtain ⟨s3, h3, hg3, hs3, hc3, hsub3⟩ := cliqueInsertEdgeSucceeds _
            { ({ s with adj_ls := A1 } : State) with adj_ls := A2 } ⟨hg2, hbd⟩
          obtain ⟨A3, rfl⟩ : ∃ A, s3 = { ({ s with adj_ls := A2 } : State) with adj_ls := A } :=
            ⟨_, hs3⟩
          have hrun : mkGraph ta (.branch (some tt) t1 t2) livelist s =
              (.success (((sptToAList tt).map Prod.fst).map ta),
                { ({ s with adj_ls := A2 } : State) with adj_ls := A3 }) := by
            simp only [mkGraph, Translator.Monadic.MonadBase.bind, ret, ignoreBind, h1, h2, h3]
          rw [hrun] at hmk
          simp only [Prod.mk.injEq, Exc.success.injEq] at hmk
          obtain ⟨rfl, rfl⟩ := hmk
          obtain ⟨⟨lo, lc, hcc1, -, -⟩, ⟨ro, rc, hcc2, -, -⟩⟩ := sub A3 hsub3 hcs
          have hA3 : A3.length = s.dim := hg3.1
          have hnd3 : (((sptToAList tt).map Prod.fst).map ta).Nodup :=
            nodupMapOn (fun x hx y hy => hinj x y (Or.inl (hin3 x ((hkeys x).mp hx)))
              (Or.inl (hin3 y ((hkeys y).mp hy)))) (sptAllDistinctMapFstToAList tt)
          have hci := colInjClique hnd3 (fun y hy => hA3 ▸ hbd y hy) hcs hc3
          obtain ⟨ft, hcc, hft⟩ := checkColOk (col ∘ ta) tt (fun x y hx hy hf =>
            hinj x y (Or.inl (hin3 x hx)) (Or.inl (hin3 y hy))
              (hci _ _ ((hmemn _).mpr ⟨x, hx, rfl⟩) ((hmemn _).mpr ⟨y, hy, rfl⟩) hf))
          refine ⟨tt, ft, by simp only [checkClashTree, hcc1, hcc2, hcc], ?_, hft⟩
          funext y
          apply propext
          exact (hmemn y).symm
  | seq t1 t2 ih1 ih2 =>
      intro ta livelist s livelist' s' col live flive
        ⟨hmk, hcs, ⟨hr, hinj⟩, himg, hnd, hlb, hcl, hg, hfl⟩
      have hdim : s.adj_ls.length = s.dim := hg.1
      have hin1 : ∀ x, inClashTree t1 x → inClashTree (.seq t1 t2) x := fun x hx => Or.inl hx
      have hin2 : ∀ x, inClashTree t2 x → inClashTree (.seq t1 t2) x := fun x hx => Or.inr hx
      obtain ⟨l2, s1, h1, hg1, hc1, hs1, hb1, hnd1, _, hsub1⟩ := mkGraphSucceeds t2 ta livelist s
        ⟨hg, fun x hx => hdim ▸ hr x (Or.inl (hin2 x hx)),
          ⟨fun x hx => hr x (Or.inl (hin2 x hx)),
            fun x y hx hy => hinj x y (Or.inl (hin2 x hx)) (Or.inl (hin2 y hy))⟩,
          hcl, hnd, hlb⟩
      obtain ⟨A1, rfl⟩ : ∃ A, s1 = { s with adj_ls := A } := ⟨_, hs1⟩
      have hA1 : A1.length = s.dim := hg1.1
      obtain ⟨livein, s2, h2, hg2, hc2, hs2, hb2, hnd2, _, hsub2⟩ := mkGraphSucceeds t1 ta l2
        { s with adj_ls := A1 }
        ⟨hg1, fun x hx => hdim ▸ hr x (Or.inl (hin1 x hx)),
          ⟨fun x hx => by show ta x < A1.length; rw [hA1, ← hdim]; exact hr x (Or.inl (hin1 x hx)),
            fun x y hx hy => hinj x y (Or.inl (hin1 x hx)) (Or.inl (hin1 y hy))⟩,
          hc1, hnd1, hb1⟩
      obtain ⟨A2, rfl⟩ : ∃ A, s2 = { ({ s with adj_ls := A1 } : State) with adj_ls := A } :=
        ⟨_, hs2⟩
      have hrun : mkGraph ta (.seq t1 t2) livelist s =
          (.success livein, { ({ s with adj_ls := A1 } : State) with adj_ls := A2 }) := by
        simp only [mkGraph, Translator.Monadic.MonadBase.bind, h1]
        exact h2
      rw [hrun] at hmk
      simp only [Prod.mk.injEq, Exc.success.injEq] at hmk
      obtain ⟨rfl, rfl⟩ := hmk
      obtain ⟨ro, rc, hcc2, himg2, hrc⟩ := ih2 ta livelist s l2 _ col live flive ⟨h1,
        colouringSatisfactorySubgraph col A2 A1 ⟨hcs, hsub2⟩,
        ⟨fun x hx => hr x (hx.imp_left (hin2 x)),
          fun x y hx hy => hinj x y (hx.imp_left (hin2 x)) (hy.imp_left (hin2 y))⟩,
        himg, hnd, hlb, hcl, hg, hfl⟩
      have hro := checkClashTreeDomain t2 (col ∘ ta) live flive ro _ hcc2
      have hct : ∀ x, (inClashTree t1 x ∨ sptDomain ro x) →
          inClashTree (.seq t1 t2) x ∨ sptDomain live x := fun x hx => by
        rcases hx with hx | hx
        · exact Or.inl (hin1 x hx)
        · rcases hro x hx with h | h
          · exact Or.inr h
          · exact Or.inl (hin2 x h)
      obtain ⟨lin, fl, hcc1, himg1, hfl1⟩ := ih1 ta l2 _ livein _ col ro rc ⟨h2, hcs,
        ⟨fun x hx => by show ta x < A1.length; rw [hA1, ← hdim]; exact hr x (hct x hx),
          fun x y hx hy => hinj x y (hct x hx) (hct y hy)⟩,
        himg2, hnd1, hb1, hc1, hg1, hrc⟩
      exact ⟨lin, fl, by simp only [checkClashTree, hcc2, hcc1], himg1, hfl1⟩

end Flapjack.RegAlloc
