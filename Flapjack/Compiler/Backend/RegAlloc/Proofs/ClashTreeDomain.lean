import Flapjack.Compiler.Backend.RegAlloc.Proofs
import Flapjack.Misc.Sptree.ToAList

/-!
# reg_allocProof clash-tree domain and congruence lemmas

Ports of `reg_allocProofScript.sml` facts about the clash-tree oracle checker
that do not mention adjacency lists: the live-set domain bound
`check_clash_tree_domain`, the colouring-congruence theorems
`check_partial_col_same_dom`/`check_clash_tree_same_dom`, and the small
predicate-set lemmas proved locally beside them. HOL sets are predicates:
`IMAGE f s` is `fun y => ∃ x, s x ∧ f x = y`, `DIFF` a negated conjunct,
`∪` a disjunction, `⊆` a bounded implication and `set l` list membership.
`INJ f s t` is its definition `(∀ x ∈ s, f x ∈ t) ∧ (∀ x y ∈ s, f x = f y →
x = y)`; with codomain `UNIV` the trivially true first conjunct is dropped,
the accepted scoped-injectivity rendering.
-/

namespace Flapjack.RegAlloc

/-- HOL `INJ_less` (`reg_allocProofScript.sml:1244-1251`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "INJ_less"]
theorem injLessRegAlloc {α β : Type} :
    ∀ (f : α → β) (s' : α → Prop) (t : β → Prop) (s : α → Prop),
      ((∀ x, s' x → t (f x)) ∧ (∀ x y, s' x → s' y → f x = f y → x = y)) ∧
        (∀ x, s x → s' x) →
      (∀ x, s x → t (f x)) ∧ (∀ x y, s x → s y → f x = f y → x = y) := by
  intro f s' t s ⟨⟨hmap, hinj⟩, hsub⟩
  exact ⟨fun x hx => hmap x (hsub x hx), fun x y hx hy => hinj x y (hsub x hx) (hsub y hy)⟩

/-- HOL `INJ_COMPOSE_IMAGE` (`reg_allocProofScript.sml:1296-1305`); `f` and
`g` are free in the HOL statement. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "INJ_COMPOSE_IMAGE"]
theorem injComposeImage {α β γ : Type} (f : α → β) (g : β → γ) :
    ∀ (a : α → Prop) (b : β → Prop) (u : γ → Prop),
      ((∀ x, a x → b (f x)) ∧ (∀ x y, a x → a y → f x = f y → x = y)) ∧
        ((∀ y, (∃ x, a x ∧ f x = y) → u (g y)) ∧
          (∀ y z, (∃ x, a x ∧ f x = y) → (∃ x, a x ∧ f x = z) → g y = g z → y = z)) →
      (∀ x, a x → u ((g ∘ f) x)) ∧
        (∀ x y, a x → a y → (g ∘ f) x = (g ∘ f) y → x = y) := by
  intro a b u ⟨⟨_, hf⟩, ⟨hgm, hg⟩⟩
  refine ⟨fun x hx => hgm (f x) ⟨x, hx, rfl⟩, fun x y hx hy he => ?_⟩
  exact hf x y hx hy (hg (f x) (f y) ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ he)

/-- HOL `domain_eq_IMAGE` (`reg_allocProofScript.sml:1327-1332`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "domain_eq_IMAGE"]
theorem domainEqImage {α : Type} (s : Spt α) :
    sptDomain s = fun y => ∃ p, p ∈ sptToAList s ∧ p.1 = y := by
  funext y
  apply propext
  rw [← sptMemMapFstToAList s y]
  simp [List.mem_map]

/-- HOL `ALL_DISTINCT_set_INJ` (`reg_allocProofScript.sml:1493-1501`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "ALL_DISTINCT_set_INJ"]
theorem allDistinctSetInj {α β : Type} :
    ∀ (ls : List α) (col : α → β), (ls.map col).Nodup →
      ∀ x y, x ∈ ls → y ∈ ls → col x = col y → x = y := by
  intro ls col hnd
  induction ls with
  | nil => intro x y hx; simp at hx
  | cons h t ih =>
      intro x y hx hy he
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
      obtain ⟨hh, hnd⟩ := hnd
      simp only [List.mem_cons] at hx hy
      rcases hx with hxh | hxt
      · rcases hy with hyh | hyt
        · exact hxh.trans hyh.symm
        · subst hxh
          exact absurd ⟨y, hyt, he.symm⟩ hh
      · rcases hy with hyh | hyt
        · subst hyh
          exact absurd ⟨x, hxt, he⟩ hh
        · exact ih hnd x y hxt hyt he

/-- HOL `IMAGE_DIFF` (`reg_allocProofScript.sml:1503-1510`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "IMAGE_DIFF"]
theorem imageDiffRegAlloc {α β : Type} (f : α → β) (s t : α → Prop) :
    (∀ x y, (s x ∨ t x) → (s y ∨ t y) → f x = f y → x = y) →
    (fun y => ∃ x, (s x ∧ ¬ t x) ∧ f x = y) =
      (fun y => (∃ x, s x ∧ f x = y) ∧ ¬ (∃ x, t x ∧ f x = y)) := by
  intro h
  funext y
  apply propext
  constructor
  · rintro ⟨x, ⟨hx, hnt⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro ⟨z, hz, hzx⟩
    exact hnt (h x z (Or.inl hx) (Or.inr hz) hzx.symm ▸ hz)
  · rintro ⟨⟨x, hx, rfl⟩, hnt⟩
    exact ⟨x, ⟨hx, fun ht => hnt ⟨x, ht, rfl⟩⟩, rfl⟩

/-- HOL `set_FILTER` (`reg_allocProofScript.sml:1512-1518`); `P` and `live`
are free. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "set_FILTER"]
theorem setFilter {α : Type} (P : α → Bool) (live : List α) :
    (fun x => x ∈ live.filter P) = fun x => x ∈ live ∧ ¬ ¬ (P x = true) := by
  funext x
  simp [List.mem_filter]

/-- HOL `MEM_MAP_IMAGE` (`reg_allocProofScript.sml:1520-1524`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "MEM_MAP_IMAGE"]
theorem memMapImage {α β : Type} (f : α → β) (l : List α) :
    (fun x => x ∈ l.map f) = fun y => ∃ x, x ∈ l ∧ f x = y := by
  funext y
  simp [List.mem_map]

/-- HOL `domain_difference` (`reg_allocProofScript.sml:1526-1532`), the local
restatement of the sptree theorem. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "domain_difference"]
theorem domainDifferenceRegAlloc {α β : Type} (s : Spt α) (t : Spt β) :
    sptDomain (sptDifference s t) = fun x => sptDomain s x ∧ ¬ sptDomain t x :=
  sptDomainDifference s t

/-- HOL `UNION_DIFF_3` (`reg_allocProofScript.sml:1534-1539`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "UNION_DIFF_3"]
theorem unionDiff3 {α : Type} (s t : α → Prop) :
    (fun x => (s x ∧ ¬ t x) ∨ t x) = fun x => s x ∨ t x := by
  funext x
  apply propext
  by_cases h : t x <;> simp [h]

/-- HOL `TWOxDIV2` (`reg_allocProofScript.sml:2031-2035`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "TWOxDIV2"]
theorem twoMulDivTwo (x : Nat) : 2 * x / 2 = x := by omega

/-- Flapjack helper: `check_col` only reads its colouring on the map's keys. -/
private theorem checkCol_congr {α : Type} (f g : Nat → Nat) (t : Spt α)
    (h : ∀ x, sptDomain t x → f x = g x) : checkCol f t = checkCol g t := by
  have hm : (sptToAList t).map (fun entry => f entry.1) =
      (sptToAList t).map (fun entry => g entry.1) := by
    apply List.map_congr_left
    intro p hp
    exact h p.1 ((sptMemMapFstToAList t p.1).mp (List.mem_map_of_mem hp))
  simp only [checkCol, hm]

/-- HOL `check_partial_col_same_dom` (`reg_allocProofScript.sml:3043-3050`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "check_partial_col_same_dom"]
theorem checkPartialColSameDom :
    ∀ (ls : List Nat) (f g : Nat → Nat) (t ft : NumSet),
      (∀ x, x ∈ ls → f x = g x) → checkPartialCol f ls t ft = checkPartialCol g ls t ft := by
  intro ls
  induction ls with
  | nil => intro f g t ft _; rfl
  | cons h tl ih =>
      intro f g t ft hfg
      have hh : f h = g h := hfg h (by simp)
      have htl : ∀ x, x ∈ tl → f x = g x := fun x hx => hfg x (by simp [hx])
      simp only [checkPartialCol, hh]
      split
      · exact ih f g t ft htl
      · split
        · exact ih f g _ _ htl
        · rfl

/-- HOL `check_clash_tree_domain` (`reg_allocProofScript.sml:1552-1563`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "check_clash_tree_domain"]
theorem checkClashTreeDomain :
    ∀ (ct : ClashTree) (f : Nat → Nat) (live flive live' flive' : NumSet),
      checkClashTree f ct live flive = some (live', flive') →
      ∀ x, sptDomain live' x → sptDomain live x ∨ inClashTree ct x := by
  intro ct
  induction ct with
  | delta w r =>
      intro f live flive live' flive' hc x hx
      simp only [checkClashTree] at hc
      split at hc
      · cases hc
      · have hd := checkPartialColDomain _ _ _ _ _ hc
        simp only at hd
        rw [hd, domainNumsetListDelete] at hx
        rcases hx with hx | ⟨hx, _⟩
        · exact Or.inr (Or.inr hx)
        · exact Or.inl hx
  | set t =>
      intro f live flive live' flive' hc x hx
      simp only [checkClashTree, checkCol] at hc
      split at hc
      · cases hc
        exact Or.inr hx
      · cases hc
  | branch fixed left right ihl ihr =>
      intro f live flive live' flive' hc x hx
      simp only [checkClashTree] at hc
      split at hc
      · cases hc
      · rename_i leftOut leftColoured hl
        split at hc
        · cases hc
        · rename_i rightOut rc hr
          cases fixed with
          | none =>
              have hd := checkPartialColDomain _ _ _ _ _ hc
              simp only at hd
              rw [hd] at hx
              rcases hx with hx | hx
              · rw [sptMemMapFstToAList, sptDomainDifference] at hx
                rcases ihr f live flive rightOut rc hr x hx.1 with h | h
                · exact Or.inl h
                · exact Or.inr (Or.inr (Or.inl h))
              · rcases ihl f live flive leftOut leftColoured hl x hx with h | h
                · exact Or.inl h
                · exact Or.inr (Or.inl h)
          | some tree =>
              simp only [checkCol] at hc
              split at hc
              · cases hc
                exact Or.inr (Or.inr (Or.inr hx))
              · cases hc
  | seq left right ihl ihr =>
      intro f live flive live' flive' hc x hx
      simp only [checkClashTree] at hc
      split at hc
      · cases hc
      · rename_i rightOut rightColoured hr
        rcases ihl f rightOut rightColoured live' flive' hc x hx with h | h
        · rcases ihr f live flive rightOut rightColoured hr x h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (Or.inr h')
        · exact Or.inr (Or.inl h)

/-- HOL `check_clash_tree_same_dom` (`reg_allocProofScript.sml:3052-3092`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "check_clash_tree_same_dom"]
theorem checkClashTreeSameDom :
    ∀ (ct : ClashTree) (f g : Nat → Nat) (live flive : NumSet),
      (∀ x, inClashTree ct x ∨ sptDomain live x → f x = g x) →
      checkClashTree f ct live flive = checkClashTree g ct live flive := by
  intro ct
  induction ct with
  | delta w r =>
      intro f g live flive hfg
      have hw : ∀ x, x ∈ w → f x = g x := fun x hx => hfg x (Or.inl (Or.inl hx))
      have hr : ∀ x, x ∈ r → f x = g x := fun x hx => hfg x (Or.inl (Or.inr hx))
      have hmap : w.map f = w.map g := List.map_congr_left hw
      simp only [checkClashTree, checkPartialColSameDom w f g live flive hw, hmap,
        checkPartialColSameDom r f g _ _ hr]
  | set t =>
      intro f g live flive hfg
      exact checkCol_congr f g t (fun x hx => hfg x (Or.inl hx))
  | branch fixed left right ihl ihr =>
      intro f g live flive hfg
      have hl := ihl f g live flive (fun x hx => hfg x (hx.elim (fun h => Or.inl (Or.inl h)) Or.inr))
      have hr := ihr f g live flive (fun x hx => hfg x (hx.elim (fun h => Or.inl (Or.inr (Or.inl h))) Or.inr))
      simp only [checkClashTree, hl, hr]
      split
      · rfl
      · rename_i leftOut leftColoured hlo
        split
        · rfl
        · rename_i rightOut rc hro
          cases fixed with
          | none =>
              apply checkPartialColSameDom
              intro x hx
              rw [sptMemMapFstToAList, sptDomainDifference] at hx
              apply hfg
              rcases checkClashTreeDomain right g live flive rightOut rc hro x hx.1 with h | h
              · exact Or.inr h
              · exact Or.inl (Or.inr (Or.inl h))
          | some tree =>
              exact checkCol_congr f g tree (fun x hx => hfg x (Or.inl (Or.inr (Or.inr hx))))
  | seq left right ihl ihr =>
      intro f g live flive hfg
      have hr := ihr f g live flive (fun x hx => hfg x (hx.elim (fun h => Or.inl (Or.inr h)) Or.inr))
      simp only [checkClashTree, hr]
      split
      · rfl
      · rename_i rightOut rightColoured hro
        apply ihl
        intro x hx
        rcases hx with hx | hx
        · exact hfg x (Or.inl (Or.inl hx))
        · rcases checkClashTreeDomain right g live flive rightOut rightColoured hro x hx with h | h
          · exact hfg x (Or.inr h)
          · exact hfg x (Or.inl (Or.inr h))

end Flapjack.RegAlloc
