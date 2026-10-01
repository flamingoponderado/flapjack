import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.ClashTree
import Flapjack.Misc.SptreeLookup

/-!
# reg_alloc proofs

Counterpart of `cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml`.
-/

namespace Flapjack.RegAlloc

/-- Exact HOL `domain_numset_list_delete` (`reg_allocProofScript.sml:1354-1362`):
the domain after deleting a list is the original domain minus the list's
members. HOL sets are predicates and `DIFF` a negated conjunct. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "domain_numset_list_delete"]
theorem domainNumsetListDelete {α : Type} :
    ∀ (l : List Nat) (live : Spt α),
      sptDomain (numsetListDelete l live) = fun k => sptDomain live k ∧ k ∉ l
  | [], live => by funext k; simp [numsetListDelete]
  | x :: xs, live => by
      rw [numsetListDelete, domainNumsetListDelete xs (sptDelete x live)]
      funext k
      apply propext
      unfold sptDomain
      rw [sptLookup_sptDelete]
      by_cases h : k = x <;> simp [h]

/-- Exact HOL `in_clash_tree_def` (`reg_allocProofScript.sml:770-780`), clause by
clause; HOL `x ∈ domain names` is the `sptDomain` predicate. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "in_clash_tree_def"]
def inClashTree : ClashTree → Nat → Prop
  | .delta w r, x => x ∈ w ∨ x ∈ r
  | .set names, x => sptDomain names x
  | .branch nameOpt t1 t2, x =>
      inClashTree t1 x ∨ inClashTree t2 x ∨
        (match nameOpt with
          | some names => sptDomain names x
          | none => False)
  | .seq t t', x => inClashTree t x ∨ inClashTree t' x

private theorem lookupUnit_eq_of_isSome (t : NumSet) (k : Nat) :
    (sptLookup k t).isSome = true ↔ sptLookup k t = some () := by
  cases sptLookup k t <;> simp

/-- Exact HOL `INJ_IMG_lookup` (`reg_allocProofScript.sml:3100-3109`). HOL's free
`g gt ft` are universally bound; `INJ g UNIV UNIV` is global injectivity. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "INJ_IMG_lookup"]
theorem injImgLookup (g : Nat → Nat) (gt ft : NumSet) :
    ∀ x, (∀ a b, g a = g b → a = b) ∧
      sptDomain gt = (fun y => ∃ x, sptDomain ft x ∧ g x = y) →
      sptLookup (g x) gt = sptLookup x ft := by
  rintro x ⟨hinj, hd⟩
  have h := congrFun hd (g x)
  unfold sptDomain at h
  cases hf : sptLookup x ft with
  | some u =>
    have : (sptLookup (g x) gt).isSome = true := by
      rw [h]; exact ⟨x, by simp [hf], rfl⟩
    rw [(lookupUnit_eq_of_isSome gt (g x)).mp this]
  | none =>
    cases hg : sptLookup (g x) gt with
    | none => rfl
    | some u =>
      exfalso
      have : (sptLookup (g x) gt).isSome = true := by rw [hg]; rfl
      rw [h] at this
      obtain ⟨y, hy, hyx⟩ := this
      rw [hinj y x hyx] at hy
      simp [hf] at hy

private theorem sptDomain_insertUnit (t : NumSet) (n k : Nat) :
    sptDomain (sptInsert n () t) k ↔ k = n ∨ sptDomain t k := by
  unfold sptDomain
  by_cases h : k = n
  · subst h; simp [sptLookup_sptInsert_same]
  · rw [sptLookup_sptInsert_ne n k () t h]; simp [h]

/-- Exact HOL `check_partial_col_INJ` of `reg_allocProofScript.sml:3111-3125`
(the colour-composition form, distinct from the word_allocProof lemma of the
same name): checking with `g ∘ f` against the `g`-image of the coloured set
gives the same live set and the `g`-image of the coloured result. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "check_partial_col_INJ"]
theorem checkPartialColInjCompose (f g : Nat → Nat) :
    ∀ (ls : List Nat) (t ft gt : NumSet),
      (∀ a b, g a = g b → a = b) ∧ sptDomain gt = (fun y => ∃ x, sptDomain ft x ∧ g x = y) →
      match checkPartialCol f ls t ft with
      | none => checkPartialCol (g ∘ f) ls t gt = none
      | some (tt, ftt) => ∃ gtt, checkPartialCol (g ∘ f) ls t gt = some (tt, gtt) ∧
          sptDomain gtt = (fun y => ∃ x, sptDomain ftt x ∧ g x = y)
  | [], t, ft, gt, ⟨_, hd⟩ => ⟨gt, rfl, hd⟩
  | h :: ls, t, ft, gt, ⟨hinj, hd⟩ => by
      have hl := injImgLookup g gt ft (f h) ⟨hinj, hd⟩
      simp only [checkPartialCol, Function.comp]
      cases ht : sptLookup h t with
      | some u =>
          cases u
          exact checkPartialColInjCompose f g ls t ft gt ⟨hinj, hd⟩
      | none =>
          rw [hl]
          cases hft : sptLookup (f h) ft with
          | some u => cases u; rfl
          | none =>
            dsimp only
            have hd' : sptDomain (sptInsert (g (f h)) () gt) =
                (fun y => ∃ x, sptDomain (sptInsert (f h) () ft) x ∧ g x = y) := by
              funext y
              apply propext
              rw [sptDomain_insertUnit, congrFun hd y]
              constructor
              · rintro (rfl | ⟨x, hx, rfl⟩)
                · exact ⟨f h, (sptDomain_insertUnit _ _ _).mpr (Or.inl rfl), rfl⟩
                · exact ⟨x, (sptDomain_insertUnit _ _ _).mpr (Or.inr hx), rfl⟩
              · rintro ⟨x, hx, rfl⟩
                rcases (sptDomain_insertUnit _ _ _).mp hx with rfl | hx
                · exact Or.inl rfl
                · exact Or.inr ⟨x, hx, rfl⟩
            exact checkPartialColInjCompose f g ls (sptInsert h () t) (sptInsert (f h) () ft)
              (sptInsert (g (f h)) () gt) ⟨hinj, hd'⟩

private theorem alistLookupIsSomeR {α : Type} (k : Nat) :
    ∀ l : List (Nat × α), (sptAListLookup k l).isSome = true ↔ k ∈ l.map Prod.fst
  | [] => by simp [sptAListLookup]
  | (a, v) :: l => by
      by_cases h : k = a
      · subst h; simp [sptAListLookup]
      · simp [sptAListLookup, h, alistLookupIsSomeR k l]

private theorem sptDomain_fromAListUnit (names : List Nat) (k : Nat) :
    sptDomain (sptFromAList (names.map (fun n => (n, ())))) k ↔ k ∈ names := by
  unfold sptDomain
  rw [sptLookup_sptFromAList, alistLookupIsSomeR, List.map_map]
  simp

/-- Exact HOL `check_col_INJ` of `reg_allocProofScript.sml:3127-3150` (the
colour-composition form, distinct from the word_allocProof lemma of the same
name). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "check_col_INJ"]
theorem checkColInjCompose (f g : Nat → Nat) (s : NumSet) (hinj : ∀ a b, g a = g b → a = b) :
    match checkCol f s with
    | none => checkCol (g ∘ f) s = none
    | some (t, ft) => ∃ gt, checkCol (g ∘ f) s = some (t, gt) ∧
        sptDomain gt = (fun y => ∃ x, sptDomain ft x ∧ g x = y) := by
  have hmap : (sptToAList s).map (fun e => (g ∘ f) e.1) =
      ((sptToAList s).map (fun e => f e.1)).map g := by
    rw [List.map_map]; rfl
  have hpw : ((sptToAList s).map (fun e => (g ∘ f) e.1)).Pairwise (· ≠ ·) ↔
      ((sptToAList s).map (fun e => f e.1)).Pairwise (· ≠ ·) := by
    rw [hmap, List.pairwise_map]
    exact List.Pairwise.iff (fun a b => ⟨fun h hab => h (congrArg g hab),
      fun h hab => h (hinj a b hab)⟩)
  unfold checkCol
  dsimp only
  by_cases hp : ((sptToAList s).map (fun e => f e.1)).Pairwise (· ≠ ·)
  · rw [if_pos hp]
    dsimp only
    refine ⟨_, by rw [if_pos (hpw.mpr hp)], ?_⟩
    funext y
    apply propext
    rw [sptDomain_fromAListUnit, hmap]
    simp only [List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, (sptDomain_fromAListUnit _ x).mpr (List.mem_map.mpr hx), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, List.mem_map.mp ((sptDomain_fromAListUnit _ x).mp hx), rfl⟩
  · rw [if_neg hp]
    dsimp only
    rw [if_neg (fun h => hp (hpw.mp h))]

/-- Exact HOL `check_clash_tree_INJ` (`reg_allocProofScript.sml:3152-3205`):
composing the colouring with an injective `g`, and starting from the `g`-image
of the coloured set, the clash-tree check succeeds or fails together and keeps
the live sets, with the `g`-image of the coloured result. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "check_clash_tree_INJ"]
theorem checkClashTreeInj :
    ∀ (ct : ClashTree) (f g : Nat → Nat) (live flive glive : NumSet),
      (∀ a b, g a = g b → a = b) ∧
        sptDomain glive = (fun y => ∃ x, sptDomain flive x ∧ g x = y) →
      match checkClashTree f ct live flive with
      | none => checkClashTree (g ∘ f) ct live glive = none
      | some (liveout, fliveout) => ∃ gliveout,
          checkClashTree (g ∘ f) ct live glive = some (liveout, gliveout) ∧
          sptDomain gliveout = (fun y => ∃ x, sptDomain fliveout x ∧ g x = y) := by
  intro ct
  induction ct with
  | delta w r =>
      rintro f g live flive glive ⟨hinj, hd⟩
      simp only [checkClashTree]
      have h1 := checkPartialColInjCompose f g w live flive glive ⟨hinj, hd⟩
      cases e1 : checkPartialCol f w live flive with
      | none => rw [e1] at h1; dsimp only at h1 ⊢; rw [h1]
      | some p1 =>
        obtain ⟨a, b⟩ := p1
        rw [e1] at h1
        obtain ⟨gb, hgb, -⟩ := h1
        dsimp only
        rw [hgb]
        dsimp only
        have hdD : sptDomain (numsetListDelete (w.map (g ∘ f)) glive) =
            (fun y => ∃ x, sptDomain (numsetListDelete (w.map f) flive) x ∧ g x = y) := by
          rw [domainNumsetListDelete, domainNumsetListDelete, hd]
          funext y
          apply propext
          simp only [List.mem_map, Function.comp]
          constructor
          · rintro ⟨⟨x, hx, rfl⟩, hn⟩
            exact ⟨x, ⟨hx, fun ⟨z, hz, hzx⟩ => hn ⟨z, hz, by rw [hzx]⟩⟩, rfl⟩
          · rintro ⟨x, ⟨hx, hn⟩, rfl⟩
            exact ⟨⟨x, hx, rfl⟩, fun ⟨z, hz, hzx⟩ => hn ⟨z, hz, (hinj _ _ hzx)⟩⟩
        have h2 := checkPartialColInjCompose f g r (numsetListDelete w live)
          (numsetListDelete (w.map f) flive) (numsetListDelete (w.map (g ∘ f)) glive)
          ⟨hinj, hdD⟩
        exact h2
  | set t =>
      rintro f g live flive glive ⟨hinj, -⟩
      simp only [checkClashTree]
      exact checkColInjCompose f g t hinj
  | branch fixed l r ihl ihr =>
      rintro f g live flive glive ⟨hinj, hd⟩
      simp only [checkClashTree]
      have hl := ihl f g live flive glive ⟨hinj, hd⟩
      cases el : checkClashTree f l live flive with
      | none => rw [el] at hl; dsimp only at hl ⊢; rw [hl]
      | some pl =>
      obtain ⟨lo, lc⟩ := pl
      rw [el] at hl
      obtain ⟨glc, hglc, hdlc⟩ := hl
      dsimp only
      rw [hglc]
      dsimp only
      have hr := ihr f g live flive glive ⟨hinj, hd⟩
      cases er : checkClashTree f r live flive with
      | none => rw [er] at hr; dsimp only at hr ⊢; rw [hr]
      | some pr =>
      obtain ⟨ro, rc⟩ := pr
      rw [er] at hr
      obtain ⟨grc, hgrc, -⟩ := hr
      dsimp only
      rw [hgrc]
      dsimp only
      cases fixed with
      | none =>
          exact checkPartialColInjCompose f g _ lo lc glc ⟨hinj, hdlc⟩
      | some tree =>
          exact checkColInjCompose f g tree hinj
  | seq l r ihl ihr =>
      rintro f g live flive glive ⟨hinj, hd⟩
      simp only [checkClashTree]
      have hr := ihr f g live flive glive ⟨hinj, hd⟩
      cases er : checkClashTree f r live flive with
      | none => rw [er] at hr; dsimp only at hr ⊢; rw [hr]
      | some pr =>
      obtain ⟨ro, rc⟩ := pr
      rw [er] at hr
      obtain ⟨grc, hgrc, hdrc⟩ := hr
      dsimp only
      rw [hgrc]
      dsimp only
      exact ihl f g ro rc grc ⟨hinj, hdrc⟩

/-- Exact HOL `check_partial_col_success` (`reg_allocProofScript.sml:1253-1294`):
a colouring injective on `set ls ∪ domain live`, with `flive` the image of
`live`, passes the partial check and keeps the image invariant. HOL
`INJ col S UNIV` is injectivity on `S` (membership in `UNIV` is trivial), and
`IMAGE` is an existential. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "check_partial_col_success"]
theorem checkPartialColSuccess : ∀ (ls : List Nat) (live flive : NumSet) (col : Nat → Nat),
    sptDomain flive = (fun y => ∃ x, sptDomain live x ∧ col x = y) ∧
      (∀ a b, (a ∈ ls ∨ sptDomain live a) → (b ∈ ls ∨ sptDomain live b) → col a = col b →
        a = b) →
    ∃ livein flivein, checkPartialCol col ls live flive = some (livein, flivein) ∧
      sptDomain flivein = (fun y => ∃ x, sptDomain livein x ∧ col x = y)
  | [], live, flive, _, ⟨hd, _⟩ => ⟨live, flive, rfl, hd⟩
  | h :: ls, live, flive, col, ⟨hd, hinj⟩ => by
      simp only [checkPartialCol]
      cases hl : sptLookup h live with
      | some u =>
          cases u
          refine checkPartialColSuccess ls live flive col ⟨hd, fun a b ha hb => hinj a b ?_ ?_⟩
          · rcases ha with ha | ha
            · exact Or.inl (List.mem_cons_of_mem _ ha)
            · exact Or.inr ha
          · rcases hb with hb | hb
            · exact Or.inl (List.mem_cons_of_mem _ hb)
            · exact Or.inr hb
      | none =>
          have hnot : sptLookup (col h) flive = none := by
            cases hc : sptLookup (col h) flive with
            | none => rfl
            | some v =>
                exfalso
                have hdom : sptDomain flive (col h) := by simp [sptDomain, hc]
                rw [hd] at hdom
                obtain ⟨x, hx, hxc⟩ := hdom
                have := hinj x h (Or.inr hx) (Or.inl List.mem_cons_self) hxc
                subst this
                simp [sptDomain, hl] at hx
          rw [hnot]
          refine checkPartialColSuccess ls (sptInsert h () live) (sptInsert (col h) () flive) col
            ⟨?_, fun a b ha hb => hinj a b ?_ ?_⟩
          · funext y
            apply propext
            rw [sptDomain_insertUnit, hd]
            constructor
            · rintro (rfl | ⟨x, hx, rfl⟩)
              · exact ⟨h, (sptDomain_insertUnit _ _ _).mpr (Or.inl rfl), rfl⟩
              · exact ⟨x, (sptDomain_insertUnit _ _ _).mpr (Or.inr hx), rfl⟩
            · rintro ⟨x, hx, rfl⟩
              rcases (sptDomain_insertUnit _ _ _).mp hx with rfl | hx
              · exact Or.inl rfl
              · exact Or.inr ⟨x, hx, rfl⟩
          · rcases ha with ha | ha
            · exact Or.inl (List.mem_cons_of_mem _ ha)
            · rcases (sptDomain_insertUnit _ _ _).mp ha with rfl | ha
              · exact Or.inl List.mem_cons_self
              · exact Or.inr ha
          · rcases hb with hb | hb
            · exact Or.inl (List.mem_cons_of_mem _ hb)
            · rcases (sptDomain_insertUnit _ _ _).mp hb with rfl | hb
              · exact Or.inl List.mem_cons_self
              · exact Or.inr hb

/-- Exact HOL `check_partial_col_domain` (`reg_allocProofScript.sml:1541-1550`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "check_partial_col_domain"]
theorem checkPartialColDomain : ∀ (ls : List Nat) (f : Nat → Nat) (live flive : NumSet)
    (v : NumSet × NumSet), checkPartialCol f ls live flive = some v →
      sptDomain v.1 = fun x => x ∈ ls ∨ sptDomain live x
  | [], _, live, flive, v, h => by
      simp only [checkPartialCol, Option.some.injEq] at h
      subst h
      funext x; simp
  | n :: ls, f, live, flive, v, h => by
      simp only [checkPartialCol] at h
      cases hl : sptLookup n live with
      | some u =>
          rw [hl] at h
          rw [checkPartialColDomain ls f live flive v h]
          funext x
          apply propext
          by_cases hx : x = n
          · subst hx; simp [sptDomain, hl]
          · simp [hx]
      | none =>
          rw [hl] at h
          cases hc : sptLookup (f n) flive with
          | some u => rw [hc] at h; cases h
          | none =>
              rw [hc] at h
              rw [checkPartialColDomain ls f _ _ v h]
              funext x
              apply propext
              rw [sptDomain_insertUnit]
              simp only [List.mem_cons]
              constructor
              · rintro (h1 | h1 | h1)
                · exact Or.inl (Or.inr h1)
                · exact Or.inl (Or.inl h1)
                · exact Or.inr h1
              · rintro ((h1 | h1) | h1)
                · exact Or.inr (Or.inl h1)
                · exact Or.inl h1
                · exact Or.inr (Or.inr h1)

end Flapjack.RegAlloc
