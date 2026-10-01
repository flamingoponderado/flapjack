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

/-- Exact HOL `check_partial_col_success` (`reg_allocProofScript.sml:1253-1294`):
when the coloured set is the image of the live set and the colouring is
injective on the checked names together with the live set, the partial check
succeeds and preserves the image invariant. HOL sets are predicates, `IMAGE`
an existential and `INJ _ _ UNIV` scoped injectivity (the `UNIV` codomain
condition is trivial). No well-formedness premise is added. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "check_partial_col_success"]
theorem checkPartialColSuccess :
    ∀ (ls : List Nat) (live flive : NumSet) (col : Nat → Nat),
      sptDomain flive = (fun y => ∃ x, sptDomain live x ∧ col x = y) ∧
      (∀ x y, (x ∈ ls ∨ sptDomain live x) → (y ∈ ls ∨ sptDomain live y) →
        col x = col y → x = y) →
      ∃ livein flivein,
        checkPartialCol col ls live flive = some (livein, flivein) ∧
        sptDomain flivein = (fun y => ∃ x, sptDomain livein x ∧ col x = y)
  | [], live, flive, col, ⟨hd, _⟩ => ⟨live, flive, rfl, hd⟩
  | h :: ls, live, flive, col, ⟨hd, hi⟩ => by
      have dins (tree : NumSet) (a x : Nat) :
          sptDomain (sptInsert a () tree) x ↔ x = a ∨ sptDomain tree x :=
        sptMem_sptInsert x a () tree
      have hiTail : ∀ x y, (x ∈ ls ∨ sptDomain live x) → (y ∈ ls ∨ sptDomain live y) →
          col x = col y → x = y := by
        intro x y hx hy he
        refine hi x y ?_ ?_ he
        · rcases hx with hx | hx
          · exact Or.inl (List.mem_cons_of_mem h hx)
          · exact Or.inr hx
        · rcases hy with hy | hy
          · exact Or.inl (List.mem_cons_of_mem h hy)
          · exact Or.inr hy
      cases hl : sptLookup h live with
      | some value =>
          cases value
          obtain ⟨livein, flivein, hc, hd'⟩ := checkPartialColSuccess ls live flive col ⟨hd, hiTail⟩
          exact ⟨livein, flivein, by simpa only [checkPartialCol, hl] using hc, hd'⟩
      | none =>
          have hnl : ¬ sptDomain live h := by simp [sptDomain, hl]
          have hf : sptLookup (col h) flive = none := by
            cases hfl : sptLookup (col h) flive with
            | none => rfl
            | some _ =>
                exfalso
                have hm : sptDomain flive (col h) := by simp [sptDomain, hfl]
                rw [hd] at hm
                obtain ⟨x, hx, he⟩ := hm
                have := hi x h (Or.inr hx) (Or.inl List.mem_cons_self) he
                subst this
                exact hnl hx
          have hd2 : sptDomain (sptInsert (col h) () flive) =
              (fun y => ∃ x, sptDomain (sptInsert h () live) x ∧ col x = y) := by
            funext y
            apply propext
            rw [dins, hd]
            constructor
            · rintro (he | ⟨x, hx, he⟩)
              · exact ⟨h, (dins live h h).mpr (Or.inl rfl), he.symm⟩
              · exact ⟨x, (dins live h x).mpr (Or.inr hx), he⟩
            · rintro ⟨x, hx, he⟩
              rcases (dins live h x).mp hx with hx | hx
              · subst x; exact Or.inl he.symm
              · exact Or.inr ⟨x, hx, he⟩
          have hi2 : ∀ x y, (x ∈ ls ∨ sptDomain (sptInsert h () live) x) →
              (y ∈ ls ∨ sptDomain (sptInsert h () live) y) → col x = col y → x = y := by
            have lift : ∀ z, (z ∈ ls ∨ sptDomain (sptInsert h () live) z) →
                (z ∈ h :: ls ∨ sptDomain live z) := by
              intro z hz
              rcases hz with hz | hz
              · exact Or.inl (List.mem_cons_of_mem h hz)
              · rcases (dins live h z).mp hz with hz | hz
                · subst z; exact Or.inl List.mem_cons_self
                · exact Or.inr hz
            intro x y hx hy he
            exact hi x y (lift x hx) (lift y hy) he
          obtain ⟨livein, flivein, hc, hd'⟩ :=
            checkPartialColSuccess ls (sptInsert h () live) (sptInsert (col h) () flive) col
              ⟨hd2, hi2⟩
          exact ⟨livein, flivein, by simpa only [checkPartialCol, hl, hf] using hc, hd'⟩

/-- Exact HOL `check_partial_col_domain` (`reg_allocProofScript.sml:1541-1550`):
a successful partial check returns the live set extended by the checked
names. `set ls ∪ domain live` is the predicate `x ∈ ls ∨ sptDomain live x`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "check_partial_col_domain"]
theorem checkPartialColDomain :
    ∀ (ls : List Nat) (f : Nat → Nat) (live flive : NumSet) (v : NumSet × NumSet),
      checkPartialCol f ls live flive = some v →
      sptDomain v.1 = (fun x => x ∈ ls ∨ sptDomain live x)
  | [], f, live, flive, v, hc => by
      simp only [checkPartialCol, Option.some.injEq] at hc
      subst hc
      funext x; simp
  | h :: ls, f, live, flive, v, hc => by
      have dins (tree : NumSet) (a x : Nat) :
          sptDomain (sptInsert a () tree) x ↔ x = a ∨ sptDomain tree x :=
        sptMem_sptInsert x a () tree
      cases hl : sptLookup h live with
      | some value =>
          cases value
          have hc' : checkPartialCol f ls live flive = some v := by
            simpa only [checkPartialCol, hl] using hc
          rw [checkPartialColDomain ls f live flive v hc']
          have hm : sptDomain live h := by simp [sptDomain, hl]
          funext x
          apply propext
          constructor
          · rintro (hx | hx)
            · exact Or.inl (List.mem_cons_of_mem h hx)
            · exact Or.inr hx
          · rintro (hx | hx)
            · rcases List.mem_cons.mp hx with hx | hx
              · subst x; exact Or.inr hm
              · exact Or.inl hx
            · exact Or.inr hx
      | none =>
          cases hf : sptLookup (f h) flive with
          | some _ => simp [checkPartialCol, hl, hf] at hc
          | none =>
              have hc' : checkPartialCol f ls (sptInsert h () live)
                  (sptInsert (f h) () flive) = some v := by
                simpa only [checkPartialCol, hl, hf] using hc
              rw [checkPartialColDomain ls f _ _ v hc']
              funext x
              apply propext
              rw [dins]
              constructor
              · rintro (hx | hx | hx)
                · exact Or.inl (List.mem_cons_of_mem h hx)
                · subst x; exact Or.inl List.mem_cons_self
                · exact Or.inr hx
              · rintro (hx | hx)
                · rcases List.mem_cons.mp hx with hx | hx
                  · exact Or.inr (Or.inl hx)
                  · exact Or.inl hx
                · exact Or.inr (Or.inr hx)

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

/-- HOL `GT_TRANS` (`reg_allocProofScript.sml:1014-1018`); `a b c` are free
naturals. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "GT_TRANS"]
theorem gtTrans (a b c : Nat) : a > b ∧ b > c → a > c := by omega

/-- HOL `opt_split` (`reg_allocProofScript.sml:3094-3098`) for the `unit option`
lookups of a `num_set`; `a` is free. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "opt_split"]
theorem optSplit (a : Option Unit) : a ≠ none ↔ a = some () := by
  cases a <;> simp

end Flapjack.RegAlloc
