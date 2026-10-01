import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan
import Flapjack.Compiler.Backend.RegAlloc.Proofs
import Flapjack.Misc.Sptree.ToAList
import Flapjack.Misc.Sptree.InsertUnchanged

/-!
# linear_scanProof: live-tree checker correctness

Ports of `linear_scanProofScript.sml:23-598`: list insertion and deletion
lemmas, the partial-colouring checker invariants, and the correspondence
between `check_live_tree` on `get_live_tree ct` and `check_clash_tree` on `ct`.

HOL sets are predicates: `domain` is `sptDomain`, `set l` list membership,
`UNION` disjunction, `DIFF` a negated conjunct, `SUBSET` pointwise
implication, `EMPTY` the false predicate and `IMAGE f s` the existential
`fun y => ∃ x, s x ∧ f x = y`. `INJ f s UNIV` is scoped injectivity
`∀ x y, s x → s y → f x = f y → x = y`; its `UNIV` codomain conjunct is
trivial and omitted, as in the accepted word_allocProof INJ ports. HOL free
variables of a statement are universally quantified first. No
well-formedness premise is added anywhere.
-/

namespace Flapjack.LinearScan

open Flapjack.RegAlloc

/-- Exact HOL `set_MAP_FST_toAList_eq_domain` (`linear_scanProofScript.sml:23-27`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "set_MAP_FST_toAList_eq_domain"]
theorem setMapFstToAListEqDomain {α : Type} :
    ∀ (s : Spt α), (fun x => x ∈ (sptToAList s).map Prod.fst) = sptDomain s := by
  intro s
  funext x
  exact propext (sptMemMapFstToAList s x)

/-- Exact HOL `numset_list_insert_FOLDL` (`linear_scanProofScript.sml:29-33`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "numset_list_insert_FOLDL"]
theorem numsetListInsertFoldl :
    ∀ (l : List Nat) (live : NumSet),
      numsetListInsert l live = l.foldl (fun live x => sptInsert x () live) live
  | [], _ => rfl
  | x :: xs, live => by
      rw [numsetListInsert, List.foldl_cons]
      exact numsetListInsertFoldl xs _

/-- Exact HOL `numset_list_insert_nottailrec_FOLDR` (`linear_scanProofScript.sml:35-39`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "numset_list_insert_nottailrec_FOLDR"]
theorem numsetListInsertNottailrecFoldr :
    ∀ (l : List Nat) (live : NumSet),
      numsetListInsertNottailrec l live = l.foldr (fun x live => sptInsert x () live) live
  | [], _ => rfl
  | x :: xs, live => by
      rw [numsetListInsertNottailrec, List.foldr_cons, numsetListInsertNottailrecFoldr xs]

/-- Exact HOL `both_numset_list_insert_equal` (`linear_scanProofScript.sml:41-46`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "both_numset_list_insert_equal"]
theorem bothNumsetListInsertEqual :
    ∀ (l : List Nat) (live : NumSet),
      numsetListInsert l live = numsetListInsertNottailrec l.reverse live := by
  intro l live
  rw [numsetListInsertFoldl, numsetListInsertNottailrecFoldr, List.foldr_reverse]

/-- Exact HOL `domain_numset_list_insert` (`linear_scanProofScript.sml:48-54`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "domain_numset_list_insert"]
theorem domainNumsetListInsert :
    ∀ (l : List Nat) (s : NumSet),
      sptDomain (numsetListInsert l s) = fun x => x ∈ l ∨ sptDomain s x
  | [], s => by funext x; simp [numsetListInsert]
  | h :: l, s => by
      rw [numsetListInsert, domainNumsetListInsert l, sptDomainInsert]
      funext x
      apply propext
      simp only [List.mem_cons]
      rw [or_assoc]
      exact or_left_comm

/-- Exact HOL `lookup_insert_id` (`linear_scanProofScript.sml:57-80`): no
well-formedness premise. HOL's unit binder `y` is vacuous and retained. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "lookup_insert_id"]
theorem lookupInsertId :
    ∀ (x : Nat) (_y : Unit) (s : NumSet), sptLookup x s = some () → s = sptInsert x () s := by
  intro x _ s h
  exact (sptInsertUnchanged s x () h).symm

private theorem lookupInsertUnit (t : NumSet) (h x : Nat)
    (hx : sptLookup x t = some ()) : sptLookup x (sptInsert h () t) = some () := by
  by_cases hxh : x = h
  · subst hxh; exact sptLookup_sptInsert_same x () t
  · rw [sptLookup_sptInsert_ne h x () t hxh]; exact hx

/-- Exact HOL `numset_list_insert_FILTER` (`linear_scanProofScript.sml:82-98`).
The HOL filter predicate `λx. lookup x live = NONE` is decided. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "numset_list_insert_FILTER"]
theorem numsetListInsertFilter :
    ∀ (l : List Nat) (live : NumSet),
      numsetListInsert (l.filter (fun x => decide (sptLookup x live = none))) live =
        numsetListInsert l live := by
  intro l live
  have key : ∀ (l : List Nat) (t : NumSet),
      (∀ x, sptLookup x live = some () → sptLookup x t = some ()) →
      numsetListInsert (l.filter (fun x => decide (sptLookup x live = none))) t =
        numsetListInsert l t := by
    intro l
    induction l with
    | nil => intro t _; rfl
    | cons h l ih =>
        intro t ht
        cases hl : sptLookup h live with
        | none =>
            rw [List.filter_cons_of_pos (by simp [hl]), numsetListInsert, numsetListInsert]
            exact ih _ (fun x hx => lookupInsertUnit t h x (ht x hx))
        | some u =>
            cases u
            rw [List.filter_cons_of_neg (by simp [hl]), numsetListInsert,
              sptInsertUnchanged t h () (ht h hl)]
            exact ih t ht
  exact key l live (fun _ hx => hx)

/-- Exact linear_scanProof `domain_numset_list_delete`
(`linear_scanProofScript.sml:100-105`), the same statement as the reviewed
reg_allocProof theorem of that name. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "domain_numset_list_delete"]
theorem domainNumsetListDeleteLinearScan {α : Type} :
    ∀ (l : List Nat) (s : Spt α),
      sptDomain (numsetListDelete l s) = fun x => sptDomain s x ∧ x ∉ l :=
  RegAlloc.domainNumsetListDelete

/-- Successful partial checks keep the colouring injective on the output
live set (the induction behind `check_partial_col_success_INJ_lemma`). -/
private theorem checkPartialColInjOut (f : Nat → Nat) :
    ∀ (l : List Nat) (live flive live' flive' : NumSet),
      sptDomain flive = (fun y => ∃ x, sptDomain live x ∧ f x = y) →
      (∀ x y, sptDomain live x → sptDomain live y → f x = f y → x = y) →
      checkPartialCol f l live flive = some (live', flive') →
      ∀ x y, sptDomain live' x → sptDomain live' y → f x = f y → x = y
  | [], live, flive, live', flive', _, hi, hc => by
      simp only [checkPartialCol, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact hi
  | h :: l, live, flive, live', flive', hd, hi, hc => by
      cases hl : sptLookup h live with
      | some u =>
          cases u
          exact checkPartialColInjOut f l live flive live' flive' hd hi
            (by simpa only [checkPartialCol, hl] using hc)
      | none =>
          cases hf : sptLookup (f h) flive with
          | some _ => simp [checkPartialCol, hl, hf] at hc
          | none =>
              have hn : ¬ sptDomain flive (f h) := by simp [sptDomain, hf]
              have hcol (x : Nat) (hx : sptDomain live x) : f x ≠ f h := by
                intro he; apply hn; rw [hd]; exact ⟨x, hx, he⟩
              have hd2 : sptDomain (sptInsert (f h) () flive) =
                  (fun y => ∃ x, sptDomain (sptInsert h () live) x ∧ f x = y) := by
                rw [sptDomainInsert, sptDomainInsert, hd]
                funext y
                apply propext
                constructor
                · rintro (he | ⟨x, hx, he⟩)
                  · exact ⟨h, Or.inl rfl, he.symm⟩
                  · exact ⟨x, Or.inr hx, he⟩
                · rintro ⟨x, hx | hx, he⟩
                  · subst x; exact Or.inl he.symm
                  · exact Or.inr ⟨x, hx, he⟩
              have hi2 : ∀ x y, sptDomain (sptInsert h () live) x →
                  sptDomain (sptInsert h () live) y → f x = f y → x = y := by
                rw [sptDomainInsert]
                rintro x y (hx | hx) (hy | hy) he
                · rw [hx, hy]
                · subst hx; exact False.elim (hcol y hy he.symm)
                · subst hy; exact False.elim (hcol x hx he)
                · exact hi x y hx hy he
              exact checkPartialColInjOut f l _ _ live' flive' hd2 hi2
                (by simpa only [checkPartialCol, hl, hf] using hc)

/-- Exact HOL `check_partial_col_success_INJ_lemma`
(`linear_scanProofScript.sml:107-134`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_partial_col_success_INJ_lemma"]
theorem checkPartialColSuccessInjLemma :
    ∀ (live' flive' : NumSet) (l : List Nat) (live flive : NumSet) (f : Nat → Nat),
      sptDomain flive = (fun y => ∃ x, sptDomain live x ∧ f x = y) ∧
      (∀ x y, sptDomain live x → sptDomain live y → f x = f y → x = y) ∧
      checkPartialCol f l live flive = some (live', flive') →
      ∀ x y, (x ∈ l ∨ sptDomain live x) → (y ∈ l ∨ sptDomain live y) →
        f x = f y → x = y := by
  intro live' flive' l live flive f ⟨hd, hi, hc⟩
  have hdom := checkPartialColDomain l f live flive (live', flive') hc
  have hinj := checkPartialColInjOut f l live flive live' flive' hd hi hc
  intro x y hx hy he
  have hx' : sptDomain live' x := by rw [hdom]; exact hx
  have hy' : sptDomain live' y := by rw [hdom]; exact hy
  exact hinj x y hx' hy' he

/-- Exact HOL `check_partial_col_success_INJ` (`linear_scanProofScript.sml:136-148`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_partial_col_success_INJ"]
theorem checkPartialColSuccessInj :
    ∀ (live' flive' : NumSet) (l : List Nat) (live flive : NumSet) (f : Nat → Nat),
      sptDomain flive = (fun y => ∃ x, sptDomain live x ∧ f x = y) ∧
      (∀ x y, sptDomain live x → sptDomain live y → f x = f y → x = y) ∧
      checkPartialCol f l live flive = some (live', flive') →
      (∀ x y, (x ∈ l ∨ sptDomain live x) → (y ∈ l ∨ sptDomain live y) →
        f x = f y → x = y) ∧
      (∀ x y, sptDomain live' x → sptDomain live' y → f x = f y → x = y) := by
  intro live' flive' l live flive f ⟨hd, hi, hc⟩
  exact ⟨checkPartialColSuccessInjLemma live' flive' l live flive f ⟨hd, hi, hc⟩,
    checkPartialColInjOut f l live flive live' flive' hd hi hc⟩

/-- Exact HOL `check_partial_col_input_monotone` (`linear_scanProofScript.sml:150-164`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_partial_col_input_monotone"]
theorem checkPartialColInputMonotone :
    ∀ (f : Nat → Nat) (live1 flive1 live2 flive2 : NumSet) (l : List Nat)
      (v : NumSet × NumSet),
      (fun y => ∃ x, sptDomain live1 x ∧ f x = y) = sptDomain flive1 ∧
        (fun y => ∃ x, sptDomain live2 x ∧ f x = y) = sptDomain flive2 →
      (∀ x, sptDomain live1 x → sptDomain live2 x) →
      (∀ x y, sptDomain live2 x → sptDomain live2 y → f x = f y → x = y) →
      checkPartialCol f l live2 flive2 = some v →
      ∃ livein1 flivein1, checkPartialCol f l live1 flive1 = some (livein1, flivein1) := by
  intro f live1 flive1 live2 flive2 l v ⟨hd1, hd2⟩ hsub hi hc
  obtain ⟨a, b⟩ := v
  have hinj := (checkPartialColSuccessInj a b l live2 flive2 f ⟨hd2.symm, hi, hc⟩).1
  obtain ⟨livein, flivein, hs, -⟩ := checkPartialColSuccess l live1 flive1 f
    ⟨hd1.symm, fun x y hx hy he =>
      hinj x y (hx.imp_right (hsub x)) (hy.imp_right (hsub y)) he⟩
  exact ⟨livein, flivein, hs⟩

/-- Exact HOL `numset_list_delete_IMAGE` (`linear_scanProofScript.sml:166-188`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "numset_list_delete_IMAGE"]
theorem numsetListDeleteImage :
    ∀ (f : Nat → Nat) (l : List Nat) (live flive : NumSet) (v : NumSet × NumSet),
      sptDomain flive = (fun y => ∃ x, sptDomain live x ∧ f x = y) →
      (∀ x y, sptDomain live x → sptDomain live y → f x = f y → x = y) →
      checkPartialCol f l live flive = some v →
      sptDomain (numsetListDelete (l.map f) flive) =
        (fun y => ∃ x, sptDomain (numsetListDelete l live) x ∧ f x = y) := by
  intro f l live flive v hd hi hc
  obtain ⟨a, b⟩ := v
  have hinj := (checkPartialColSuccessInj a b l live flive f ⟨hd, hi, hc⟩).1
  rw [RegAlloc.domainNumsetListDelete, RegAlloc.domainNumsetListDelete, hd]
  funext y
  apply propext
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hnm⟩
    exact ⟨x, ⟨hx, fun hm => hnm (List.mem_map_of_mem hm)⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hnx⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    intro hm
    obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hm
    have := hinj z x (Or.inl hz) (Or.inr hx) hzx
    subst this
    exact hnx hz

/-- Exact HOL `check_partial_col_IMAGE` (`linear_scanProofScript.sml:190-203`):
only the image premise is needed. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_partial_col_IMAGE"]
theorem checkPartialColImage :
    ∀ (f : Nat → Nat) (l : List Nat) (live flive live' flive' : NumSet),
      sptDomain flive = (fun y => ∃ x, sptDomain live x ∧ f x = y) →
      checkPartialCol f l live flive = some (live', flive') →
      sptDomain flive' = (fun y => ∃ x, sptDomain live' x ∧ f x = y)
  | _, [], live, flive, live', flive', hd, hc => by
      simp only [checkPartialCol, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact hd
  | f, h :: l, live, flive, live', flive', hd, hc => by
      cases hl : sptLookup h live with
      | some u =>
          cases u
          exact checkPartialColImage f l live flive live' flive' hd
            (by simpa only [checkPartialCol, hl] using hc)
      | none =>
          cases hf : sptLookup (f h) flive with
          | some _ => simp [checkPartialCol, hl, hf] at hc
          | none =>
              refine checkPartialColImage f l _ _ live' flive' ?_
                (by simpa only [checkPartialCol, hl, hf] using hc)
              rw [sptDomainInsert, sptDomainInsert, hd]
              funext y
              apply propext
              constructor
              · rintro (he | ⟨x, hx, he⟩)
                · exact ⟨h, Or.inl rfl, he.symm⟩
                · exact ⟨x, Or.inr hx, he⟩
              · rintro ⟨x, hx | hx, he⟩
                · subst x; exact Or.inl he.symm
                · exact Or.inr ⟨x, hx, he⟩

/-- Exact HOL `branch_domain` (`linear_scanProofScript.sml:205-212`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "branch_domain"]
theorem branchDomain :
    ∀ (live1 live2 : NumSet),
      (fun x => x ∈ (sptToAList (sptDifference live2 live1)).map Prod.fst ∨
        sptDomain live1 x) = fun x => sptDomain live1 x ∨ sptDomain live2 x := by
  intro live1 live2
  funext x
  apply propext
  rw [sptMemMapFstToAList, sptDomainDifference]
  by_cases h1 : sptDomain live1 x <;> simp [h1]

/-- Pointwise form of `branch_domain` (Flapjack helper, no HOL original). -/
theorem branchDomainIff (live1 live2 : NumSet) (x : Nat) :
    (x ∈ (sptToAList (sptDifference live2 live1)).map Prod.fst ∨ sptDomain live1 x) ↔
      (sptDomain live1 x ∨ sptDomain live2 x) := by
  rw [sptMemMapFstToAList, sptDomainDifference]
  by_cases h1 : sptDomain live1 x <;> simp [h1]

/-- Exact HOL `check_partial_col_branch_domain` (`linear_scanProofScript.sml:214-220`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_partial_col_branch_domain"]
theorem checkPartialColBranchDomain :
    ∀ (f : Nat → Nat) (live1 live2 flive1 liveout fliveout : NumSet),
      checkPartialCol f ((sptToAList (sptDifference live2 live1)).map Prod.fst)
          live1 flive1 = some (liveout, fliveout) →
      sptDomain liveout = fun x => sptDomain live1 x ∨ sptDomain live2 x := by
  intro f live1 live2 flive1 liveout fliveout hc
  rw [← branchDomain]
  exact checkPartialColDomain _ f live1 flive1 (liveout, fliveout) hc

/-- Exact HOL `check_partial_col_branch_comm` (`linear_scanProofScript.sml:223-235`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_partial_col_branch_comm"]
theorem checkPartialColBranchComm :
    ∀ (f : Nat → Nat) (live1 flive1 live2 flive2 a b : NumSet),
      (∀ x y, sptDomain live1 x → sptDomain live1 y → f x = f y → x = y) →
      sptDomain flive1 = (fun y => ∃ x, sptDomain live1 x ∧ f x = y) ∧
        sptDomain flive2 = (fun y => ∃ x, sptDomain live2 x ∧ f x = y) →
      checkPartialCol f ((sptToAList (sptDifference live2 live1)).map Prod.fst)
          live1 flive1 = some (a, b) →
      ∃ c d, checkPartialCol f ((sptToAList (sptDifference live1 live2)).map Prod.fst)
          live2 flive2 = some (c, d) := by
  intro f live1 flive1 live2 flive2 a b hi ⟨hd1, hd2⟩ hc
  have hinj := (checkPartialColSuccessInj a b _ live1 flive1 f ⟨hd1, hi, hc⟩).1
  obtain ⟨c, d, hs, -⟩ := checkPartialColSuccess _ live2 flive2 f
    ⟨hd2, fun x y hx hy he =>
      hinj x y ((branchDomainIff live1 live2 x).mpr ((branchDomainIff live2 live1 x).mp hx).symm)
        ((branchDomainIff live1 live2 y).mpr ((branchDomainIff live2 live1 y).mp hy).symm) he⟩
  exact ⟨c, d, hs⟩

/-- Exact HOL `check_partial_col_list_monotone` (`linear_scanProofScript.sml:237-252`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_partial_col_list_monotone"]
theorem checkPartialColListMonotone :
    ∀ (f : Nat → Nat) (live flive s1 s2 a b : NumSet),
      sptDomain flive = (fun y => ∃ x, sptDomain live x ∧ f x = y) →
      (∀ x y, sptDomain live x → sptDomain live y → f x = f y → x = y) →
      (∀ x, sptDomain s1 x → sptDomain s2 x) →
      checkPartialCol f ((sptToAList s2).map Prod.fst) live flive = some (a, b) →
      ∃ c d, checkPartialCol f ((sptToAList s1).map Prod.fst) live flive = some (c, d) := by
  intro f live flive s1 s2 a b hd hi hsub hc
  have hinj := (checkPartialColSuccessInj a b _ live flive f ⟨hd, hi, hc⟩).1
  obtain ⟨c, d, hs, -⟩ := checkPartialColSuccess _ live flive f
    ⟨hd, fun x y hx hy he => by
      rw [sptMemMapFstToAList] at hx hy
      refine hinj x y ?_ ?_ he
      · rw [sptMemMapFstToAList]; exact hx.imp_left (hsub x)
      · rw [sptMemMapFstToAList]; exact hy.imp_left (hsub y)⟩
  exact ⟨c, d, hs⟩

/-- Exact HOL `check_live_tree_success` (`linear_scanProofScript.sml:254-303`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_live_tree_success"]
theorem checkLiveTreeSuccess :
    ∀ (lt : LiveTree) (live flive live' flive' : NumSet) (f : Nat → Nat),
      sptDomain flive = (fun y => ∃ x, sptDomain live x ∧ f x = y) ∧
      (∀ x y, sptDomain live x → sptDomain live y → f x = f y → x = y) ∧
      checkLiveTree f lt live flive = some (live', flive') →
      sptDomain flive' = (fun y => ∃ x, sptDomain live' x ∧ f x = y) ∧
      (∀ x y, sptDomain live' x → sptDomain live' y → f x = f y → x = y) := by
  intro lt
  induction lt with
  | writes l =>
      intro live flive live' flive' f ⟨hd, hi, hc⟩
      cases hp : checkPartialCol f l live flive with
      | none => simp [checkLiveTree, hp] at hc
      | some v =>
          simp only [checkLiveTree, hp, Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          refine ⟨numsetListDeleteImage f l live flive v hd hi hp, ?_⟩
          intro x y hx hy he
          rw [RegAlloc.domainNumsetListDelete] at hx hy
          exact hi x y hx.1 hy.1 he
  | reads l =>
      intro live flive live' flive' f ⟨hd, hi, hc⟩
      simp only [checkLiveTree] at hc
      exact ⟨checkPartialColImage f l live flive live' flive' hd hc,
        (checkPartialColSuccessInj live' flive' l live flive f ⟨hd, hi, hc⟩).2⟩
  | branch lt1 lt2 ih1 _ =>
      intro live flive live' flive' f ⟨hd, hi, hc⟩
      cases h1 : checkLiveTree f lt1 live flive with
      | none => simp [checkLiveTree, h1] at hc
      | some p1 =>
          obtain ⟨livein1, flivein1⟩ := p1
          cases h2 : checkLiveTree f lt2 live flive with
          | none => simp [checkLiveTree, h1, h2] at hc
          | some p2 =>
              obtain ⟨livein2, flivein2⟩ := p2
              simp only [checkLiveTree, h1, h2] at hc
              obtain ⟨hd1, hi1⟩ := ih1 live flive livein1 flivein1 f ⟨hd, hi, h1⟩
              exact ⟨checkPartialColImage f _ livein1 flivein1 live' flive' hd1 hc,
                (checkPartialColSuccessInj live' flive' _ livein1 flivein1 f
                  ⟨hd1, hi1, hc⟩).2⟩
  | seq lt1 lt2 ih1 ih2 =>
      intro live flive live' flive' f ⟨hd, hi, hc⟩
      cases h2 : checkLiveTree f lt2 live flive with
      | none => simp [checkLiveTree, h2] at hc
      | some p2 =>
          obtain ⟨livein2, flivein2⟩ := p2
          simp only [checkLiveTree, h2] at hc
          obtain ⟨hd2, hi2⟩ := ih2 live flive livein2 flivein2 f ⟨hd, hi, h2⟩
          exact ih1 livein2 flivein2 live' flive' f ⟨hd2, hi2, hc⟩

/-- Exact HOL `ALL_DISTINCT_INJ_MAP` (`linear_scanProofScript.sml:305-311`);
`ALL_DISTINCT` is `List.Nodup`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "ALL_DISTINCT_INJ_MAP"]
theorem allDistinctInjMap {α β : Type} :
    ∀ (f : α → β) (l : List α), (l.map f).Nodup →
      ∀ x y, x ∈ l → y ∈ l → f x = f y → x = y := by
  intro f l
  induction l with
  | nil => intro _ x y hx; simp at hx
  | cons h t ih =>
      intro hnd x y hx0 hy0 he
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hnm, hnd⟩ := hnd
      rcases List.mem_cons.mp hx0 with hx | hx <;> rcases List.mem_cons.mp hy0 with hy | hy
      · rw [hx, hy]
      · subst hx; exact False.elim (hnm (he ▸ List.mem_map_of_mem hy))
      · subst hy; exact False.elim (hnm (he.symm ▸ List.mem_map_of_mem hx))
      · exact ih hnd x y hx hy he

/-- Exact HOL `check_col_output` (`linear_scanProofScript.sml:313-329`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_col_output"]
theorem checkColOutput :
    ∀ (f : Nat → Nat) (live live' flive' : NumSet),
      checkCol f live = some (live', flive') →
      sptDomain flive' = (fun y => ∃ x, sptDomain live' x ∧ f x = y) ∧
      (∀ x y, sptDomain live' x → sptDomain live' y → f x = f y → x = y) := by
  intro f live live' flive' hc
  unfold checkCol at hc
  dsimp only at hc
  split at hc
  · rename_i hpw
    simp only [Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨hl, hf⟩ := hc
    subst hf
    rw [← hl]
    refine ⟨?_, ?_⟩
    · rw [sptDomainFromAList]
      funext y
      apply propext
      simp only [List.map_map, Function.comp_def]
      constructor
      · intro hm
        obtain ⟨⟨k, v⟩, hk, rfl⟩ := List.mem_map.mp hm
        exact ⟨k, (sptMemMapFstToAList live k).mp (List.mem_map_of_mem (f := Prod.fst) hk), rfl⟩
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨⟨k, v⟩, hk, hkx⟩ := List.mem_map.mp ((sptMemMapFstToAList live x).mpr hx)
        simp only at hkx
        subst hkx
        exact List.mem_map.mpr ⟨(k, v), hk, rfl⟩
    · intro x y hx hy he
      have hnd : (((sptToAList live).map Prod.fst).map f).Nodup := by
        rw [List.map_map]; exact hpw
      exact allDistinctInjMap f _ hnd x y ((sptMemMapFstToAList live x).mpr hx)
        ((sptMemMapFstToAList live y).mpr hy) he
  · cases hc

/-- Exact HOL `check_col_success` (`linear_scanProofScript.sml:331-343`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_col_success"]
theorem checkColSuccess :
    ∀ (f : Nat → Nat) (live : NumSet),
      (∀ x y, sptDomain live x → sptDomain live y → f x = f y → x = y) →
      ∃ flive, checkCol f live = some (live, flive) := by
  intro f live hi
  have hnd : ((sptToAList live).map (fun entry => f entry.1)).Pairwise (· ≠ ·) := by
    have hk := sptAllDistinctMapFstToAList live
    unfold List.Nodup at hk
    rw [List.pairwise_map] at hk ⊢
    refine hk.imp_of_mem ?_
    intro a b ha hb hne heq
    apply hne
    exact hi a.1 b.1 ((sptMemMapFstToAList live a.1).mp (List.mem_map_of_mem ha))
      ((sptMemMapFstToAList live b.1).mp (List.mem_map_of_mem hb)) heq
  unfold checkCol
  dsimp only
  rw [if_pos hnd]
  exact ⟨_, rfl⟩

/-- Exact HOL `check_clash_tree_output` (`linear_scanProofScript.sml:345-392`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_clash_tree_output"]
theorem checkClashTreeOutput :
    ∀ (f : Nat → Nat) (ct : ClashTree) (live flive livein flivein : NumSet),
      sptDomain flive = (fun y => ∃ x, sptDomain live x ∧ f x = y) ∧
      (∀ x y, sptDomain live x → sptDomain live y → f x = f y → x = y) ∧
      checkClashTree f ct live flive = some (livein, flivein) →
      sptDomain flivein = (fun y => ∃ x, sptDomain livein x ∧ f x = y) ∧
      (∀ x y, sptDomain livein x → sptDomain livein y → f x = f y → x = y) := by
  intro f ct
  induction ct with
  | delta writes reads =>
      intro live flive livein flivein ⟨hd, hi, hc⟩
      cases hp : checkPartialCol f writes live flive with
      | none => simp [checkClashTree, hp] at hc
      | some v =>
          simp only [checkClashTree, hp] at hc
          have hd' := numsetListDeleteImage f writes live flive v hd hi hp
          have hi' : ∀ x y, sptDomain (numsetListDelete writes live) x →
              sptDomain (numsetListDelete writes live) y → f x = f y → x = y := by
            intro x y hx hy he
            rw [RegAlloc.domainNumsetListDelete] at hx hy
            exact hi x y hx.1 hy.1 he
          exact ⟨checkPartialColImage f reads _ _ livein flivein hd' hc,
            (checkPartialColSuccessInj livein flivein reads _ _ f ⟨hd', hi', hc⟩).2⟩
  | set tree =>
      intro live flive livein flivein ⟨_, _, hc⟩
      exact checkColOutput f tree livein flivein hc
  | branch fixed left right ihl _ =>
      intro live flive livein flivein ⟨hd, hi, hc⟩
      cases hl : checkClashTree f left live flive with
      | none => simp [checkClashTree, hl] at hc
      | some pl =>
          obtain ⟨lo, lc⟩ := pl
          cases hr : checkClashTree f right live flive with
          | none => simp [checkClashTree, hl, hr] at hc
          | some pr =>
              obtain ⟨ro, rc⟩ := pr
              simp only [checkClashTree, hl, hr] at hc
              cases fixed with
              | none =>
                  simp only at hc
                  obtain ⟨hdl, hil⟩ := ihl live flive lo lc ⟨hd, hi, hl⟩
                  exact ⟨checkPartialColImage f _ lo lc livein flivein hdl hc,
                    (checkPartialColSuccessInj livein flivein _ lo lc f ⟨hdl, hil, hc⟩).2⟩
              | some tree =>
                  simp only at hc
                  exact checkColOutput f tree livein flivein hc
  | seq left right ihl ihr =>
      intro live flive livein flivein ⟨hd, hi, hc⟩
      cases hr : checkClashTree f right live flive with
      | none => simp [checkClashTree, hr] at hc
      | some pr =>
          obtain ⟨ro, rc⟩ := pr
          simp only [checkClashTree, hr] at hc
          obtain ⟨hdr, hir⟩ := ihr live flive ro rc ⟨hd, hi, hr⟩
          exact ihl ro rc livein flivein ⟨hdr, hir, hc⟩

/-- Exact HOL `get_live_tree_correct_lemma` (`linear_scanProofScript.sml:394-510`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_live_tree_correct_lemma"]
theorem getLiveTreeCorrectLemma :
    ∀ (f : Nat → Nat) (live flive live' flive' : NumSet) (ct : ClashTree)
      (livein' flivein' : NumSet),
      (fun y => ∃ x, sptDomain live x ∧ f x = y) = sptDomain flive ∧
        (fun y => ∃ x, sptDomain live' x ∧ f x = y) = sptDomain flive' →
      (∀ x y, sptDomain live' x → sptDomain live' y → f x = f y → x = y) →
      (∀ x, sptDomain live x → sptDomain live' x) →
      checkLiveTree f (getLiveTree ct) live' flive' = some (livein', flivein') →
      ∃ livein flivein, checkClashTree f ct live flive = some (livein, flivein) ∧
        (∀ x, sptDomain livein x → sptDomain livein' x) := by
  intro f live flive live' flive' ct
  induction ct generalizing live flive live' flive' with
  | delta lwr lrd =>
      intro livein' flivein' ⟨hd, hd'⟩ hi' hsub hc
      have hi : ∀ x y, sptDomain live x → sptDomain live y → f x = f y → x = y :=
        fun x y hx hy he => hi' x y (hsub x hx) (hsub y hy) he
      simp only [getLiveTree] at hc
      cases hw' : checkPartialCol f lwr live' flive' with
      | none => simp [checkLiveTree, hw'] at hc
      | some w' =>
          simp only [checkLiveTree, hw'] at hc
          obtain ⟨w, hw⟩ := (⟨_, rfl⟩ : ∃ w, checkPartialCol f lwr live flive = w)
          obtain ⟨a, b, hab⟩ :=
            checkPartialColInputMonotone f live flive live' flive' lwr w' ⟨hd, hd'⟩ hsub hi' hw'
          have hdel := numsetListDeleteImage f lwr live flive (a, b) hd.symm hi hab
          have hdel' := numsetListDeleteImage f lwr live' flive' w' hd'.symm hi' hw'
          have hidel' : ∀ x y, sptDomain (numsetListDelete lwr live') x →
              sptDomain (numsetListDelete lwr live') y → f x = f y → x = y := by
            intro x y hx hy he
            rw [RegAlloc.domainNumsetListDelete] at hx hy
            exact hi' x y hx.1 hy.1 he
          have hsubdel : ∀ x, sptDomain (numsetListDelete lwr live) x →
              sptDomain (numsetListDelete lwr live') x := by
            intro x hx
            rw [RegAlloc.domainNumsetListDelete] at hx ⊢
            exact ⟨hsub x hx.1, hx.2⟩
          obtain ⟨l1, fl1, hr⟩ := checkPartialColInputMonotone f _ _ _ _ lrd
            (livein', flivein') ⟨hdel.symm, hdel'.symm⟩ hsubdel hidel' hc
          refine ⟨l1, fl1, ?_, ?_⟩
          · simp only [checkClashTree, hab, hr]
          · intro x hx
            rw [checkPartialColDomain lrd f _ _ (l1, fl1) hr] at hx
            rw [checkPartialColDomain lrd f _ _ (livein', flivein') hc]
            exact hx.imp_right (hsubdel x)
  | set s =>
      intro livein' flivein' ⟨_, hd'⟩ hi' _ hc
      simp only [getLiveTree, checkLiveTree] at hc
      have hdom := checkPartialColDomain _ f live' flive' (livein', flivein') hc
      have hinj := (checkPartialColSuccessInj livein' flivein' _ live' flive' f
        ⟨hd'.symm, hi', hc⟩).1
      obtain ⟨flive0, hcol⟩ := checkColSuccess f s (fun x y hx hy he =>
        hinj x y (Or.inl ((sptMemMapFstToAList s x).mpr hx))
          (Or.inl ((sptMemMapFstToAList s y).mpr hy)) he)
      refine ⟨s, flive0, by simp only [checkClashTree, hcol], ?_⟩
      intro x hx
      rw [hdom]
      exact Or.inl ((sptMemMapFstToAList s x).mpr hx)
  | branch o ct1 ct2 ih1 ih2 =>
      intro livein' flivein' ⟨hd, hd'⟩ hi' hsub hc
      have hi : ∀ x y, sptDomain live x → sptDomain live y → f x = f y → x = y :=
        fun x y hx hy he => hi' x y (hsub x hx) (hsub y hy) he
      -- The `Branch lt1 lt2` check common to both cut-set cases.
      have branchCase : ∀ mid fmid,
          checkLiveTree f (.branch (getLiveTree ct1) (getLiveTree ct2)) live' flive' =
            some (mid, fmid) →
          (∃ livein1 flivein1 livein2 flivein2,
            checkClashTree f ct1 live flive = some (livein1, flivein1) ∧
            checkClashTree f ct2 live flive = some (livein2, flivein2) ∧
            ∃ livein flivein,
              checkPartialCol f ((sptToAList (sptDifference livein2 livein1)).map Prod.fst)
                livein1 flivein1 = some (livein, flivein) ∧
              (∀ x, sptDomain livein x → sptDomain mid x)) ∧
          sptDomain fmid = (fun y => ∃ x, sptDomain mid x ∧ f x = y) ∧
          (∀ x y, sptDomain mid x → sptDomain mid y → f x = f y → x = y) := by
        intro mid fmid hb
        cases h1 : checkLiveTree f (getLiveTree ct1) live' flive' with
        | none => simp [checkLiveTree, h1] at hb
        | some p1 =>
            obtain ⟨l1', f1'⟩ := p1
            cases h2 : checkLiveTree f (getLiveTree ct2) live' flive' with
            | none => simp [checkLiveTree, h1, h2] at hb
            | some p2 =>
                obtain ⟨l2', f2'⟩ := p2
                simp only [checkLiveTree, h1, h2] at hb
                obtain ⟨l1, fl1, hc1, hs1⟩ := ih1 live flive live' flive' l1' f1' ⟨hd, hd'⟩ hi' hsub h1
                obtain ⟨l2, fl2, hc2, hs2⟩ := ih2 live flive live' flive' l2' f2' ⟨hd, hd'⟩ hi' hsub h2
                obtain ⟨hdl1', hil1'⟩ := checkLiveTreeSuccess _ live' flive' l1' f1' f ⟨hd'.symm, hi', h1⟩
                have hinj' := (checkPartialColSuccessInj mid fmid _ l1' f1' f ⟨hdl1', hil1', hb⟩).1
                obtain ⟨hdl1, -⟩ := checkClashTreeOutput f ct1 live flive l1 fl1 ⟨hd.symm, hi, hc1⟩
                obtain ⟨li, fli, hli, -⟩ := checkPartialColSuccess _ l1 fl1 f
                  ⟨hdl1, fun x y hx hy he =>
                    hinj' x y ((branchDomainIff l1' l2' x).mpr
                        (((branchDomainIff l1 l2 x).mp hx).imp (hs1 x) (hs2 x)))
                      ((branchDomainIff l1' l2' y).mpr
                        (((branchDomainIff l1 l2 y).mp hy).imp (hs1 y) (hs2 y))) he⟩
                refine ⟨⟨l1, fl1, l2, fl2, hc1, hc2, li, fli, hli, ?_⟩,
                  checkPartialColImage f _ l1' f1' mid fmid hdl1' hb,
                  (checkPartialColSuccessInj mid fmid _ l1' f1' f ⟨hdl1', hil1', hb⟩).2⟩
                intro x hx
                rw [checkPartialColBranchDomain f l1 l2 fl1 li fli hli] at hx
                rw [checkPartialColBranchDomain f l1' l2' f1' mid fmid hb]
                exact hx.imp (hs1 x) (hs2 x)
      cases o with
      | none =>
          simp only [getLiveTree] at hc
          obtain ⟨⟨l1, fl1, l2, fl2, hc1, hc2, li, fli, hli, hs⟩, -, -⟩ :=
            branchCase livein' flivein' hc
          exact ⟨li, fli, by simp only [checkClashTree, hc1, hc2, hli], hs⟩
      | some cut =>
          have hc' : (match checkLiveTree f (.branch (getLiveTree ct1) (getLiveTree ct2))
              live' flive' with
              | none => none
              | some (livein2, flivein2) =>
                  checkLiveTree f (.reads ((sptToAList cut).map Prod.fst)) livein2 flivein2) =
              some (livein', flivein') := hc
          cases hm : checkLiveTree f (.branch (getLiveTree ct1) (getLiveTree ct2)) live' flive' with
          | none => rw [hm] at hc'; cases hc'
          | some pm =>
              obtain ⟨mid, fmid⟩ := pm
              rw [hm] at hc'
              have hc : checkPartialCol f ((sptToAList cut).map Prod.fst) mid fmid =
                  some (livein', flivein') := hc'
              obtain ⟨⟨l1, fl1, l2, fl2, hc1, hc2, -⟩, hdm, him⟩ := branchCase mid fmid hm
              have hdom := checkPartialColDomain _ f mid fmid (livein', flivein') hc
              have hinj := (checkPartialColSuccessInj livein' flivein' _ mid fmid f
                ⟨hdm, him, hc⟩).1
              obtain ⟨fc, hcol⟩ := checkColSuccess f cut (fun x y hx hy he =>
                hinj x y (Or.inl ((sptMemMapFstToAList cut x).mpr hx))
                  (Or.inl ((sptMemMapFstToAList cut y).mpr hy)) he)
              refine ⟨cut, fc, by simp only [checkClashTree, hc1, hc2, hcol], ?_⟩
              intro x hx
              rw [hdom]
              exact Or.inl ((sptMemMapFstToAList cut x).mpr hx)
  | seq ct1 ct2 ih1 ih2 =>
      intro livein' flivein' ⟨hd, hd'⟩ hi' hsub hc
      have hi : ∀ x y, sptDomain live x → sptDomain live y → f x = f y → x = y :=
        fun x y hx hy he => hi' x y (hsub x hx) (hsub y hy) he
      simp only [getLiveTree] at hc
      cases h2 : checkLiveTree f (getLiveTree ct2) live' flive' with
      | none => simp [checkLiveTree, h2] at hc
      | some p2 =>
          obtain ⟨l2', f2'⟩ := p2
          simp only [checkLiveTree, h2] at hc
          obtain ⟨t2, ft2, hc2, hs2⟩ := ih2 live flive live' flive' l2' f2' ⟨hd, hd'⟩ hi' hsub h2
          obtain ⟨hdt2, -⟩ := checkClashTreeOutput f ct2 live flive t2 ft2 ⟨hd.symm, hi, hc2⟩
          obtain ⟨hdl2', hil2'⟩ := checkLiveTreeSuccess _ live' flive' l2' f2' f ⟨hd'.symm, hi', h2⟩
          obtain ⟨li, fli, hc1, hs1⟩ :=
            ih1 t2 ft2 l2' f2' livein' flivein' ⟨hdt2.symm, hdl2'.symm⟩ hil2' hs2 hc
          exact ⟨li, fli, by simp only [checkClashTree, hc2, hc1], hs1⟩

/-- Exact HOL `get_live_tree_correct` (`linear_scanProofScript.sml:512-520`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_live_tree_correct"]
theorem getLiveTreeCorrect :
    ∀ (f : Nat → Nat) (live flive : NumSet) (ct : ClashTree) (livein flivein : NumSet),
      (fun y => ∃ x, sptDomain live x ∧ f x = y) = sptDomain flive →
      (∀ x y, sptDomain live x → sptDomain live y → f x = f y → x = y) →
      checkLiveTree f (getLiveTree ct) live flive = some (livein, flivein) →
      ∃ livein' flivein', checkClashTree f ct live flive = some (livein', flivein') := by
  intro f live flive ct livein flivein hd hi hc
  obtain ⟨a, b, h, -⟩ :=
    getLiveTreeCorrectLemma f live flive live flive ct livein flivein ⟨hd, hd⟩ hi
      (fun _ hx => hx) hc
  exact ⟨a, b, h⟩

/-- Exact HOL `get_live_tree_correct_LN` (`linear_scanProofScript.sml:522-528`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_live_tree_correct_LN"]
theorem getLiveTreeCorrectLN :
    ∀ (f : Nat → Nat) (ct : ClashTree) (livein flivein : NumSet),
      checkLiveTree f (getLiveTree ct) .ln .ln = some (livein, flivein) →
      ∃ livein' flivein', checkClashTree f ct .ln .ln = some (livein', flivein') := by
  intro f ct livein flivein hc
  refine getLiveTreeCorrect f .ln .ln ct livein flivein ?_ ?_ hc
  · funext y; simp [sptDomain, sptLookup]
  · intro x y hx; simp [sptDomain, sptLookup] at hx

/-- Exact HOL `check_partial_col_numset_list_insert`
(`linear_scanProofScript.sml:530-546`): raw tree equality, no wf premise. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_partial_col_numset_list_insert"]
theorem checkPartialColNumsetListInsert :
    ∀ (f : Nat → Nat) (l : List Nat) (live flive liveout fliveout : NumSet),
      checkPartialCol f l live flive = some (liveout, fliveout) →
      liveout = numsetListInsert l live
  | _, [], live, flive, liveout, fliveout, hc => by
      simp only [checkPartialCol, Option.some.injEq, Prod.mk.injEq] at hc
      exact hc.1.symm
  | f, h :: l, live, flive, liveout, fliveout, hc => by
      rw [numsetListInsert]
      cases hl : sptLookup h live with
      | some u =>
          cases u
          rw [sptInsertUnchanged live h () hl]
          exact checkPartialColNumsetListInsert f l live flive liveout fliveout
            (by simpa only [checkPartialCol, hl] using hc)
      | none =>
          cases hf : sptLookup (f h) flive with
          | some _ => simp [checkPartialCol, hl, hf] at hc
          | none =>
              exact checkPartialColNumsetListInsert f l _ _ liveout fliveout
                (by simpa only [checkPartialCol, hl, hf] using hc)

/-- Exact HOL `check_live_tree_eq_get_live_backward`
(`linear_scanProofScript.sml:548-575`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_live_tree_eq_get_live_backward"]
theorem checkLiveTreeEqGetLiveBackward :
    ∀ (f : Nat → Nat) (lt : LiveTree) (live flive liveout fliveout : NumSet),
      checkLiveTree f lt live flive = some (liveout, fliveout) →
      liveout = getLiveBackward lt live := by
  intro f lt
  induction lt with
  | writes l =>
      intro live flive liveout fliveout hc
      cases hp : checkPartialCol f l live flive with
      | none => simp [checkLiveTree, hp] at hc
      | some _ =>
          simp only [checkLiveTree, hp, Option.some.injEq, Prod.mk.injEq] at hc
          rw [getLiveBackward, ← hc.1]
  | reads l =>
      intro live flive liveout fliveout hc
      exact checkPartialColNumsetListInsert f l live flive liveout fliveout hc
  | branch lt1 lt2 ih1 ih2 =>
      intro live flive liveout fliveout hc
      cases h1 : checkLiveTree f lt1 live flive with
      | none => simp [checkLiveTree, h1] at hc
      | some p1 =>
          obtain ⟨l1, f1⟩ := p1
          cases h2 : checkLiveTree f lt2 live flive with
          | none => simp [checkLiveTree, h1, h2] at hc
          | some p2 =>
              obtain ⟨l2, f2⟩ := p2
              simp only [checkLiveTree, h1, h2] at hc
              rw [checkPartialColNumsetListInsert f _ l1 f1 liveout fliveout hc,
                ih1 live flive l1 f1 h1, ih2 live flive l2 f2 h2]
              rfl
  | seq lt1 lt2 ih1 ih2 =>
      intro live flive liveout fliveout hc
      cases h2 : checkLiveTree f lt2 live flive with
      | none => simp [checkLiveTree, h2] at hc
      | some p2 =>
          obtain ⟨l2, f2⟩ := p2
          simp only [checkLiveTree, h2] at hc
          rw [ih1 l2 f2 liveout fliveout hc, ih2 live flive l2 f2 h2]
          rfl

/-- Exact HOL `fix_domination_fixes_domination` (`linear_scanProofScript.sml:577-582`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "fix_domination_fixes_domination"]
theorem fixDominationFixesDomination :
    ∀ (lt : LiveTree), sptDomain (getLiveBackward (fixDomination lt) .ln) = fun _ => False := by
  intro lt
  simp only [fixDomination]
  split
  · rename_i h
    rw [h]
    funext x
    simp [sptDomain, sptLookup]
  · rw [getLiveBackward, getLiveBackward, RegAlloc.domainNumsetListDelete]
    funext x
    apply propext
    rw [sptMemMapFstToAList]
    simp

/-- Exact HOL `fix_domination_check_live_tree` (`linear_scanProofScript.sml:584-592`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "fix_domination_check_live_tree"]
theorem fixDominationCheckLiveTree :
    ∀ (f : Nat → Nat) (lt : LiveTree) (liveout fliveout : NumSet),
      checkLiveTree f (fixDomination lt) .ln .ln = some (liveout, fliveout) →
      ∃ liveout' fliveout', checkLiveTree f lt .ln .ln = some (liveout', fliveout') := by
  intro f lt liveout fliveout hc
  simp only [fixDomination] at hc
  split at hc
  · exact ⟨liveout, fliveout, hc⟩
  · cases h : checkLiveTree f lt .ln .ln with
    | none => simp [checkLiveTree, h] at hc
    | some p => exact ⟨p.1, p.2, rfl⟩

/-- Exact HOL `size_of_live_tree_positive` (`linear_scanProofScript.sml:594-598`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "size_of_live_tree_positive"]
theorem sizeOfLiveTreePositive : ∀ (lt : LiveTree), 0 ≤ sizeOfLiveTree lt := by
  intro lt
  induction lt with
  | writes _ => simp [sizeOfLiveTree]
  | reads _ => simp [sizeOfLiveTree]
  | branch _ _ ih1 ih2 => simp only [sizeOfLiveTree]; omega
  | seq _ _ ih1 ih2 => simp only [sizeOfLiveTree]; omega

end Flapjack.LinearScan
