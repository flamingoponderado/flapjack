import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan.Proofs.Intervals

/-!
# linear_scanProof: interval checking implies live-tree checking

Ports of `linear_scanProofScript.sml:1767-2018`: disjoint-colour intervals
(`check_intervals`) make `check_live_tree` succeed on `fix_domination lt`, and
`get_intervals_ct` agrees with `get_intervals` on the live-tree view of the
clash tree. Renderings as in `LiveTree` and `Intervals`; HOL `THE` is the
tagged `holThe`, used only at `SOME` values here.
-/

namespace Flapjack.LinearScan

open Flapjack.RegAlloc

/-- Exact HOL `exists_point_inside_interval_interval_intersect`
(`linear_scanProofScript.sml:1767-1774`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "exists_point_inside_interval_interval_intersect"]
theorem existsPointInsideIntervalIntervalIntersect :
    ∀ (l1 r1 l2 r2 v : Int),
      pointInsideInterval (l1, r1) v ∧ pointInsideInterval (l2, r2) v →
      intervalIntersect (l1, r1) (l2, r2) := by
  intro l1 r1 l2 r2 v ⟨⟨a, b⟩, ⟨c, d⟩⟩
  exact ⟨by omega, by omega⟩

/-- A name with a beginning and an end around `n` has its HOL interval
`(THE beg, THE end)` containing `n` (Flapjack helper). -/
private theorem pointOfLookups (beg end_ : Spt Int) (r : Nat) (vb ve n : Int)
    (hb : sptLookup r beg = some vb) (he : sptLookup r end_ = some ve)
    (h1 : vb ≤ n) (h2 : n ≤ ve) :
    pointInsideInterval (holThe (sptLookup r beg), holThe (sptLookup r end_)) n := by
  rw [hb, he]
  exact ⟨h1, h2⟩

/-- Names whose intervals share a point and whose colours agree are equal
under `check_intervals` (Flapjack helper). -/
private theorem injOfPoints (f : Nat → Nat) (beg end_ : Spt Int) (n : Int)
    (hci : checkIntervals f beg end_) (S : Nat → Prop)
    (hS : ∀ r, S r → sptDomain beg r ∧
      pointInsideInterval (holThe (sptLookup r beg), holThe (sptLookup r end_)) n) :
    ∀ x y, S x → S y → f x = f y → x = y := by
  intro x y hx hy he
  obtain ⟨dx, px⟩ := hS x hx
  obtain ⟨dy, py⟩ := hS y hy
  exact hci x y ⟨dx, dy, existsPointInsideIntervalIntervalIntersect _ _ _ _ n ⟨px, py⟩, he⟩

private theorem someOfDomain (t : Spt Int) (r : Nat) (h : sptDomain t r) :
    ∃ v, sptLookup r t = some v := by
  unfold sptDomain at h
  cases hl : sptLookup r t with
  | none => rw [hl] at h; simp at h
  | some v => exact ⟨v, rfl⟩

/-- Exact HOL `check_intervals_check_live_tree_lemma`
(`linear_scanProofScript.sml:1776-1928`); the free `n_out` is quantified first. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_intervals_check_live_tree_lemma"]
theorem checkIntervalsCheckLiveTreeLemma :
    ∀ (n_out : Int) (lt : LiveTree) (n_in : Int) (beg_out end_out : Spt Int)
      (f : Nat → Nat) (live flive : NumSet),
      checkStartliveProp lt n_in beg_out end_out (n_in - sizeOfLiveTree lt) ∧
      checkNumberPropertyStrong (fun n (live' : NumSet) => ∀ r, sptDomain live' r →
        (sptLookup r beg_out).elim n_out (fun x => x) ≤ n) lt n_in live ∧
      checkNumberProperty (fun n (live' : NumSet) => ∀ r, sptDomain live' r →
        ∃ v, sptLookup r end_out = some v ∧ n + 1 ≤ v) lt n_in live ∧
      checkNumberPropertyStrong (fun _n (live' : NumSet) =>
        ∀ x, sptDomain live' x → sptDomain end_out x) lt n_in live ∧
      sptDomain beg_out = sptDomain end_out ∧
      (∀ x, liveTreeRegisters lt x → sptDomain end_out x) ∧
      checkIntervals f beg_out end_out ∧
      sptDomain flive = (fun y => ∃ x, sptDomain live x ∧ f x = y) ∧
      (∀ x y, sptDomain live x → sptDomain live y → f x = f y → x = y) →
      ∃ liveout fliveout, checkLiveTree f lt live flive = some (liveout, fliveout) := by
  intro n_out lt
  induction lt with
  | writes l =>
      intro n_in beg_out end_out f live flive ⟨hsl, hP, hQ, hR, hde, hreg, hci, hd, _⟩
      have pts : ∀ r, (r ∈ l ∨ sptDomain live r) → sptDomain beg_out r ∧
          pointInsideInterval (holThe (sptLookup r beg_out), holThe (sptLookup r end_out)) n_in := by
        intro r hr
        by_cases hm : r ∈ l
        · obtain ⟨hb, ve, he, hle⟩ := hsl r hm
          have hdb : sptDomain beg_out r := by rw [hde]; exact hreg r hm
          obtain ⟨vb, hvb⟩ := someOfDomain _ _ hdb
          simp only [hvb] at hb
          exact ⟨hdb, pointOfLookups _ _ r vb ve n_in hvb he hb hle⟩
        · have hdl : sptDomain (numsetListDelete l live) r := by
            rw [RegAlloc.domainNumsetListDelete]; exact ⟨hr.resolve_left hm, hm⟩
          have hdb : sptDomain beg_out r := by rw [hde]; exact hR r hdl
          obtain ⟨vb, hvb⟩ := someOfDomain _ _ hdb
          have hp := hP r hdl
          rw [hvb] at hp
          obtain ⟨ve, he, hle⟩ := hQ r hdl
          exact ⟨hdb, pointOfLookups _ _ r vb ve n_in hvb he (by simp at hp; omega) (by omega)⟩
      obtain ⟨livein, flivein, hc, -⟩ :=
        checkPartialColSuccess l live flive f ⟨hd, injOfPoints f _ _ n_in hci _ pts⟩
      exact ⟨numsetListDelete l live, numsetListDelete (l.map f) flive,
        by simp only [checkLiveTree, hc]⟩
  | reads l =>
      intro n_in beg_out end_out f live flive ⟨_, hP, hQ, hR, hde, _, hci, hd, _⟩
      have pts : ∀ r, (r ∈ l ∨ sptDomain live r) → sptDomain beg_out r ∧
          pointInsideInterval (holThe (sptLookup r beg_out), holThe (sptLookup r end_out)) n_in := by
        intro r hr
        have hdl : sptDomain (numsetListInsert l live) r := by
          rw [domainNumsetListInsert]; exact hr
        have hdb : sptDomain beg_out r := by rw [hde]; exact hR r hdl
        obtain ⟨vb, hvb⟩ := someOfDomain _ _ hdb
        have hp := hP r hdl
        rw [hvb] at hp
        obtain ⟨ve, he, hle⟩ := hQ r hdl
        exact ⟨hdb, pointOfLookups _ _ r vb ve n_in hvb he (by simp at hp; omega) (by omega)⟩
      obtain ⟨livein, flivein, hc, -⟩ :=
        checkPartialColSuccess l live flive f ⟨hd, injOfPoints f _ _ n_in hci _ pts⟩
      exact ⟨livein, flivein, hc⟩
  | branch lt1 lt2 ih1 ih2 =>
      intro n_in beg_out end_out f live flive ⟨hsl, hP, hQ, hR, hde, hreg, hci, hd, hi⟩
      have p1 := sizeOfLiveTreePositive lt1
      have p2 := sizeOfLiveTreePositive lt2
      obtain ⟨hsl1, hsl2⟩ := hsl
      obtain ⟨hP1, hP2, hP3⟩ := hP
      obtain ⟨hQ1, hQ2⟩ := hQ
      obtain ⟨hR1, hR2, hR3⟩ := hR
      simp only [liveTreeRegisters] at hreg
      have hsl2' := checkStartlivePropAugmentNdef (n_in - sizeOfLiveTree lt2) lt2 n_in _ _ _
        ⟨hsl2, by simp only [sizeOfLiveTree]; omega, by omega⟩
      obtain ⟨l2, fl2, h2⟩ := ih2 n_in beg_out end_out f live flive
        ⟨hsl2', hP2, hQ2, hR2, hde, fun x hx => hreg x (Or.inr hx), hci, hd, hi⟩
      have hsl1' : checkStartliveProp lt1 (n_in - sizeOfLiveTree lt2) beg_out end_out
          (n_in - sizeOfLiveTree lt2 - sizeOfLiveTree lt1) := by
        simp only [sizeOfLiveTree] at hsl1
        rw [show n_in - sizeOfLiveTree lt2 - sizeOfLiveTree lt1 =
          n_in - (sizeOfLiveTree lt1 + sizeOfLiveTree lt2) by omega]
        exact hsl1
      obtain ⟨l1, fl1, h1⟩ := ih1 (n_in - sizeOfLiveTree lt2) beg_out end_out f live flive
        ⟨hsl1', hP1, hQ1, hR1, hde, fun x hx => hreg x (Or.inl hx), hci, hd, hi⟩
      have e1 := checkLiveTreeEqGetLiveBackward f lt1 live flive l1 fl1 h1
      have e2 := checkLiveTreeEqGetLiveBackward f lt2 live flive l2 fl2 h2
      obtain ⟨hdl1, -⟩ := checkLiveTreeSuccess lt1 live flive l1 fl1 f ⟨hd, hi, h1⟩
      have q1 := checkNumberPropertyIntend end_out lt1 _ live hQ1
      have q2 := checkNumberPropertyIntend end_out lt2 _ live hQ2
      let m := n_in - sizeOfLiveTree (.branch lt1 lt2)
      have pts : ∀ r, (sptDomain l1 r ∨ sptDomain l2 r) → sptDomain beg_out r ∧
          pointInsideInterval (holThe (sptLookup r beg_out), holThe (sptLookup r end_out)) m := by
        intro r hr
        have hgb : sptDomain (getLiveBackward (.branch lt1 lt2) live) r := by
          simp only [getLiveBackward]
          rw [domainNumsetListInsert]
          rw [e1, e2] at hr
          exact (branchDomainIff _ _ r).mpr hr
        have hdb : sptDomain beg_out r := by rw [hde]; exact hR3 r hgb
        obtain ⟨vb, hvb⟩ := someOfDomain _ _ hdb
        have hp := hP3 r hgb
        rw [hvb] at hp
        simp at hp
        refine ⟨hdb, ?_⟩
        rw [e1, e2] at hr
        rcases hr with hr | hr
        · obtain ⟨ve, he, hle⟩ := q1 r hr
          exact pointOfLookups _ _ r vb ve m hvb he hp
            (by simp only [m, sizeOfLiveTree]; omega)
        · obtain ⟨ve, he, hle⟩ := q2 r hr
          exact pointOfLookups _ _ r vb ve m hvb he hp
            (by simp only [m, sizeOfLiveTree]; omega)
      have hinj := injOfPoints f _ _ m hci _ pts
      obtain ⟨li, fli, hc, -⟩ := checkPartialColSuccess _ l1 fl1 f
        ⟨hdl1, fun x y hx hy he => hinj x y ((branchDomainIff l1 l2 x).mp hx)
          ((branchDomainIff l1 l2 y).mp hy) he⟩
      exact ⟨li, fli, by simp only [checkLiveTree, h1, h2, hc]⟩
  | seq lt1 lt2 ih1 ih2 =>
      intro n_in beg_out end_out f live flive ⟨hsl, hP, hQ, hR, hde, hreg, hci, hd, hi⟩
      have p1 := sizeOfLiveTreePositive lt1
      have p2 := sizeOfLiveTreePositive lt2
      obtain ⟨hsl1, hsl2⟩ := hsl
      obtain ⟨hP1, hP2⟩ := hP
      obtain ⟨hQ1, hQ2⟩ := hQ
      obtain ⟨hR1, hR2⟩ := hR
      simp only [liveTreeRegisters] at hreg
      have hsl2' := checkStartlivePropAugmentNdef (n_in - sizeOfLiveTree lt2) lt2 n_in _ _ _
        ⟨hsl2, by simp only [sizeOfLiveTree]; omega, by omega⟩
      obtain ⟨l2, fl2, h2⟩ := ih2 n_in beg_out end_out f live flive
        ⟨hsl2', hP2, hQ2, hR2, hde, fun x hx => hreg x (Or.inr hx), hci, hd, hi⟩
      have e2 := checkLiveTreeEqGetLiveBackward f lt2 live flive l2 fl2 h2
      obtain ⟨hdl2, hil2⟩ := checkLiveTreeSuccess lt2 live flive l2 fl2 f ⟨hd, hi, h2⟩
      have hsl1' : checkStartliveProp lt1 (n_in - sizeOfLiveTree lt2) beg_out end_out
          (n_in - sizeOfLiveTree lt2 - sizeOfLiveTree lt1) := by
        simp only [sizeOfLiveTree] at hsl1
        rw [show n_in - sizeOfLiveTree lt2 - sizeOfLiveTree lt1 =
          n_in - (sizeOfLiveTree lt1 + sizeOfLiveTree lt2) by omega]
        exact hsl1
      rw [← e2] at hP1 hQ1 hR1
      obtain ⟨l1, fl1, h1⟩ := ih1 (n_in - sizeOfLiveTree lt2) beg_out end_out f l2 fl2
        ⟨hsl1', hP1, hQ1, hR1, hde, fun x hx => hreg x (Or.inl hx), hci, hdl2, hil2⟩
      exact ⟨l1, fl1, by simp only [checkLiveTree, h2, h1]⟩

/-- Exact HOL `check_intervals_check_live_tree` (`linear_scanProofScript.sml:1930-1950`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_intervals_check_live_tree"]
theorem checkIntervalsCheckLiveTree :
    ∀ (lt : LiveTree) (n_out : Int) (beg_out end_out : Spt Int) (f : Nat → Nat),
      (n_out, beg_out, end_out) = getIntervals (fixDomination lt) 0 .ln .ln ∧
      checkIntervals f beg_out end_out →
      ∃ liveout fliveout, checkLiveTree f (fixDomination lt) .ln .ln = some (liveout, fliveout) := by
  intro lt n_out beg_out end_out f ⟨h, hci⟩
  have hnone : ∀ r v, sptLookup r (Spt.ln : Spt Int) = some v → (0 : Int) ≤ v := by
    intro r v hv; simp [sptLookup] at hv
  have emp : ∀ r, ¬ sptDomain (Spt.ln : NumSet) r := by intro r; simp [sptDomain, sptLookup]
  have hsl := getIntervalsCheckStartliveProp _ _ _ _ _ _ _ ⟨h, hnone⟩
  have hP := getIntervalsBegLessLive lt () _ _ _ h
  have hQ := getIntervalsLiveLessEnd _ _ _ _ .ln _ _ _ ⟨h, fun r hr => absurd hr (emp r)⟩
  have hR := checkNumberPropertySubsetEndout _ _ _ _ .ln _ _ _ ⟨h, fun x hx => absurd hx (emp x)⟩
  obtain ⟨db, de⟩ := getIntervalsDomainEqLiveTreeRegisters lt _ _ _ h
  have hn := getIntervalsNout _ _ _ _ _ _ _ h
  rw [hn] at hP
  refine checkIntervalsCheckLiveTreeLemma (0 - sizeOfLiveTree (fixDomination lt)) _ 0 _ _ f .ln .ln
    ⟨?_, hP, hQ, hR, db.trans de.symm, fun x hx => by rw [de]; exact hx, hci, ?_, ?_⟩
  · rw [← hn]; exact hsl
  · funext y; apply propext; simp [sptDomain, sptLookup]
  · intro x y hx; exact absurd hx (emp x)

/-! Structural unfolding of the compound `get_intervals_ct_aux` cases. -/

private theorem getIntervalsCtAuxBranch (o : Option NumSet) (ct1 ct2 : ClashTree) (n : Int)
    (b e : Spt Int) (live : NumSet) (n_out : Int) (b_out e_out : Spt Int) (l_out : NumSet)
    (h : (n_out, b_out, e_out, l_out) = getIntervalsCtAux (.branch o ct1 ct2) n b e live) :
    ∃ n2 b2 e2 l2 n1 b1 e1 l1,
      (n2, b2, e2, l2) = getIntervalsCtAux ct2 n b e live ∧
      (n1, b1, e1, l1) = getIntervalsCtAux ct1 n2 b2 e2 live ∧
      (o = none → (n_out, b_out, e_out, l_out) = (n1, b1, e1, sptUnion l1 l2)) ∧
      (∀ cutset, o = some cutset → (n_out, b_out, e_out, l_out) =
        (n1 - 1, b1, numsetListAddIfGt ((sptToAList cutset).map Prod.fst) n1 e1,
          sptUnion cutset (sptUnion l1 l2))) := by
  rcases h2 : getIntervalsCtAux ct2 n b e live with ⟨n2, b2, e2, l2⟩
  rcases h1 : getIntervalsCtAux ct1 n2 b2 e2 live with ⟨n1, b1, e1, l1⟩
  refine ⟨n2, b2, e2, l2, n1, b1, e1, l1, rfl, h1.symm, ?_, ?_⟩
  · intro ho; subst ho; simp only [getIntervalsCtAux, h2, h1] at h; exact h
  · intro c hc; subst hc; simp only [getIntervalsCtAux, h2, h1] at h; exact h

private theorem getIntervalsCtAuxSeq (ct1 ct2 : ClashTree) (n : Int)
    (b e : Spt Int) (live : NumSet) (n_out : Int) (b_out e_out : Spt Int) (l_out : NumSet)
    (h : (n_out, b_out, e_out, l_out) = getIntervalsCtAux (.seq ct1 ct2) n b e live) :
    ∃ n2 b2 e2 l2, (n2, b2, e2, l2) = getIntervalsCtAux ct2 n b e live ∧
      (n_out, b_out, e_out, l_out) = getIntervalsCtAux ct1 n2 b2 e2 l2 := by
  rcases h2 : getIntervalsCtAux ct2 n b e live with ⟨n2, b2, e2, l2⟩
  simp only [getIntervalsCtAux, h2] at h
  exact ⟨n2, b2, e2, l2, rfl, h⟩

/-- Exact HOL `get_intervals_ct_aux_live` (`linear_scanProofScript.sml:1952-1977`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_ct_aux_live"]
theorem getIntervalsCtAuxLive :
    ∀ (ct : ClashTree) (n_in : Int) (beg_in end_in : Spt Int) (live_in live_in' : NumSet)
      (n_out : Int) (beg_out end_out : Spt Int) (live_out : NumSet),
      sptDomain live_in = sptDomain live_in' ∧
      (n_out, beg_out, end_out, live_out) = getIntervalsCtAux ct n_in beg_in end_in live_in →
      sptDomain live_out = sptDomain (getLiveBackward (getLiveTree ct) live_in') := by
  intro ct
  induction ct with
  | delta wr rd =>
      intro n_in beg_in end_in live_in live_in' n_out beg_out end_out live_out ⟨hl, h⟩
      simp only [getIntervalsCtAux, Prod.mk.injEq] at h
      rw [h.2.2.2]
      simp only [getLiveTree, getLiveBackward]
      rw [domainNumsetListInsert, domainNumsetListInsert, RegAlloc.domainNumsetListDelete,
        RegAlloc.domainNumsetListDelete, hl]
  | set cutset =>
      intro n_in beg_in end_in live_in live_in' n_out beg_out end_out live_out ⟨hl, h⟩
      simp only [getIntervalsCtAux, Prod.mk.injEq] at h
      rw [h.2.2.2]
      simp only [getLiveTree, getLiveBackward]
      rw [domainNumsetListInsert, sptDomain_sptUnion, hl]
      funext x
      rw [sptMemMapFstToAList]
  | branch o ct1 ct2 ih1 ih2 =>
      intro n_in beg_in end_in live_in live_in' n_out beg_out end_out live_out ⟨hl, h⟩
      obtain ⟨n2, b2, e2, l2, n1, b1, e1, l1, h2, h1, hnone, hsome⟩ :=
        getIntervalsCtAuxBranch o ct1 ct2 _ _ _ _ _ _ _ _ h
      have d2 := ih2 _ _ _ _ _ _ _ _ _ ⟨hl, h2⟩
      have d1 := ih1 _ _ _ _ _ _ _ _ _ ⟨hl, h1⟩
      have hbr : sptDomain (getLiveBackward (.branch (getLiveTree ct1) (getLiveTree ct2)) live_in') =
          fun x => sptDomain l1 x ∨ sptDomain l2 x := by
        simp only [getLiveBackward]
        rw [domainNumsetListInsert, d1, d2]
        funext x
        exact propext (branchDomainIff _ _ x)
      cases o with
      | none =>
          have hres := hnone rfl
          simp only [Prod.mk.injEq] at hres
          rw [hres.2.2.2, sptDomain_sptUnion]
          simp only [getLiveTree]
          rw [hbr]
      | some cut =>
          have hres := hsome cut rfl
          simp only [Prod.mk.injEq] at hres
          rw [hres.2.2.2, sptDomain_sptUnion, sptDomain_sptUnion]
          simp only [getLiveTree]
          rw [show getLiveBackward (.seq (.reads ((sptToAList cut).map Prod.fst))
              (.branch (getLiveTree ct1) (getLiveTree ct2))) live_in' =
            numsetListInsert ((sptToAList cut).map Prod.fst)
              (getLiveBackward (.branch (getLiveTree ct1) (getLiveTree ct2)) live_in') from rfl]
          rw [domainNumsetListInsert, hbr]
          funext x
          rw [sptMemMapFstToAList]
  | seq ct1 ct2 ih1 ih2 =>
      intro n_in beg_in end_in live_in live_in' n_out beg_out end_out live_out ⟨hl, h⟩
      obtain ⟨n2, b2, e2, l2, h2, h1⟩ := getIntervalsCtAuxSeq ct1 ct2 _ _ _ _ _ _ _ _ h
      have d2 := ih2 _ _ _ _ _ _ _ _ _ ⟨hl, h2⟩
      exact ih1 _ _ _ _ _ _ _ _ _ ⟨d2, h1⟩

/-- Exact HOL `get_intervals_ct_aux_int` (`linear_scanProofScript.sml:1979-2001`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_ct_aux_int"]
theorem getIntervalsCtAuxInt :
    ∀ (ct : ClashTree) (n_in : Int) (beg_in end_in : Spt Int) (live_in : NumSet)
      (n_out : Int) (beg_out end_out : Spt Int) (live_out : NumSet),
      (n_out, beg_out, end_out, live_out) = getIntervalsCtAux ct n_in beg_in end_in live_in →
      (n_out, beg_out, end_out) = getIntervals (getLiveTree ct) n_in beg_in end_in := by
  intro ct
  induction ct with
  | delta wr rd =>
      intro n_in beg_in end_in live_in n_out beg_out end_out live_out h
      simp only [getIntervalsCtAux, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, -⟩ := h
      simp only [getLiveTree, getIntervals, h1, h2, h3]
      congr 1
      omega
  | set cutset =>
      intro n_in beg_in end_in live_in n_out beg_out end_out live_out h
      simp only [getIntervalsCtAux, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, -⟩ := h
      simp only [getLiveTree, getIntervals, h1, h2, h3]
  | branch o ct1 ct2 ih1 ih2 =>
      intro n_in beg_in end_in live_in n_out beg_out end_out live_out h
      obtain ⟨n2, b2, e2, l2, n1, b1, e1, l1, h2, h1, hnone, hsome⟩ :=
        getIntervalsCtAuxBranch o ct1 ct2 _ _ _ _ _ _ _ _ h
      have g2 := ih2 _ _ _ _ _ _ _ _ h2
      have g1 := ih1 _ _ _ _ _ _ _ _ h1
      have hb : getIntervals (.branch (getLiveTree ct1) (getLiveTree ct2)) n_in beg_in end_in =
          (n1, b1, e1) := by
        simp only [getIntervals]
        rw [← g2]
        exact g1.symm
      cases o with
      | none =>
          have hres := hnone rfl
          simp only [Prod.mk.injEq] at hres
          obtain ⟨r1, r2, r3, -⟩ := hres
          simp only [getLiveTree]
          rw [hb, r1, r2, r3]
      | some cut =>
          have hres := hsome cut rfl
          simp only [Prod.mk.injEq] at hres
          obtain ⟨r1, r2, r3, -⟩ := hres
          simp only [getLiveTree]
          rw [show getIntervals (.seq (.reads ((sptToAList cut).map Prod.fst))
              (.branch (getLiveTree ct1) (getLiveTree ct2))) n_in beg_in end_in =
            (match getIntervals (.branch (getLiveTree ct1) (getLiveTree ct2)) n_in beg_in end_in with
              | (n2, b2, e2) => getIntervals (.reads ((sptToAList cut).map Prod.fst)) n2 b2 e2)
            from rfl, hb]
          simp only [getIntervals, r1, r2, r3]
  | seq ct1 ct2 ih1 ih2 =>
      intro n_in beg_in end_in live_in n_out beg_out end_out live_out h
      obtain ⟨n2, b2, e2, l2, h2, h1⟩ := getIntervalsCtAuxSeq ct1 ct2 _ _ _ _ _ _ _ _ h
      have g2 := ih2 _ _ _ _ _ _ _ _ h2
      have g1 := ih1 _ _ _ _ _ _ _ _ h1
      simp only [getLiveTree, getIntervals]
      rw [← g2]
      exact g1

/-- Exact HOL `get_intervals_ct_eq` (`linear_scanProofScript.sml:2003-2018`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_ct_eq"]
theorem getIntervalsCtEq :
    ∀ (ct : ClashTree) (int_beg1 int_beg2 int_end1 int_end2 : Spt Int) (n1 n2 : Int),
      (n1, int_beg1, int_end1) = getIntervalsCt ct ∧
      (n2, int_beg2, int_end2) = getIntervals (fixDomination (getLiveTree ct)) 0 .ln .ln →
      (∀ r, sptLookup r int_beg1 = sptLookup r int_beg2) ∧
      (∀ r, sptLookup r int_end1 = sptLookup r int_end2) := by
  intro ct int_beg1 int_beg2 int_end1 int_end2 n1 n2 ⟨h1, h2⟩
  rcases ha : getIntervalsCtAux ct 0 .ln .ln .ln with ⟨n, b, e, live⟩
  have hint := getIntervalsCtAuxInt ct _ _ _ _ _ _ _ _ ha.symm
  have hlive := getIntervalsCtAuxLive ct _ _ _ .ln .ln _ _ _ _ ⟨rfl, ha.symm⟩
  simp only [getIntervalsCt, ha, Prod.mk.injEq] at h1
  obtain ⟨-, rb, re⟩ := h1
  subst rb; subst re
  have memEq : ∀ r, r ∈ (sptToAList live).map Prod.fst ↔
      r ∈ (sptToAList (getLiveBackward (getLiveTree ct) .ln)).map Prod.fst := by
    intro r
    rw [sptMemMapFstToAList, sptMemMapFstToAList, hlive]
  simp only [fixDomination] at h2
  split at h2
  · rename_i hln
    rw [← hint] at h2
    simp only [Prod.mk.injEq] at h2
    obtain ⟨-, rfl, rfl⟩ := h2
    have hno : ∀ r, r ∉ (sptToAList live).map Prod.fst := by
      intro r hr
      rw [memEq, hln] at hr
      simp at hr
    constructor
    · intro r; rw [lookupNumsetListAddIfLt, if_neg (hno r)]
    · intro r; rw [lookupNumsetListAddIfGt, if_neg (hno r)]
  · rw [show getIntervals (.seq (.writes ((sptToAList (getLiveBackward (getLiveTree ct) .ln)).map
          Prod.fst)) (getLiveTree ct)) 0 .ln .ln =
        (match getIntervals (getLiveTree ct) 0 .ln .ln with
          | (n2, b2, e2) => getIntervals (.writes ((sptToAList (getLiveBackward (getLiveTree ct)
              .ln)).map Prod.fst)) n2 b2 e2) from rfl, ← hint] at h2
    simp only [getIntervals, Prod.mk.injEq] at h2
    obtain ⟨-, rfl, rfl⟩ := h2
    constructor
    · intro r
      rw [lookupNumsetListAddIfLt, lookupNumsetListAddIfLt]
      by_cases hm : r ∈ (sptToAList live).map Prod.fst
      · rw [if_pos hm, if_pos ((memEq r).mp hm)]
      · rw [if_neg hm, if_neg (fun h => hm ((memEq r).mpr h))]
    · intro r
      rw [lookupNumsetListAddIfGt, lookupNumsetListAddIfGt]
      by_cases hm : r ∈ (sptToAList live).map Prod.fst
      · rw [if_pos hm, if_pos ((memEq r).mp hm)]
      · rw [if_neg hm, if_neg (fun h => hm ((memEq r).mpr h))]

end Flapjack.LinearScan
