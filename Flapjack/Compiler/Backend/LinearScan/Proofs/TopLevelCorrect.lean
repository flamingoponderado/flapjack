import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan.Proofs.WithoutRenaming
import Flapjack.Compiler.Backend.LinearScan.Proofs.Bijection
import Flapjack.Compiler.Backend.LinearScan.Proofs.ApplyBijection
import Flapjack.Compiler.Backend.RegAlloc.SpDefault

/-!
# linear_scanProof: `linear_scan_reg_alloc_correct`

Port of `linear_scanProofScript.sml:6008-6230`, the correctness of the linear-scan
register allocator: the colouring it returns passes `check_clash_tree`, is
defined exactly on the clash-tree registers, respects the physical and stack
register conventions, and separates forced pairs. Renderings as in
`WithoutRenaming` and `ApplyBijection`; HOL `sp_default` is the tagged
`spDefault`.
-/

namespace Flapjack.LinearScan

open Flapjack Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-- `do a; b; c od` associates. -/
private theorem ignoreBind_assoc {σ α β γ ε : Type} (a : M σ α ε) (b : M σ β ε) (c : M σ γ ε)
    (s : σ) : ignoreBind a (ignoreBind b c) s = ignoreBind (ignoreBind a b) c s := by
  simp only [ignoreBind]
  rcases a s with ⟨r, s'⟩
  cases r <;> rfl

private theorem holEl_replicate {α : Type} [Nonempty α] (n i : Nat) (a : α) (h : i < n) :
    holEl i (List.replicate n a) = a := by
  rw [holEl_eq_getElem _ _ (by simpa using h), List.getElem_replicate]

private theorem stack_not_phy' (r : Nat) (h : isStackVar r = true) : isPhyVar r = false := by
  simp only [isStackVar, isPhyVar, decide_eq_true_eq] at h ⊢
  exact decide_eq_false (by omega)

/-- A duplicate-free list of numbers below `n` has at most `n` elements. -/
private theorem nodup_length_le :
    ∀ (n : Nat) (l : List Nat), l.Nodup → (∀ x, x ∈ l → x < n) → l.length ≤ n
  | 0, [], _, _ => Nat.le_refl _
  | 0, x :: _, _, h => absurd (h x List.mem_cons_self) (Nat.not_lt_zero _)
  | n + 1, l, hn, h => by
      by_cases hm : n ∈ l
      · have hlen := List.length_erase_of_mem hm
        have ih := nodup_length_le n (l.erase n) (hn.erase n) (fun x hx => by
          have hne : x ≠ n := fun e => by
            subst e; exact (List.Nodup.not_mem_erase hn) hx
          have := h x (List.mem_of_mem_erase hx)
          omega)
        have : 0 < l.length := List.length_pos_of_mem hm
        omega
      · have ih := nodup_length_le n l hn (fun x hx => by
          have hne : x ≠ n := fun e => hm (e ▸ hx)
          have := h x hx
          omega)
        omega

/-- The values of an association list with distinct keys and injective values
are distinct. -/
private theorem nodup_map_snd {l : List (Nat × Nat)} (hk : (l.map Prod.fst).Nodup)
    (hv : ∀ p, p ∈ l → ∀ q, q ∈ l → p.2 = q.2 → p.1 = q.1) : (l.map Prod.snd).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons p t ih =>
      rw [List.map_cons, List.nodup_cons] at hk ⊢
      refine ⟨fun hm => ?_, ih hk.2 (fun a ha b hb => hv a (List.mem_cons_of_mem _ ha) b
        (List.mem_cons_of_mem _ hb))⟩
      obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
      have := hv q (List.mem_cons_of_mem _ hq) p List.mem_cons_self he
      exact hk.1 (List.mem_map.mpr ⟨q, hq, this⟩)

/-- Exact HOL `linear_scan_reg_alloc_correct` (`linear_scanProofScript.sml:6008-6230`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "linear_scan_reg_alloc_correct"]
theorem linearScanRegAllocCorrect :
    ∀ (k : Nat) (moves : List (Nat × (Nat × Nat))) (ct : ClashTree) (forced : List (Nat × Nat)),
      (∀ x, x ∈ forced → inClashTree ct x.1 ∧ inClashTree ct x.2) →
      ∃ col livein flivein,
        linearScanRegAlloc k moves ct forced = .success col ∧
        checkClashTree (spDefault col) ct .ln .ln = some (livein, flivein) ∧
        (∀ r, inClashTree ct r →
          sptDomain col r ∧
          if isPhyVar r then spDefault col r = r / 2
          else if isStackVar r then k ≤ spDefault col r
          else True) ∧
        (∀ r, sptDomain col r → inClashTree ct r) ∧
        (∀ x, x ∈ forced → spDefault col x.1 = spDefault col x.2 → x.1 = x.2) := by
  intro k moves ct forced hfct
  -- the register bijection
  let bs := findBijectionClashTree findBijectionInit ct
  have hgb := findBijectionClashTreeInvariants findBijectionInit ct (fun _ => False)
    findBijectionInitInvariants
  obtain ⟨hdom, ⟨hinv1, hinv2⟩, ⟨hstk, _, hphy⟩, _, _, _, hnmax⟩ := hgb
  have hdomct : ∀ x, inClashTree ct x ↔ sptDomain bs.bij x := fun x => by
    have := congrFun hdom x
    simp only [or_false] at this
    rw [this]
  let b := fun r => miscThe 0 (sptLookup r bs.bij)
  have hlk : ∀ x, inClashTree ct x → sptLookup x bs.bij = some (b x) := by
    intro x hx
    have hd := (hdomct x).mp hx
    simp only [sptDomain] at hd
    cases h : sptLookup x bs.bij with
    | none => rw [h] at hd; cases hd
    | some v => simp [b, h, miscThe]
  have hbinj : ∀ x y, inClashTree ct x → inClashTree ct y → b x = b y → x = y := by
    intro x y hx hy he
    have h1 := hinv1 x (b x) (hlk x hx)
    have h2 := hinv1 y (b y) (hlk y hy)
    rw [he, h2] at h1
    exact (Option.some.inj h1).symm
  -- the renamed clash tree and its inputs
  let ct' := applyBijOnClashTree ct bs.bij
  have hct' : ∀ y, inClashTree ct' y ↔ ∃ x, inClashTree ct x ∧ b x = y := fun y => by
    have := congrFun (inClashTreeApplyBij bs.bij ct (fun x hx => (hdomct x).mp hx)) y
    exact Iff.of_eq this
  let forced' := forced.map (fun (r1, r2) =>
    (miscThe 0 (sptLookup r1 bs.bij), miscThe 0 (sptLookup r2 bs.bij)))
  let moves' := moves.map (fun (p, (r1, r2)) =>
    (p, (miscThe 0 (sptLookup r1 bs.bij), miscThe 0 (sptLookup r2 bs.bij))))
  let ru := (sptToAList bs.bij).map Prod.snd
  have hru : ∀ r, r ∈ ru ↔ ∃ x, sptLookup x bs.bij = some r := by
    intro r
    simp only [ru, List.mem_map]
    constructor
    · rintro ⟨⟨x, v⟩, hp, rfl⟩
      exact ⟨x, (sptMemToAList _ _ _).mp hp⟩
    · rintro ⟨x, hx⟩
      exact ⟨(x, r), (sptMemToAList _ _ _).mpr hx, rfl⟩
  have hruct : ∀ r, r ∈ ru ↔ inClashTree ct' r := by
    intro r
    rw [hru, hct']
    constructor
    · rintro ⟨x, hx⟩
      have hin : inClashTree ct x := (hdomct x).mpr (by simp [sptDomain, hx])
      refine ⟨x, hin, ?_⟩
      have := hlk x hin
      rw [hx] at this
      exact (Option.some.inj this).symm
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hlk x hx⟩
  have hbmax : ∀ x, b x ≤ bs.nmax := fun x => hnmax x
  have hrund : ru.Nodup := by
    apply nodup_map_snd (sptAllDistinctMapFstToAList _)
    intro p hp q hq he
    have h1 := hinv1 _ _ ((sptMemToAList _ _ _).mp hp)
    have h2 := hinv1 _ _ ((sptMemToAList _ _ _).mp hq)
    rw [he, h2] at h1
    exact (Option.some.inj h1).symm
  have hrub : ∀ r, r ∈ ru → r ≤ bs.nmax := by
    intro r hr
    obtain ⟨x, hx⟩ := (hru r).mp hr
    have := hbmax x
    simp only [b, hx, miscThe] at this
    exact this
  have hrulen : ru.length ≤ bs.nmax + 1 := by
    exact nodup_length_le (bs.nmax + 1) ru hrund (fun r hr => Nat.lt_succ_of_le (hrub r hr))
  -- the hidden state built by the generated runner
  let sth0 : LinearScanHiddenState :=
    { colors := List.replicate (bs.nmax + 1) 0, int_beg := List.replicate (bs.nmax + 1) 1,
      int_end := List.replicate (bs.nmax + 1) 1, sorted_regs := List.replicate (bs.nmax + 1) 0,
      sorted_moves := List.replicate moves'.length (0, (0, 0)) }
  obtain ⟨sthout, livein0, flivein0, hrun, hcheck, hconv, hforced, hlout⟩ :=
    linearRegAllocWithoutRenamingCorrect ru sth0 k moves' ct' forced'
      ⟨fun i hi => by simp only [sth0] at hi ⊢; rw [holEl_replicate _ _ _ (by simpa using hi)]; decide,
        fun i hi => by simp only [sth0] at hi ⊢; rw [holEl_replicate _ _ _ (by simpa using hi)]; decide,
        by simp [sth0],
        hruct,
        fun r hr => by
          obtain ⟨x, _, rfl⟩ := (hct' r).mp hr
          simp only [sth0, List.length_replicate]
          exact Nat.lt_succ_of_le (hbmax x),
        fun x hx => by
          obtain ⟨⟨a, c⟩, hm, rfl⟩ := List.mem_map.mp hx
          exact ⟨(hct' _).mpr ⟨a, (hfct _ hm).1, rfl⟩, (hct' _).mpr ⟨c, (hfct _ hm).2, rfl⟩⟩,
        fun x hx => by
          simp only [moves', List.map_map, List.mem_map] at hx
          obtain ⟨⟨p, a, c⟩, _, rfl⟩ := hx
          simp only [sth0, List.length_replicate]
          exact ⟨Nat.lt_succ_of_le (hbmax a), Nat.lt_succ_of_le (hbmax c)⟩,
        by simpa [sth0] using hrulen,
        by simp [sth0],
        by simp [sth0], by simp [sth0], hrund⟩
  have hsl : sthout.colors.length = bs.nmax + 1 := by rw [hlout]; simp [sth0]
  -- read the colouring back through the inverse bijection
  obtain ⟨col, hext, hcol, hdcol⟩ :=
    extractColorationOutput bs.bij bs.invbij sthout ru .ln
      ⟨hinv1, hinv2, fun r hr => by
          obtain ⟨x, hx⟩ := (hru r).mp hr
          show (sptLookup r bs.invbij).isSome
          rw [hinv1 x r hx]; rfl,
        fun r hr => by rw [hsl]; exact Nat.lt_succ_of_le (hrub r hr)⟩
  have hbru : ∀ r, inClashTree ct r → b r ∈ ru := fun r hr => (hru _).mpr ⟨r, hlk r hr⟩
  have hcolv : ∀ r, inClashTree ct r → sptLookup r col = some (holEl (b r) sthout.colors) := by
    intro r hr
    have := hcol r ((hdomct r).mp hr)
    rw [if_pos (hbru r hr)] at this
    exact this
  have hspd : ∀ r, inClashTree ct r → spDefault col r = holEl (b r) sthout.colors := by
    intro r hr
    simp only [spDefault, hcolv r hr]
  -- transport the checker result back to the original tree
  have hempty : ∀ (f : Nat → Nat),
      sptDomain (Spt.ln : NumSet) = (fun y => ∃ x, sptDomain (Spt.ln : NumSet) x ∧ f x = y) := by
    intro f; funext y; apply propext
    simp [sptDomain, sptLookup]
  obtain ⟨livein, flivein, hcct, _⟩ :=
    checkClashTreeApplyBijection bs.bij bs.invbij (fun r => holEl r sthout.colors) ct .ln .ln
      .ln .ln livein0 flivein0
      ⟨hinv1, hinv2, fun x hx => (hdomct x).mp hx, fun x hx => by simp [sptDomain, sptLookup] at hx,
        hempty _, hempty _, hempty _, fun x _ hx => by simp [sptDomain, sptLookup] at hx, hcheck⟩
  have hceq := checkClashTreeEqualCol (spDefault col) (fun r => holEl (b r) sthout.colors) ct
    .ln .ln ⟨hspd, fun r hr => by simp [sptDomain, sptLookup] at hr⟩
  refine ⟨col, livein, flivein, ?_, by rw [hceq]; exact hcct, fun r hr => ⟨?_, ?_⟩,
    fun r hr => ?_, fun x hx he => ?_⟩
  · -- the run
    have hrun' := hrun
    simp only [linearScanRegAlloc, runLinearRegAllocIntervals, runILinearScanHiddenState, run,
      linearRegAllocAndExtractColoration]
    rw [ignoreBind_assoc]
    show (ignoreBind (ignoreBind (getIntervalsCtMonad ct')
      (linearRegAllocIntervals k forced' moves' ru)) (extractColoration bs.invbij ru .ln) sth0).1 = _
    simp only [ignoreBind] at hrun' ⊢
    rw [hrun']
    simp only [hext]
  · simp [sptDomain, hcolv r hr]
  · have hin' : inClashTree ct' (b r) := (hct' _).mpr ⟨r, hr, rfl⟩
    have hc := hconv (b r) hin'
    rw [hspd r hr]
    split
    · next hp =>
      have hbr : b r = r := (hphy r ⟨Or.inl hr, hp⟩).symm
      rw [hbr] at hc
      rw [if_pos hp] at hc
      rw [hbr]; exact hc
    · next hp =>
      split
      · next hs =>
        have hs' : isStackVar (b r) = true := (hstk r (Or.inl hr)).mp hs
        rw [if_neg (by rw [stack_not_phy' _ hs']; decide), if_pos hs'] at hc
        exact hc
      · trivial
  · rcases hdcol r hr with h | h
    · exact (hdomct r).mpr h
    · simp [sptDomain, sptLookup] at h
  · obtain ⟨h1, h2⟩ := hfct x hx
    rw [hspd _ h1, hspd _ h2] at he
    have hm : (b x.1, b x.2) ∈ forced' := List.mem_map.mpr ⟨x, hx, rfl⟩
    exact hbinj _ _ h1 h2 (hforced _ hm he)

end Flapjack.LinearScan
