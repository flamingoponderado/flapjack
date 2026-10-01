import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan.Sorting
import Flapjack.Compiler.Backend.RegAlloc
import Flapjack.Misc.ListEl

/-!
# linear_scanProof: array equations and register exchange

Ports of `linear_scanProofScript.sml:2020-2402`: the `[simp]` equations of the
generated array accessors, and the correctness of `find_reg_exchange`,
`MAP_colors` and `apply_reg_exchange`. HOL `EL` is the Flapjack rendering
`holEl` (unspecified past the end, as in HOL), `LUPDATE t n l` is
`l.set n t`, and `ALL_DISTINCT` is `List.Nodup`.
-/

namespace Flapjack.LinearScan

open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-! Each accessor equation is the generated definition unfolded through
`Marray_sub`/`Marray_update` and `Msub_eq`/`Mupdate_eq`. -/

private theorem subEqn {value : Type} [Nonempty value] (get : LinearScanHiddenState → List value)
    (n : Nat) (s : LinearScanHiddenState) :
    arraySub get StateException.Subscript n s =
      if n < (get s).length then (.success (holEl n (get s)), s)
      else (.failure .Subscript, s) := by
  unfold arraySub
  split
  · rename_i h; rw [msubEq _ _ _ h, holEl_eq_getElem n _ h]
  · rename_i h; rw [mSubExnEq _ _ _ (by omega)]

private theorem updateEqn {value : Type} (get : LinearScanHiddenState → List value)
    (set : List value → LinearScanHiddenState → LinearScanHiddenState)
    (n : Nat) (t : value) (s : LinearScanHiddenState) :
    arrayUpdate get set StateException.Subscript n t s =
      if n < (get s).length then (.success (), set ((get s).set n t) s)
      else (.failure .Subscript, s) := by
  by_cases h : n < (get s).length
  · rw [if_pos h]; unfold arrayUpdate; rw [mupdateEq _ _ _ _ h]
  · rw [if_neg h]; unfold arrayUpdate; rw [mUpdateExnEq _ _ _ _ (by omega)]

/-- HOL `colors_sub_eqn` (`linear_scanProofScript.sml:2020-2029`).

Provisional and untagged: this ports HOL `colors_sub_eqn` but its statement uses HOL `EL`
(rendered by the untagged total `holEl`, or its bounded form), whose HOL
`listScript` provenance is pending review (bead flapjack-pxn.18.5.15.3.38.1).
Restore the `@[hol]` tag once that review is accepted. -/
theorem colorsSubEqn (n : Nat) (s : LinearScanHiddenState) :
    colorsSub n s = if n < s.colors.length then (.success (holEl n s.colors), s)
      else (.failure .Subscript, s) := subEqn _ n s

/-- Exact HOL `update_colors_eqn` (`linear_scanProofScript.sml:2031-2040`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "update_colors_eqn"]
theorem updateColorsEqn (n t : Nat) (s : LinearScanHiddenState) :
    updateColors n t s = if n < s.colors.length then
      (.success (), { s with colors := s.colors.set n t }) else (.failure .Subscript, s) :=
  updateEqn _ _ n t s

/-- HOL `int_beg_sub_eqn` (`linear_scanProofScript.sml:2042-2051`).

Provisional and untagged: this ports HOL `int_beg_sub_eqn` but its statement uses HOL `EL`
(rendered by the untagged total `holEl`, or its bounded form), whose HOL
`listScript` provenance is pending review (bead flapjack-pxn.18.5.15.3.38.1).
Restore the `@[hol]` tag once that review is accepted. -/
theorem intBegSubEqn (n : Nat) (s : LinearScanHiddenState) :
    intBegSub n s = if n < s.int_beg.length then (.success (holEl n s.int_beg), s)
      else (.failure .Subscript, s) := subEqn _ n s

/-- Exact HOL `update_int_beg_eqn` (`linear_scanProofScript.sml:2053-2062`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "update_int_beg_eqn"]
theorem updateIntBegEqn (n : Nat) (t : Int) (s : LinearScanHiddenState) :
    updateIntBeg n t s = if n < s.int_beg.length then
      (.success (), { s with int_beg := s.int_beg.set n t }) else (.failure .Subscript, s) :=
  updateEqn _ _ n t s

/-- HOL `int_end_sub_eqn` (`linear_scanProofScript.sml:2064-2073`).

Provisional and untagged: this ports HOL `int_end_sub_eqn` but its statement uses HOL `EL`
(rendered by the untagged total `holEl`, or its bounded form), whose HOL
`listScript` provenance is pending review (bead flapjack-pxn.18.5.15.3.38.1).
Restore the `@[hol]` tag once that review is accepted. -/
theorem intEndSubEqn (n : Nat) (s : LinearScanHiddenState) :
    intEndSub n s = if n < s.int_end.length then (.success (holEl n s.int_end), s)
      else (.failure .Subscript, s) := subEqn _ n s

/-- Exact HOL `update_int_end_eqn` (`linear_scanProofScript.sml:2075-2084`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "update_int_end_eqn"]
theorem updateIntEndEqn (n : Nat) (t : Int) (s : LinearScanHiddenState) :
    updateIntEnd n t s = if n < s.int_end.length then
      (.success (), { s with int_end := s.int_end.set n t }) else (.failure .Subscript, s) :=
  updateEqn _ _ n t s

/-- HOL `sorted_regs_sub_eqn` (`linear_scanProofScript.sml:2086-2095`).

Provisional and untagged: this ports HOL `sorted_regs_sub_eqn` but its statement uses HOL `EL`
(rendered by the untagged total `holEl`, or its bounded form), whose HOL
`listScript` provenance is pending review (bead flapjack-pxn.18.5.15.3.38.1).
Restore the `@[hol]` tag once that review is accepted. -/
theorem sortedRegsSubEqn (n : Nat) (s : LinearScanHiddenState) :
    sortedRegsSub n s = if n < s.sorted_regs.length then
      (.success (holEl n s.sorted_regs), s) else (.failure .Subscript, s) := subEqn _ n s

/-- Exact HOL `update_sorted_regs_eqn` (`linear_scanProofScript.sml:2097-2106`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "update_sorted_regs_eqn"]
theorem updateSortedRegsEqn (n t : Nat) (s : LinearScanHiddenState) :
    updateSortedRegs n t s = if n < s.sorted_regs.length then
      (.success (), { s with sorted_regs := s.sorted_regs.set n t })
      else (.failure .Subscript, s) :=
  updateEqn _ _ n t s

/-- HOL `sorted_moves_sub_eqn` (`linear_scanProofScript.sml:2108-2117`).

Provisional and untagged: this ports HOL `sorted_moves_sub_eqn` but its statement uses HOL `EL`
(rendered by the untagged total `holEl`, or its bounded form), whose HOL
`listScript` provenance is pending review (bead flapjack-pxn.18.5.15.3.38.1).
Restore the `@[hol]` tag once that review is accepted. -/
theorem sortedMovesSubEqn (n : Nat) (s : LinearScanHiddenState) :
    sortedMovesSub n s = if n < s.sorted_moves.length then
      (.success (holEl n s.sorted_moves), s) else (.failure .Subscript, s) := subEqn _ n s

/-- Exact HOL `update_sorted_moves_eqn` (`linear_scanProofScript.sml:2119-2128`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "update_sorted_moves_eqn"]
theorem updateSortedMovesEqn (n : Nat) (t : Nat × (Nat × Nat)) (s : LinearScanHiddenState) :
    updateSortedMoves n t s = if n < s.sorted_moves.length then
      (.success (), { s with sorted_moves := s.sorted_moves.set n t })
      else (.failure .Subscript, s) :=
  updateEqn _ _ n t s

/-- HOL proof-script definition `lookup_default_id` (`linear_scanProofScript.sml:2132-2134`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "lookup_default_id_def"]
def lookupDefaultId (s : Spt Nat) (x : Nat) : Nat := (sptLookup x s).elim x (fun x => x)

/-- HOL proof-script definition `find_reg_exchange_step`
(`linear_scanProofScript.sml:2136-2143`); `EL r colors` is unbounded, as in HOL.

Provisional and untagged: this ports HOL `find_reg_exchange_step_def` but its statement uses HOL `EL`
(rendered by the untagged total `holEl`, or its bounded form), whose HOL
`listScript` provenance is pending review (bead flapjack-pxn.18.5.15.3.38.1).
Restore the `@[hol]` tag once that review is accepted. -/
noncomputable def findRegExchangeStep (colors : List Nat) (r : Nat) :
    Spt Nat × Spt Nat → Spt Nat × Spt Nat
  | (exch, invexch) =>
      let col1 := holEl r colors
      let fcol1 := r / 2
      let col2 := lookupDefaultId invexch fcol1
      let fcol2 := lookupDefaultId exch col1
      (sptInsert col1 fcol1 (sptInsert col2 fcol2 exch),
        sptInsert fcol1 col1 (sptInsert fcol2 col2 invexch))

/-- HOL `find_reg_exchange_FOLDL` (`linear_scanProofScript.sml:2145-2153`);
HOL's unused binder `colors` is retained.

Provisional and untagged: this ports HOL `find_reg_exchange_FOLDL` but its statement uses HOL `EL`
(rendered by the untagged total `holEl`, or its bounded form), whose HOL
`listScript` provenance is pending review (bead flapjack-pxn.18.5.15.3.38.1).
Restore the `@[hol]` tag once that review is accepted. -/
theorem findRegExchangeFoldl :
    ∀ (l _colors : List Nat) (exch invexch : Spt Nat) (sth : LinearScanHiddenState),
      (∀ r, r ∈ l → r < sth.colors.length) →
      findRegExchange l exch invexch sth =
        (.success (l.foldl (fun a b => findRegExchangeStep sth.colors b a) (exch, invexch)), sth) := by
  intro l
  induction l with
  | nil => intro _ exch invexch sth _; rfl
  | cons r rs ih =>
      intro colors exch invexch sth hl
      have hr : r < sth.colors.length := hl r List.mem_cons_self
      have step : findRegExchange (r :: rs) exch invexch sth =
          findRegExchange rs
            (sptInsert (holEl r sth.colors) (r / 2)
              (sptInsert (lookupDefaultId invexch (r / 2))
                (lookupDefaultId exch (holEl r sth.colors)) exch))
            (sptInsert (r / 2) (holEl r sth.colors)
              (sptInsert (lookupDefaultId exch (holEl r sth.colors))
                (lookupDefaultId invexch (r / 2)) invexch)) sth := by
        show Translator.Monadic.MonadBase.bind (colorsSub r) _ sth = _
        unfold Translator.Monadic.MonadBase.bind
        rw [colorsSubEqn, if_pos hr]
        rfl
      rw [step, ih colors _ _ sth (fun x hx => hl x (List.mem_cons_of_mem r hx))]
      rfl

/-- Exact HOL `lookup_default_id_insert` (`linear_scanProofScript.sml:2155-2160`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "lookup_default_id_insert"]
theorem lookupDefaultIdInsert :
    ∀ (s : Spt Nat) (k1 k2 v : Nat),
      lookupDefaultId (sptInsert k2 v s) k1 = if k1 = k2 then v else lookupDefaultId s k1 := by
  intro s k1 k2 v
  unfold lookupDefaultId
  by_cases h : k1 = k2
  · subst h; rw [sptLookup_sptInsert_same]; simp
  · rw [sptLookup_sptInsert_ne k2 k1 v s h, if_neg h]

/-- HOL proof-script definition `id` (`linear_scanProofScript.sml:2162-2164`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "id_def"]
def lsId {α : Type} (x : α) : α := x

/-- The induction step of `find_reg_exchange_FOLDR_correct`, with the two
lookup functions abstracted: one step composes the permutation with the
transposition of `cols h` and `σi (h / 2)` (Flapjack helper). -/
private theorem exchangeStep (cols σ σi De Di : Nat → Nat) (h k : Nat) (t : List Nat)
    (hσσi : ∀ x, σ (σi x) = x) (hσiσ : ∀ x, σi (σ x) = x)
    (hD : ∀ x, De x = if x = cols h then h / 2 else if x = σi (h / 2) then σ (cols h) else σ x)
    (hDi : ∀ y, Di y = if y = h / 2 then cols h else if y = σ (cols h) then σi (h / 2) else σi y)
    (hnotin : cols h ∉ t.map cols) (hphy : ∀ r, r ∈ h :: t → r % 2 = 0)
    (hb : ∀ r, r ∈ t → σ (cols r) = r / 2)
    (hc : (∀ r, r ∈ t → (k ≤ cols r ↔ k ≤ r / 2)) → ∀ c, lsId (k ≤ c ↔ k ≤ σ c))
    (hd : (∀ r, r ∈ t → r / 2 < k) → ∀ c, k ≤ c ∧ (∀ r, r ∈ t → c ≠ cols r) → k ≤ σ c)
    (he : (∀ r, r ∈ t → k ≤ cols r ∧ k ≤ r / 2) → ∀ c, c < k → σ c = c) :
    ((De ∘ Di = fun x => x) ∧ (Di ∘ De = fun x => x)) ∧
    (∀ r, r ∈ h :: t → De (cols r) = r / 2) ∧
    ((∀ r, r ∈ h :: t → (k ≤ cols r ↔ k ≤ r / 2)) → ∀ c, lsId (k ≤ c ↔ k ≤ De c)) ∧
    ((∀ r, r ∈ h :: t → r / 2 < k) →
      ∀ c, k ≤ c ∧ (∀ r, r ∈ h :: t → c ≠ cols r) → k ≤ De c) ∧
    ((∀ r, r ∈ h :: t → k ≤ cols r ∧ k ≤ r / 2) → ∀ c, c < k → De c = c) := by
  have hσ2 : σ (σi (h / 2)) = h / 2 := hσσi _
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · funext x
    simp only [Function.comp]
    rw [hDi x]
    by_cases x1 : x = h / 2
    · rw [if_pos x1, hD, if_pos rfl, x1]
    · rw [if_neg x1]
      by_cases x2 : x = σ (cols h)
      · rw [if_pos x2, hD]
        by_cases e : σi (h / 2) = cols h
        · exfalso; apply x1; rw [x2, ← e, hσ2]
        · rw [if_neg e, if_pos rfl, x2]
      · rw [if_neg x2, hD]
        have n1 : σi x ≠ cols h := by intro e; apply x2; rw [← e, hσσi]
        have n2 : σi x ≠ σi (h / 2) := by intro e; apply x1; rw [← hσσi x, e, hσ2]
        rw [if_neg n1, if_neg n2, hσσi]
  · funext y
    simp only [Function.comp]
    rw [hD y]
    by_cases y1 : y = cols h
    · rw [if_pos y1, hDi, if_pos rfl, y1]
    · rw [if_neg y1]
      by_cases y2 : y = σi (h / 2)
      · rw [if_pos y2, hDi]
        have e : σ (cols h) ≠ h / 2 := by
          intro e; apply y1; rw [y2, ← e, hσiσ]
        rw [if_neg e, if_pos rfl, y2]
      · rw [if_neg y2, hDi]
        have n1 : σ y ≠ h / 2 := by intro e; apply y2; rw [← e, hσiσ]
        have n2 : σ y ≠ σ (cols h) := by intro e; apply y1; rw [← hσiσ y, e, hσiσ]
        rw [if_neg n1, if_neg n2, hσiσ]
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · rw [hD, if_pos rfl]
    · have n1 : cols r ≠ cols h := by
        intro e; apply hnotin; rw [← e]; exact List.mem_map_of_mem hr
      have n2 : cols r ≠ σi (h / 2) := by
        intro e
        have h1 := hb r hr
        rw [e, hσ2] at h1
        have pr := hphy r (List.mem_cons_of_mem h hr)
        have ph := hphy h List.mem_cons_self
        have : r = h := by omega
        subst this
        exact n1 rfl
      rw [hD, if_neg n1, if_neg n2, hb r hr]
  · intro H c
    have Ht : ∀ r, r ∈ t → (k ≤ cols r ↔ k ≤ r / 2) :=
      fun r hr => H r (List.mem_cons_of_mem h hr)
    have hc' := hc Ht
    have k1 : k ≤ cols h ↔ k ≤ h / 2 := H h List.mem_cons_self
    have k2 : k ≤ σi (h / 2) ↔ k ≤ h / 2 := by
      have := hc' (σi (h / 2)); simp only [lsId] at this; rw [hσ2] at this; exact this
    simp only [lsId]
    rw [hD]
    by_cases c1 : c = cols h
    · rw [if_pos c1, c1, k1]
    · rw [if_neg c1]
      by_cases c2 : c = σi (h / 2)
      · rw [if_pos c2, c2, k2, ← k1]
        have := hc' (cols h); simp only [lsId] at this; exact this
      · rw [if_neg c2]
        have := hc' c; simp only [lsId] at this; exact this
  · intro H c ⟨hkc, hnc⟩
    have Ht : ∀ r, r ∈ t → r / 2 < k := fun r hr => H r (List.mem_cons_of_mem h hr)
    rw [hD]
    have c1 : c ≠ cols h := hnc h List.mem_cons_self
    rw [if_neg c1]
    by_cases c2 : c = σi (h / 2)
    · exfalso
      have := hd Ht c ⟨hkc, fun r hr => hnc r (List.mem_cons_of_mem h hr)⟩
      rw [c2, hσ2] at this
      have := H h List.mem_cons_self
      omega
    · rw [if_neg c2]
      exact hd Ht c ⟨hkc, fun r hr => hnc r (List.mem_cons_of_mem h hr)⟩
  · intro H c hck
    have Ht : ∀ r, r ∈ t → k ≤ cols r ∧ k ≤ r / 2 := fun r hr => H r (List.mem_cons_of_mem h hr)
    have hh := H h List.mem_cons_self
    rw [hD]
    have c1 : c ≠ cols h := by omega
    rw [if_neg c1]
    by_cases c2 : c = σi (h / 2)
    · exfalso
      have := he Ht c hck
      rw [c2, hσ2] at this
      omega
    · rw [if_neg c2]
      exact he Ht c hck

/-- HOL `find_reg_exchange_FOLDR_correct` (`linear_scanProofScript.sml:2166-2281`).

Provisional and untagged: this ports HOL `find_reg_exchange_FOLDR_correct` but its statement uses HOL `EL`
(rendered by the untagged total `holEl`, or its bounded form), whose HOL
`listScript` provenance is pending review (bead flapjack-pxn.18.5.15.3.38.1).
Restore the `@[hol]` tag once that review is accepted. -/
theorem findRegExchangeFoldrCorrect :
    ∀ (l colors : List Nat) (exch invexch : Spt Nat) (k : Nat),
      (l.map (fun r => holEl r colors)).Nodup ∧ (∀ r, r ∈ l → isPhyVar r) ∧
      (exch, invexch) = l.foldr (fun a b => findRegExchangeStep colors a b) (.ln, .ln) →
      ((lookupDefaultId exch ∘ lookupDefaultId invexch = fun x => x) ∧
        (lookupDefaultId invexch ∘ lookupDefaultId exch = fun x => x)) ∧
      (∀ r, r ∈ l → lookupDefaultId exch (holEl r colors) = r / 2) ∧
      ((∀ r, r ∈ l → (k ≤ holEl r colors ↔ k ≤ r / 2)) →
        ∀ c, lsId (k ≤ c ↔ k ≤ lookupDefaultId exch c)) ∧
      ((∀ r, r ∈ l → r / 2 < k) →
        ∀ c, k ≤ c ∧ (∀ r, r ∈ l → c ≠ holEl r colors) → k ≤ lookupDefaultId exch c) ∧
      ((∀ r, r ∈ l → k ≤ holEl r colors ∧ k ≤ r / 2) →
        ∀ c, c < k → lookupDefaultId exch c = c) := by
  intro l colors
  induction l with
  | nil =>
      intro exch invexch k ⟨_, _, hf⟩
      simp only [List.foldr, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      have d0 : ∀ x, lookupDefaultId .ln x = x := fun x => rfl
      refine ⟨⟨funext fun x => by simp [Function.comp, d0], funext fun x => by
        simp [Function.comp, d0]⟩, by simp, fun _ c => by simp [lsId, d0],
        fun _ c hc => by rw [d0]; exact hc.1, fun _ c _ => d0 c⟩
  | cons h t ih =>
      intro exch invexch k ⟨hnd, hphy, hf⟩
      rcases hft : t.foldr (fun a b => findRegExchangeStep colors a b) (.ln, .ln) with
        ⟨exch1, invexch1⟩
      rw [List.foldr_cons, hft] at hf
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hnotin, hnd⟩ := hnd
      obtain ⟨⟨inv1, inv2⟩, hb, hc, hd, he⟩ :=
        ih exch1 invexch1 k ⟨hnd, fun r hr => hphy r (List.mem_cons_of_mem h hr), hft.symm⟩
      simp only [findRegExchangeStep, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      have hphy' : ∀ r, r ∈ h :: t → r % 2 = 0 := by
        intro r hr; have := hphy r hr; simpa [isPhyVar] using this
      exact exchangeStep (fun r => holEl r colors) (lookupDefaultId exch1)
        (lookupDefaultId invexch1) _ _ h k t
        (fun x => congrFun inv1 x) (fun x => congrFun inv2 x)
        (fun x => by rw [lookupDefaultIdInsert, lookupDefaultIdInsert])
        (fun y => by rw [lookupDefaultIdInsert, lookupDefaultIdInsert])
        hnotin hphy' hb hc hd he

/-- HOL `find_reg_exchange_correct` (`linear_scanProofScript.sml:2283-2311`).

Provisional and untagged: this ports HOL `find_reg_exchange_correct` but its statement uses HOL `EL`
(rendered by the untagged total `holEl`, or its bounded form), whose HOL
`listScript` provenance is pending review (bead flapjack-pxn.18.5.15.3.38.1).
Restore the `@[hol]` tag once that review is accepted. -/
theorem findRegExchangeCorrect :
    ∀ (l : List Nat) (sth : LinearScanHiddenState) (k : Nat),
      (l.map (fun r => holEl r sth.colors)).Nodup ∧ (∀ r, r ∈ l → isPhyVar r) ∧
      (∀ r, r ∈ l → r < sth.colors.length) →
      ∃ exch invexch, findRegExchange l .ln .ln sth = (.success (exch, invexch), sth) ∧
      ((lookupDefaultId exch ∘ lookupDefaultId invexch = fun x => x) ∧
        (lookupDefaultId invexch ∘ lookupDefaultId exch = fun x => x)) ∧
      (∀ r, r ∈ l → lookupDefaultId exch (holEl r sth.colors) = r / 2) ∧
      ((∀ r, r ∈ l → (k ≤ holEl r sth.colors ↔ k ≤ r / 2)) →
        ∀ c, lsId (k ≤ c ↔ k ≤ lookupDefaultId exch c)) ∧
      ((∀ r, r ∈ l → r / 2 < k) →
        ∀ c, k ≤ c ∧ (∀ r, r ∈ l → c ≠ holEl r sth.colors) → k ≤ lookupDefaultId exch c) ∧
      ((∀ r, r ∈ l → k ≤ holEl r sth.colors ∧ k ≤ r / 2) →
        ∀ c, c < k → lookupDefaultId exch c = c) := by
  intro l sth k ⟨hnd, hphy, hlen⟩
  rw [findRegExchangeFoldl l [] .ln .ln sth hlen, List.foldl_eq_foldr_reverse]
  rcases hf : l.reverse.foldr (fun x y => findRegExchangeStep sth.colors x y) (.ln, .ln) with
    ⟨exch, invexch⟩
  refine ⟨exch, invexch, rfl, ?_⟩
  have hnd' : (l.reverse.map (fun r => holEl r sth.colors)).Nodup := by
    rw [List.map_reverse]
    unfold List.Nodup at hnd ⊢
    rw [List.pairwise_reverse]
    exact hnd.imp (fun h e => h e.symm)
  have := findRegExchangeFoldrCorrect l.reverse sth.colors exch invexch k
    ⟨hnd', fun r hr => hphy r (List.mem_reverse.mp hr), hf.symm⟩
  simp only [List.mem_reverse] at this
  exact this

/-- HOL `MAP_colors_eq_lemma` (`linear_scanProofScript.sml:2313-2350`).

Provisional and untagged: this ports HOL `MAP_colors_eq_lemma` but its statement uses HOL `EL`
(rendered by the untagged total `holEl`, or its bounded form), whose HOL
`listScript` provenance is pending review (bead flapjack-pxn.18.5.15.3.38.1).
Restore the `@[hol]` tag once that review is accepted. -/
theorem mapColorsEqLemma :
    ∀ (sth : LinearScanHiddenState) (n : Nat) (f : Nat → Nat),
      n ≤ sth.colors.length →
      ∃ sthout, (.success (), sthout) = mapColors f n sth ∧
        sth.colors.length = sthout.colors.length ∧
        sthout.int_beg = sth.int_beg ∧ sthout.int_end = sth.int_end ∧
        (∀ n', n' < n → holEl n' sthout.colors = f (holEl n' sth.colors)) ∧
        (∀ n', n ≤ n' → holEl n' sthout.colors = holEl n' sth.colors) := by
  intro sth n f
  induction n generalizing sth with
  | zero =>
      intro _
      exact ⟨sth, rfl, rfl, rfl, rfl, fun n' h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  | succ n ih =>
      intro hn
      have hlt : n < sth.colors.length := by omega
      let sth' : LinearScanHiddenState :=
        { sth with colors := sth.colors.set n (f (holEl n sth.colors)) }
      have hlen' : sth'.colors.length = sth.colors.length := by simp [sth']
      obtain ⟨sthout, hrun, hl, hb, he, hlo, hhi⟩ := ih sth' (by omega)
      have hstep : mapColors f (n + 1) sth = mapColors f n sth' := by
        show Translator.Monadic.MonadBase.bind (colorsSub n) _ sth = _
        unfold Translator.Monadic.MonadBase.bind
        rw [colorsSubEqn, if_pos hlt]
        show Translator.Monadic.MonadBase.ignoreBind (updateColors n (f (holEl n sth.colors))) (mapColors f n) sth = _
        unfold Translator.Monadic.MonadBase.ignoreBind
        rw [updateColorsEqn, if_pos hlt]
      refine ⟨sthout, by rw [hstep]; exact hrun, by rw [← hl, hlen'], hb, he, ?_, ?_⟩
      · intro n' hn'
        by_cases e : n' = n
        · subst e
          rw [hhi n' (Nat.le_refl _)]
          show holEl n' (sth.colors.set n' _) = _
          rw [holEl_set _ _ _ _ hlt, if_pos rfl]
        · rw [hlo n' (by omega)]
          show f (holEl n' (sth.colors.set n _)) = _
          rw [holEl_set _ _ _ _ hlt, if_neg (Ne.symm e)]
      · intro n' hn'
        rw [hhi n' (by omega)]
        show holEl n' (sth.colors.set n _) = _
        rw [holEl_set _ _ _ _ hlt, if_neg (by omega)]

/-- HOL `MAP_colors_eq` (`linear_scanProofScript.sml:2352-2362`).

Provisional and untagged: this ports HOL `MAP_colors_eq` but its statement uses HOL `EL`
(rendered by the untagged total `holEl`, or its bounded form), whose HOL
`listScript` provenance is pending review (bead flapjack-pxn.18.5.15.3.38.1).
Restore the `@[hol]` tag once that review is accepted. -/
theorem mapColorsEq :
    ∀ (sth : LinearScanHiddenState) (f : Nat → Nat),
      ∃ sthout, (.success (), sthout) = mapColors f sth.colors.length sth ∧
        (∀ n, n < sth.colors.length → holEl n sthout.colors = f (holEl n sth.colors)) ∧
        sth.colors.length = sthout.colors.length ∧
        sthout.int_beg = sth.int_beg ∧ sthout.int_end = sth.int_end := by
  intro sth f
  obtain ⟨sthout, hrun, hl, hb, he, hlo, -⟩ := mapColorsEqLemma sth sth.colors.length f (Nat.le_refl _)
  exact ⟨sthout, hrun, hlo, hl, hb, he⟩

/-- HOL `apply_reg_exchange_correct` (`linear_scanProofScript.sml:2364-2402`).

Provisional and untagged: this ports HOL `apply_reg_exchange_correct` but its statement uses HOL `EL`
(rendered by the untagged total `holEl`, or its bounded form), whose HOL
`listScript` provenance is pending review (bead flapjack-pxn.18.5.15.3.38.1).
Restore the `@[hol]` tag once that review is accepted. -/
theorem applyRegExchangeCorrect :
    ∀ (l : List Nat) (sth : LinearScanHiddenState) (k : Nat),
      (l.map (fun r => holEl r sth.colors)).Nodup ∧ (∀ r, r ∈ l → isPhyVar r) ∧
      (∀ r, r ∈ l → r < sth.colors.length) →
      ∃ sthout, (.success (), sthout) = applyRegExchange l sth ∧
        sthout.colors.length = sth.colors.length ∧
        sthout.int_beg = sth.int_beg ∧ sthout.int_end = sth.int_end ∧
        (∀ r1 r2, r1 < sth.colors.length ∧ r2 < sth.colors.length →
          holEl r1 sthout.colors = holEl r2 sthout.colors →
          holEl r1 sth.colors = holEl r2 sth.colors) ∧
        (∀ r, r ∈ l → holEl r sthout.colors = r / 2) ∧
        ((∀ r, r ∈ l → (k ≤ holEl r sth.colors ↔ k ≤ r / 2)) →
          ∀ r, r < sth.colors.length →
            (k ≤ holEl r sth.colors ↔ k ≤ holEl r sthout.colors)) ∧
        ((∀ r, r ∈ l → r / 2 < k) →
          ∀ r, r < sth.colors.length ∧ k ≤ holEl r sth.colors ∧
            (∀ r', r' ∈ l → holEl r sth.colors ≠ holEl r' sth.colors) →
            k ≤ holEl r sthout.colors) ∧
        ((∀ r, r ∈ l → k ≤ holEl r sth.colors ∧ k ≤ r / 2) →
          ∀ r, r < sth.colors.length ∧ holEl r sth.colors < k →
            holEl r sthout.colors = holEl r sth.colors) := by
  intro l sth k hpre
  obtain ⟨exch, invexch, hfind, ⟨_, inv2⟩, hb, hc, hd, he⟩ := findRegExchangeCorrect l sth k hpre
  obtain ⟨sthout, hrun, hel, hl, hib, hie⟩ := mapColorsEq sth (lookupDefaultId exch)
  have happ : applyRegExchange l sth = mapColors (lookupDefaultId exch) sth.colors.length sth := by
    show Translator.Monadic.MonadBase.bind (findRegExchange l .ln .ln) _ sth = _
    unfold Translator.Monadic.MonadBase.bind
    rw [hfind]
    rfl
  refine ⟨sthout, by rw [happ]; exact hrun, hl.symm, hib, hie, ?_, ?_, ?_, ?_, ?_⟩
  · intro r1 r2 ⟨h1, h2⟩ heq
    rw [hel r1 h1, hel r2 h2] at heq
    have := congrArg (lookupDefaultId invexch) heq
    have i1 := congrFun inv2 (holEl r1 sth.colors)
    have i2 := congrFun inv2 (holEl r2 sth.colors)
    simp only [Function.comp] at i1 i2
    rw [← i1, ← i2]
    exact this
  · intro r hr
    rw [hel r (hpre.2.2 r hr), hb r hr]
  · intro H r hr
    rw [hel r hr]
    exact hc H (holEl r sth.colors)
  · intro H r ⟨hr, hk, hn⟩
    rw [hel r hr]
    exact hd H _ ⟨hk, hn⟩
  · intro H r ⟨hr, hk⟩
    rw [hel r hr]
    exact he H _ hk

end Flapjack.LinearScan
