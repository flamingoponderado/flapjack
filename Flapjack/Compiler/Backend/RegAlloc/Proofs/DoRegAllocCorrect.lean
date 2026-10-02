import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.Proofs.MkGraphCheckClashTree
import Flapjack.Compiler.Backend.RegAlloc.Proofs.DoAlloc1Success
import Flapjack.Compiler.Backend.RegAlloc.Proofs.AtempAssignment
import Flapjack.Compiler.Backend.RegAlloc.Proofs.StempAssignment
import Flapjack.Compiler.Backend.RegAlloc.Proofs.ColourExtraction
import Flapjack.Compiler.Backend.RegAlloc.Proofs.MkBij

/-!
# reg_allocProof: correctness of `do_reg_alloc`

Ports of `reg_allocProofScript.sml:3235-3490`, `do_reg_alloc_correct` and
`reg_alloc_correct`: from the initial allocator state on the remapping of a clash tree,
`do_reg_alloc` (and hence `reg_alloc`) succeeds and its colouring passes the
`check_clash_tree` oracle, respects the register conventions, is supported on the clash tree,
and separates every forced pair. HOL `REPLICATE` is `List.replicate`, `EVERY`
bounded membership, `DIV` `/`, sets are predicates (`domain` is `sptDomain`) and `LN` is
`Spt.ln`.
-/

namespace Flapjack.RegAlloc

open Flapjack Flapjack.Translator.Monadic.MonadBase

/-- Exact HOL `do_reg_alloc_correct` (`reg_allocProofScript.sml:3235-3453`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "do_reg_alloc_correct"]
theorem doRegAllocCorrect :
    ∀ (alg : Algorithm) (scost : Option (Spt Nat)) (k : Nat)
      (moves : List (Nat × (Nat × Nat))) (ct : ClashTree) (forced : List (Nat × Nat))
      (fs : NumSet) (st : State) (ta fa : Spt Nat) (n : Nat),
      mkBij ct = (ta, fa, n) →
      st.adj_ls = List.replicate n [] →
      st.node_tag = List.replicate n .Atemp →
      st.degrees = List.replicate n 0 →
      st.dim = n →
      st.simp_wl = [] →
      st.spill_wl = [] →
      st.freeze_wl = [] →
      st.avail_moves_wl = [] →
      st.unavail_moves_wl = [] →
      st.coalesced = List.replicate n 0 →
      st.move_related = List.replicate n false →
      (∀ m ∈ forced, inClashTree ct m.1 ∧ inClashTree ct m.2) →
      ∃ spcol st' livein flivein,
        doRegAlloc alg scost k moves ct forced fs (ta, fa, n) st = (.success spcol, st') ∧
        checkClashTree (spDefault spcol) ct .ln .ln = some (livein, flivein) ∧
        (∀ x, inClashTree ct x →
          sptDomain spcol x ∧
            if isPhyVar x then spDefault spcol x = x / 2
            else if isStackVar x then k ≤ spDefault spcol x
            else True) ∧
        (∀ x, sptDomain spcol x → inClashTree ct x) ∧
        ∀ m ∈ forced, spDefault spcol m.1 = spDefault spcol m.2 → m.1 = m.2 := by
  intro alg scost k moves ct forced fs st ta fa n hbij hadj htag hdeg hdim hsimp hspill hfreeze
    havail hunavail hcoal hmr hforced
  /- the remapping bijection -/
  have haux : mkBijAux ct (.ln, .ln, 0) = (ta, fa, n) := by
    have e : mkBij ct = mkBijAux ct (.ln, .ln, 0) := by
      unfold mkBij
      obtain ⟨a, b, c⟩ := mkBijAux ct (.ln, .ln, 0)
      rfl
    rw [← e]; exact hbij
  have hln : ∀ x, ¬ sptDomain (.ln : Spt Nat) x := fun x h => by
    simp [sptDomain, sptLookup] at h
  have hdomta : ∀ x, sptDomain ta x ↔ inClashTree ct x := fun x => by
    have := congrFun (mkBijAuxDomain ct .ln .ln 0 ta fa n haux) x
    simp only [eq_iff_iff] at this
    rw [this]
    exact ⟨fun h => h.resolve_left (hln x), Or.inr⟩
  obtain ⟨hinvtf, hinvft, hdomfa⟩ := mkBijAuxBij ct .ln .ln 0 ta fa n
    ⟨haux, fun m fm h => by simp [sptLookup] at h, fun m fm h => by simp [sptLookup] at h,
      by funext x; simp [sptDomain, sptLookup]⟩
  have hwf : sptWf ta = true := (mkBijAuxWf ct .ln .ln 0 ta fa n ⟨haux, rfl, rfl⟩).1
  have hsome : ∀ x, inClashTree ct x → ∃ v, sptLookup x ta = some v := fun x hx => by
    have h := (hdomta x).mpr hx
    simp only [sptDomain] at h
    cases hl : sptLookup x ta with
    | none => rw [hl] at h; cases h
    | some v => exact ⟨v, rfl⟩
  have hspd : ∀ (t : Spt Nat) x v, sptLookup x t = some v → spDefault t x = v :=
    fun t x v h => by simp only [spDefault, h]
  have hvlt : ∀ x v, sptLookup x ta = some v → v < n := fun x v h => by
    have h2 := hinvtf x v h
    have : sptDomain fa v := by simp [sptDomain, h2]
    rw [hdomfa] at this; exact this
  have hfa : ∀ x v, sptLookup x ta = some v → spDefault fa v = x := fun x v h =>
    hspd fa v x (hinvtf x v h)
  have htainj : ∀ x y, inClashTree ct x → inClashTree ct y →
      spDefault ta x = spDefault ta y → x = y := fun x y hx hy he => by
    obtain ⟨v, hv⟩ := hsome x hx
    obtain ⟨w, hw⟩ := hsome y hy
    rw [hspd ta x v hv, hspd ta y w hw] at he
    subst he
    have h1 := hinvtf x v hv
    have h2 := hinvtf y v hw
    rw [h1] at h2
    exact Option.some.inj h2
  have htab : ∀ x, inClashTree ct x → spDefault ta x < n := fun x hx => by
    obtain ⟨v, hv⟩ := hsome x hx
    rw [hspd ta x v hv]; exact hvlt x v hv
  /- the initial state is good -/
  have hrep : ∀ {α : Type} [Nonempty α] (a : α) i, i < n → holEl i (List.replicate n a) = a :=
    fun a i hi => by
      rw [holEl_eq_getElem _ _ (by simpa using hi), List.getElem_replicate]
  have hg : goodRaState st := by
    refine ⟨by rw [hadj, hdim]; simp, by rw [htag, hdim]; simp, by rw [hdeg, hdim]; simp,
      by rw [hcoal, hdim]; simp, by rw [hmr, hdim]; simp, fun v hv => ?_, fun ls hls v hv => ?_,
      fun ls hls => ?_, (by rw [hsimp]; intro _ h; cases h), (by rw [hspill]; intro _ h; cases h),
      (by rw [hfreeze]; intro _ h; cases h), (by rw [havail]; intro _ h; cases h),
      (by rw [hunavail]; intro _ h; cases h), fun x y he => ?_⟩
    · rw [hcoal] at hv
      obtain ⟨hn, rfl⟩ := List.mem_replicate.mp hv
      rw [hdim]; omega
    · rw [hadj] at hls
      rw [(List.mem_replicate.mp hls).2] at hv
      cases hv
    · rw [hadj] at hls
      rw [(List.mem_replicate.mp hls).2]
      trivial
    · obtain ⟨hx, _, hm⟩ := he
      rw [hadj] at hx hm
      rw [hrep _ x (by simpa using hx)] at hm
      cases hm
  have hadjl : st.adj_ls.length = n := by rw [hadj]; simp
  /- initialisation: graph, forced edges and tags -/
  have hcl0 : isClique ([] : List Nat) st.adj_ls := fun _ _ ⟨h, _⟩ => by cases h
  have hb0 : ∀ y ∈ ([] : List Nat), y < st.dim := fun _ h => by cases h
  obtain ⟨l0, s1, h1, hg1, _, hs1, _, _, _, _⟩ := mkGraphSucceeds ct (spDefault ta) [] st
    ⟨hg, fun x hx => hdim ▸ htab x hx,
      ⟨fun x hx => hadjl ▸ htab x hx, fun x y hx hy he => htainj x y hx hy he⟩,
      hcl0, List.nodup_nil, hb0⟩
  obtain ⟨A1, rfl⟩ : ∃ A, s1 = { st with adj_ls := A } := ⟨_, hs1⟩
  obtain ⟨s2, h2, hg2, hs2, he2⟩ := extendGraphSucceeds forced (spDefault ta)
    { st with adj_ls := A1 } ⟨hg1, fun m hm => ⟨hdim ▸ htab _ (hforced m hm).1,
      hdim ▸ htab _ (hforced m hm).2⟩⟩
  obtain ⟨A2, rfl⟩ : ∃ A, s2 = { ({ st with adj_ls := A1 } : State) with adj_ls := A } :=
    ⟨_, hs2⟩
  obtain ⟨s3, h3, hg3, hs3, htags⟩ := mkTagsSucceeds
    { ({ st with adj_ls := A1 } : State) with adj_ls := A2 } n fs (spDefault fa) ⟨hg2, hdim.symm⟩
  obtain ⟨T3, rfl⟩ : ∃ T, s3 =
      { ({ ({ st with adj_ls := A1 } : State) with adj_ls := A2 } : State) with node_tag := T } :=
    ⟨_, hs3⟩
  /- move filtering and the heuristic allocation -/
  obtain ⟨ts, hf, hts⟩ := stExFilterFullConsistencyOk k (moves.map (updateMove (spDefault ta)))
    [] _ hg3
  obtain ⟨ls, s4, h4, hg4, hsub4, hd4, ht4⟩ := doAlloc1Success _
    (if alg = .Simple then [] else ts) scost k ⟨hg3, fun m hm => by
      split at hm
      · cases hm
      · rcases hts m hm with h | h
        · exact h
        · cases h⟩
  have hn4 : s4.dim = n := hd4.trans hdim
  have hT3 : s4.node_tag = T3 := ht4
  have hT3l : T3.length = n := by rw [← hT3, hg4.2.1, hn4]
  /- tags fixed by `mk_tags` are physical colours -/
  have hfix3 : ∀ i, i < n → ∀ c, holEl i T3 = .Fixed c →
      isPhyVar (spDefault fa i) = true ∧ c = spDefault fa i / 2 := fun i hi c hc => by
    have h := htags i (spDefault fa i) ⟨hi, rfl⟩
    change (if isPhyVar (spDefault fa i) then holEl i T3 = .Fixed (spDefault fa i / 2)
      else if isStackVar (spDefault fa i) then holEl i T3 = .Stemp
      else holEl i T3 = .Atemp ∨ holEl i T3 = .Stemp) at h
    by_cases hp : isPhyVar (spDefault fa i) = true
    · rw [if_pos hp, hc] at h
      exact ⟨hp, Tag.Fixed.inj h⟩
    · rw [if_neg hp] at h
      by_cases hs : isStackVar (spDefault fa i) = true
      · rw [if_pos hs, hc] at h; cases h
      · rw [if_neg hs, hc] at h
        rcases h with h | h <;> cases h
  have hfainj : ∀ x y, x < n → y < n → spDefault fa x = spDefault fa y → x = y :=
    fun x y hx hy he => by
      have hdx : sptDomain fa x := by rw [hdomfa]; exact hx
      have hdy : sptDomain fa y := by rw [hdomfa]; exact hy
      simp only [sptDomain] at hdx hdy
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hdx
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hdy
      rw [hspd fa x u hu, hspd fa y w hw] at he
      subst he
      have e1 := hinvft x u hu
      have e2 := hinvft y u hw
      rw [e1] at e2
      exact Option.some.inj e2
  have hnc4 : noClash s4.adj_ls s4.node_tag := by
    intro x y he
    have hx : x < n := by rw [← hn4, ← hg4.1]; exact he.1
    have hy : y < n := by rw [← hn4, ← hg4.1]; exact he.2.1
    rw [hT3]
    split
    · next a b ha hb =>
        intro hab
        obtain ⟨hpx, hax⟩ := hfix3 x hx a ha
        obtain ⟨hpy, hby⟩ := hfix3 y hy b hb
        simp only [isPhyVar, decide_eq_true_eq] at hpx hpy
        refine hfainj x y hx hy ?_
        omega
    · trivial
  /- colour assignment -/
  obtain ⟨mvs, hmvs⟩ :
      ∃ m, resortMoves (movesToSp (moves.map (updateMove (spDefault ta))) .ln) = m := ⟨_, rfl⟩
  obtain ⟨s5, h5, hnc5, hg5, hs5, hnoA, hkeep5⟩ := assignAtempsCorrect k ls (biasedPref mvs) s4
    ⟨hg4, goodPrefBiasedPref mvs, hnc4⟩
  obtain ⟨T5, rfl⟩ : ∃ T, s5 = { s4 with node_tag := T } := ⟨_, hs5⟩
  obtain ⟨s6, h6, hnc6, hg6, hs6, hst6⟩ := assignStempsCorrect { s4 with node_tag := T5 } k
    (negBiasedPref k mvs) ⟨hg5, hnc5, goodNegPrefNegBiasedPref k mvs⟩
  obtain ⟨T6, rfl⟩ : ∃ T, s6 = { ({ s4 with node_tag := T5 } : State) with node_tag := T } :=
    ⟨_, hs6⟩
  have hT5l : T5.length = n := by rw [← hn4]; exact hg5.2.1
  have hT6l : T6.length = n := by rw [← hn4]; exact hg6.2.1
  have hnoA5 : ∀ m, m < n → holEl m T5 ≠ .Atemp := fun m hm => by
    refine hnoA _ ?_
    show holEl m T5 ∈ T5
    rw [holEl_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hT6 : ∀ m, m < n → if holEl m T5 = .Stemp then ∃ k', holEl m T6 = .Fixed k' ∧ k ≤ k'
      else holEl m T6 = holEl m T5 := fun m hm => hst6 m (by rw [hT5l]; exact hm)
  have hT5 : ∀ m, m < n → holEl m T3 ≠ .Atemp → holEl m T5 = holEl m T3 := fun m hm hna => by
    have := hkeep5 m ⟨by rw [hT3]; omega, by rw [hT3]; exact hna⟩
    rw [hT3] at this; exact this
  have hfixed6 : ∀ m, m < n → ∃ c, holEl m T6 = .Fixed c := fun m hm => by
    have h := hT6 m hm
    by_cases hs : holEl m T5 = .Stemp
    · rw [if_pos hs] at h
      obtain ⟨k', hk', _⟩ := h
      exact ⟨k', hk'⟩
    · rw [if_neg hs] at h
      rw [h]
      cases ht : holEl m T5 with
      | Fixed c => exact ⟨c, rfl⟩
      | Atemp => exact absurd ht (hnoA5 m hm)
      | Stemp => exact absurd ht hs
  /- colour extraction -/
  have hex := extractColorSucceeds _ ta ⟨hg6, fun x y h => by
    show y < s4.dim; rw [hn4]; exact hvlt x y h, hwf⟩
  let g := fun v => extractTag (holEl v T6)
  have hlook : ∀ x v, sptLookup x ta = some v → sptLookup x (sptMap g ta) = some (g v) :=
    fun x v h => by rw [sptLookup_sptMap, h]; rfl
  /- the colouring of the final graph is satisfactory -/
  let col := fun f => if f < T6.length then extractTag (holEl f T6) else 0
  have hcol : colouringSatisfactory col s4.adj_ls := by
    refine noClashColouringSatisfactory s4.adj_ls T6 ⟨hnc6, ?_, fun t ht => ?_⟩
    · rw [hg4.1, hn4, hT6l]
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
      rw [← holEl_eq_getElem _ _ hi]
      obtain ⟨c, hc⟩ := hfixed6 i (by omega)
      rw [hc]
      exact ⟨by simp, by simp⟩
  have hsub12 : isSubgraph A1 A2 := fun a b h => (he2 a b).mpr (Or.inr (Or.inr h))
  have himg0 : (fun y => ∃ x, sptDomain (.ln : NumSet) x ∧ spDefault ta x = y) =
      (fun y => y ∈ ([] : List Nat)) := by
    funext y
    apply propext
    constructor
    · rintro ⟨x, hx, _⟩
      exact absurd hx (hln x)
    · intro h
      cases h
  have hfl0 : sptDomain (.ln : NumSet) =
      (fun y => ∃ x, sptDomain (.ln : NumSet) x ∧ (col ∘ spDefault ta) x = y) := by
    funext y
    apply propext
    constructor
    · intro h
      exact absurd h (hln y)
    · rintro ⟨x, hx, _⟩
      exact absurd hx (hln x)
  obtain ⟨livein, flivein, hcc, -, -⟩ := mkGraphCheckClashTree ct (spDefault ta) [] st l0
    { st with adj_ls := A1 } col .ln .ln ⟨h1,
      colouringSatisfactorySubgraph col s4.adj_ls A1 ⟨hcol,
        isSubgraphTrans _ _ _ ⟨hsub12, hsub4⟩⟩,
      ⟨fun x hx => hadjl ▸ htab x (hx.resolve_right (hln x)),
        fun x y hx hy he => htainj x y (hx.resolve_right (hln x)) (hy.resolve_right (hln y)) he⟩,
      himg0, List.nodup_nil, hb0, hcl0, hg, hfl0⟩
  have hspcol : ∀ x, inClashTree ct x → ∃ v, sptLookup x ta = some v ∧ v < n ∧
      spDefault (sptMap g ta) x = extractTag (holEl v T6) := fun x hx => by
    obtain ⟨v, hv⟩ := hsome x hx
    exact ⟨v, hv, hvlt x v hv, hspd _ x _ (hlook x v hv)⟩
  refine ⟨sptMap g ta, { ({ s4 with node_tag := T5 } : State) with node_tag := T6 }, livein,
    flivein, ?_, ?_, fun x hx => ?_, fun x hx => ?_,
    fun m hm heq => ?_⟩
  · simp only [doRegAlloc, initRaState, ignoreBind, Translator.Monadic.MonadBase.bind, ret, h1,
      h2, h3, hf, h4, hmvs, h5, h6, hex]
    rfl
  · rw [checkClashTreeSameDom ct (spDefault (sptMap g ta)) (col ∘ spDefault ta) .ln .ln
      (fun x hx => ?_)]
    · exact hcc
    · obtain ⟨v, hv, hvn, hx⟩ := hspcol x (hx.resolve_right (hln x))
      simp only [Function.comp_apply, hspd ta x v hv, hx, col, if_pos (show v < T6.length by omega)]
  · obtain ⟨v, hv, hvn, hxv⟩ := hspcol x hx
    refine ⟨by simp [sptDomain, hlook x v hv], ?_⟩
    have ht := htags v x ⟨hvn, (hfa x v hv).symm⟩
    change (if isPhyVar x then holEl v T3 = .Fixed (x / 2)
      else if isStackVar x then holEl v T3 = .Stemp
      else holEl v T3 = .Atemp ∨ holEl v T3 = .Stemp) at ht
    rw [hxv]
    by_cases hp : isPhyVar x = true
    · rw [if_pos hp] at ht ⊢
      have e5 : holEl v T5 = .Fixed (x / 2) := by rw [hT5 v hvn (by rw [ht]; simp), ht]
      have e6 := hT6 v hvn
      rw [if_neg (by rw [e5]; simp), e5] at e6
      rw [e6]; rfl
    · rw [if_neg hp] at ht ⊢
      by_cases hs : isStackVar x = true
      · rw [if_pos hs] at ht ⊢
        have e5 : holEl v T5 = .Stemp := by rw [hT5 v hvn (by rw [ht]; simp), ht]
        have e6 := hT6 v hvn
        rw [if_pos e5] at e6
        obtain ⟨k', hk', hkk⟩ := e6
        rw [hk']; exact hkk
      · rw [if_neg hs]; trivial
  · have h := hx
    simp only [sptDomain, sptLookup_sptMap, Option.isSome_map] at h
    exact (hdomta x).mp h
  · obtain ⟨hx1, hx2⟩ := hforced m hm
    obtain ⟨v1, hv1, hv1n, he1⟩ := hspcol m.1 hx1
    obtain ⟨v2, hv2, hv2n, he2'⟩ := hspcol m.2 hx2
    have hedge : hasEdge A2 v1 v2 :=
      (he2 v1 v2).mpr (Or.inr (Or.inl ⟨m.1, m.2, hspd ta _ _ hv1, hspd ta _ _ hv2, hm⟩))
    have hedge4 := hsub4 v1 v2 hedge
    have hc : col v1 = col v2 := by
      simp only [col, if_pos (show v1 < T6.length by omega), if_pos (show v2 < T6.length by omega)]
      rw [← he1, ← he2']; exact heq
    have hv := hcol v1 hedge4.1 v2 ⟨hedge4.2.1, hedge4.2.2⟩ hc
    exact htainj _ _ hx1 hx2 (by rw [hspd ta _ _ hv1, hspd ta _ _ hv2, hv])

/-- Exact HOL `reg_alloc_correct` (`reg_allocProofScript.sml:3460-3490`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "reg_alloc_correct"]
theorem regAllocCorrect :
    ∀ (alg : Algorithm) (scost : Option (Spt Nat)) (k : Nat)
      (moves : List (Nat × (Nat × Nat))) (ct : ClashTree) (forced : List (Nat × Nat))
      (fs : NumSet),
      (∀ m ∈ forced, inClashTree ct m.1 ∧ inClashTree ct m.2) →
      ∃ spcol livein flivein,
        regAlloc alg scost k moves ct forced fs = .success spcol ∧
        checkClashTree (spDefault spcol) ct .ln .ln = some (livein, flivein) ∧
        (∀ x, inClashTree ct x →
          sptDomain spcol x ∧
            if isPhyVar x then spDefault spcol x = x / 2
            else if isStackVar x then k ≤ spDefault spcol x
            else True) ∧
        (∀ x, sptDomain spcol x → inClashTree ct x) ∧
        ∀ m ∈ forced, spDefault spcol m.1 = spDefault spcol m.2 → m.1 = m.2 := by
  intro alg scost k moves ct forced fs hforced
  rcases hb : mkBij ct with ⟨ta, fa, n⟩
  obtain ⟨spcol, st', livein, flivein, hrun, hcc, hdom, hsup, hfor⟩ :=
    doRegAllocCorrect alg scost k moves ct forced fs
      { adj_ls := List.replicate n [], node_tag := List.replicate n .Atemp,
        degrees := List.replicate n 0, dim := n, simp_wl := [], spill_wl := [], freeze_wl := [],
        avail_moves_wl := [], unavail_moves_wl := [], coalesced := List.replicate n 0,
        move_related := List.replicate n false, stack := [] }
      ta fa n hb rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hforced
  refine ⟨spcol, livein, flivein, ?_, hcc, hdom, hsup, hfor⟩
  simp only [regAlloc, hb, regAllocAux, runIraState, Translator.Monadic.MonadBase.run]
  rw [hrun]

end Flapjack.RegAlloc
