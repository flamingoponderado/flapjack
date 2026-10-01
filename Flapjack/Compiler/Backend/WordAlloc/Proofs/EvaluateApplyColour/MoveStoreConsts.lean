import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Leaves

/-!
# `evaluate_apply_colour` `Move` and `StoreConsts` cases

HOL `Resume evaluate_apply_colour[Move]` (`word_allocProofScript.sml:1169-1223`)
and `Resume evaluate_apply_colour[StoreConsts]`
(`word_allocProofScript.sml:2024-2061`). Neither case has a sub-program, so
neither needs an induction hypothesis. Each theorem is the HOL theorem with
`prog` fixed to that constructor: the same `st cst f live lt` binders, the same
three HOL premises and the same existential conclusion.

The untagged helpers below are local Lean proof infrastructure; they factor the
`alist_insert` and `delete` reasoning these two cases share. They do not claim
to port independent HOL declarations.
-/

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

namespace EvaluateApplyColourMoveStoreConstsWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end EvaluateApplyColourMoveStoreConstsWitnesses

/-- Lookup of the source state after a fold of `sptDelete`; a key survives
exactly when it is in the source tree and is not one of the deleted keys. -/
theorem sptDomain_foldr_sptDelete {α : Type} (ks : List Nat) (t : Spt α) (n : Nat) :
    sptDomain (ks.foldr sptDelete t) n ↔ sptDomain t n ∧ n ∉ ks := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
      simp only [List.foldr_cons, ih, sptDomain_del, List.mem_cons, not_or]
      constructor <;> intro h <;> exact ⟨h.2.1, h.1, h.2.2⟩

/-- `Nodup` is preserved by a map that is injective on the list. -/
theorem nodupMapOfInjOn {α β : Type} {f : α → β} :
    ∀ {ns : List α}, ns.Nodup → (∀ a b, a ∈ ns → b ∈ ns → f a = f b → a = b) →
      (ns.map f).Nodup
  | [], _, _ => by simp
  | x :: xs, hnd, hinj => by
      rw [List.nodup_cons] at hnd
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, nodupMapOfInjOn hnd.2 fun a b ha hb h =>
        hinj a b (List.mem_cons_of_mem x ha) (List.mem_cons_of_mem x hb) h⟩
      intro hfx
      obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hfx
      have hxy : x = y := hinj x y (by simp) (List.mem_cons_of_mem x hy) hfy.symm
      exact hnd.1 (hxy.symm ▸ hy)

/-- Length of the value list produced by a successful `getVars`. -/
theorem getVarsLength {width : Nat} [NeZero width] {C F : Type} :
    ∀ (ls : List Nat) (s : WordSemStateFiniteExact width C F) (vs : List (WordLocW width)),
      WordSemStateFiniteExact.getVars ls s = some vs → vs.length = ls.length := by
  intro ls
  induction ls with
  | nil =>
      intro s vs h
      simp only [WordSemStateFiniteExact.getVars, Option.some.injEq] at h
      subst h; rfl
  | cons n ns ih =>
      intro s vs h
      simp only [WordSemStateFiniteExact.getVars] at h
      cases hv : WordSemStateFiniteExact.getVar n s with
      | none => rw [hv] at h; simp at h
      | some v =>
          cases hvs : WordSemStateFiniteExact.getVars ns s with
          | none => rw [hv, hvs] at h; simp at h
          | some vs' =>
              rw [hv, hvs] at h
              simp only [Option.some.injEq] at h
              subst h
              simp only [List.length_cons, ih s vs' hvs]

/-- `sptAlistInsert` does not change a lookup at a key outside the inserted
name list. -/
theorem sptLookup_sptAlistInsert_notMem {α : Type} (ns : List Nat) (vs : List α)
    (t : Spt α) (n : Nat) (hn : n ∉ ns) :
    sptLookup n (LoopSemStateFiniteExact.sptAlistInsert ns vs t) = sptLookup n t := by
  induction ns generalizing vs with
  | nil => simp [LoopSemStateFiniteExact.sptAlistInsert]
  | cons x xs ih =>
      cases vs with
      | nil => simp [LoopSemStateFiniteExact.sptAlistInsert]
      | cons v vs =>
          rw [LoopSemStateFiniteExact.sptAlistInsert,
            sptLookup_sptInsert_ne x n v _ (by rintro rfl; exact hn (by simp))]
          exact ih vs (by intro h; exact hn (List.mem_cons_of_mem x h))

/-- `sptAlistInsert` lookup at a member of a duplicate-free name list, with
the value list at least as long: the first-occurrence value is returned. -/
theorem sptLookup_sptAlistInsert_get? {α : Type} :
    ∀ (ns : List Nat) (vs : List α) (t : Spt α) (n : Nat),
      ns.Nodup → ns.length = vs.length → n ∈ ns →
      sptLookup n (LoopSemStateFiniteExact.sptAlistInsert ns vs t) = vs[ns.idxOf n]? := by
  intro ns
  induction ns with
  | nil => intro vs t n _ _ hn; simp at hn
  | cons x xs ih =>
      intro vs t n hnd hlen hn
      cases vs with
      | nil => simp at hlen
      | cons v vs =>
          have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
          have hlen' : xs.length = vs.length := by simpa using hlen
          rw [LoopSemStateFiniteExact.sptAlistInsert]
          by_cases hnx : n = x
          · subst hnx
            rw [sptLookup_sptInsert_same, List.idxOf_cons_self]
            rfl
          · have hnxs : n ∈ xs := by
              rcases List.mem_cons.mp hn with h | h
              · exact absurd h hnx
              · exact h
            rw [sptLookup_sptInsert_ne x n v _ hnx, ih vs t n hnd' hlen' hnxs, List.idxOf_cons]
            simp only [beq_eq_false_iff_ne.mpr (Ne.symm hnx), cond_false,
              List.getElem?_cons_succ]

/-- The first-occurrence index of a mapped element is the first-occurrence
index of the original element, when the map is injective on the list. -/
theorem idxOf_map_of_nodup_inj {f : Nat → Nat} {ns : List Nat} (hnodup : ns.Nodup)
    (hinj : ∀ a b, a ∈ ns → b ∈ ns → f a = f b → a = b) {n : Nat} (hn : n ∈ ns) :
    (ns.map f).idxOf (f n) = ns.idxOf n := by
  let i := (ns.map f).idxOf (f n)
  have hmem : f n ∈ ns.map f := List.mem_map.mpr ⟨n, hn, rfl⟩
  have hi : i < (ns.map f).length := List.idxOf_lt_length_of_mem hmem
  have hget : (ns.map f)[i] = f n := List.getElem_idxOf hi
  have hiLen : i < ns.length := by simpa [List.length_map] using hi
  have hmapget : (ns.map f)[i] = f ns[i] := List.getElem_map ..
  have heq : f ns[i] = f n := by rw [← hmapget, hget]
  have hni : ns[i] = n := hinj ns[i] n (List.getElem_mem hiLen) hn heq
  calc (ns.map f).idxOf (f n) = i := rfl
    _ = ns.idxOf ns[i] := (List.Nodup.idxOf_getElem hnodup i hiLen).symm
    _ = ns.idxOf n := by rw [hni]

/-- The `Move` post-state locals relation: inserting `ns` / `ns.map f` around
`src` / `dst` preserves the live-scoped relation, where names in `ns` are
written (`getwrites`) and live names outside `ns` are already related through
`getlive`. -/
theorem sptAlistInsertRelLive {α : Type} (f : Nat → Nat) (ns : List Nat) (vs : List α)
    (src dst : Spt α) (live getlive getwrites : Nat → Prop)
    (hnodup : ns.Nodup) (hlen : ns.length = vs.length)
    (hinj : ∀ a b, (getwrites a ∨ live a) → (getwrites b ∨ live b) → f a = f b → a = b)
    (hns : ∀ n, n ∈ ns → getwrites n)
    (hbase : ∀ n, live n → n ∉ ns → getlive n)
    (hr : strongLocalsRel f getlive src dst) :
    strongLocalsRel f live (LoopSemStateFiniteExact.sptAlistInsert ns vs src)
      (LoopSemStateFiniteExact.sptAlistInsert (ns.map f) vs dst) := by
  intro n v ⟨hnlive, hlookup⟩
  have hinjns : ∀ a b, a ∈ ns → b ∈ ns → f a = f b → a = b :=
    fun a b ha hb h => hinj a b (Or.inl (hns a ha)) (Or.inl (hns b hb)) h
  by_cases hmem : n ∈ ns
  · rw [sptLookup_sptAlistInsert_get? ns vs src n hnodup hlen hmem] at hlookup
    obtain ⟨hlt, hval⟩ := List.getElem?_eq_some_iff.mp hlookup
    have hnodupMap : (ns.map f).Nodup := nodupMapOfInjOn hnodup hinjns
    have hlenMap : (ns.map f).length = vs.length := by simpa [List.length_map] using hlen
    rw [sptLookup_sptAlistInsert_get? (ns.map f) vs dst (f n) hnodupMap hlenMap
      (List.mem_map.mpr ⟨n, hmem, rfl⟩), idxOf_map_of_nodup_inj hnodup hinjns hmem]
    exact List.getElem?_eq_some_iff.mpr ⟨hlt, hval⟩
  · rw [sptLookup_sptAlistInsert_notMem ns vs src n hmem] at hlookup
    have hglive : getlive n := hbase n hnlive hmem
    have hdst : sptLookup (f n) dst = some v := hr n v ⟨hglive, hlookup⟩
    have hnotmem : f n ∉ ns.map f := by
      intro hfc
      obtain ⟨m, hm, hfm⟩ := List.mem_map.mp hfc
      have hmn : m = n := hinj m n (Or.inl (hns m hm)) (Or.inr hnlive) hfm
      exact hmem (hmn ▸ hm)
    rw [sptLookup_sptAlistInsert_notMem (ns.map f) vs dst (f n) hnotmem]
    exact hdst

/-- HOL `evaluate_apply_colour`, `Move` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_Move {width : Nat} [NeZero width] {C F : Type} (pri : Nat)
    (moves : List (Nat × Nat)) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.move pri moves : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.move pri moves : WordLangProgHOL (BitVec width)) live lt)) st.locals cst.locals →
      applyColourPost f (.move pri moves : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour]
  simp only [colouringOk, getLive, getWrites] at hok hr
  have hnd : (moves.map Prod.fst).Nodup := by
    by_cases h : (moves.map Prod.fst).Nodup
    · exact h
    · rw [evaluate, if_neg h] at he
      exact absurd rfl he
  obtain ⟨vs, hgv⟩ : ∃ vs, WordSemStateFiniteExact.getVars (moves.map Prod.snd) st = some vs := by
    cases h : WordSemStateFiniteExact.getVars (moves.map Prod.snd) st with
    | none => rw [evaluate, if_pos hnd, h] at he; exact absurd rfl he
    | some vs => exact ⟨vs, rfl⟩
  have hns : ∀ n, n ∈ moves.map Prod.fst →
      sptDomain (numsetListInsert (moves.map Prod.fst) .ln) n :=
    fun n hn => (sptDomain_numsetIns _ _ _).mpr (Or.inr hn)
  have hinj : ∀ a b, (sptDomain (numsetListInsert (moves.map Prod.fst) .ln) a ∨
        sptDomain live a) →
      (sptDomain (numsetListInsert (moves.map Prod.fst) .ln) b ∨ sptDomain live b) →
      f a = f b → a = b :=
    fun a b ha hb h => hok.2 a b
      ((sptDomain_uni _ _ a).mpr (ha.elim Or.inl Or.inr))
      ((sptDomain_uni _ _ b).mpr (hb.elim Or.inl Or.inr)) h
  have hinjns : ∀ a b, a ∈ moves.map Prod.fst → b ∈ moves.map Prod.fst →
      f a = f b → a = b :=
    fun a b ha hb h => hinj a b (Or.inl (hns a ha)) (Or.inl (hns b hb)) h
  have hnodupC : ((moves.map Prod.fst).map f).Nodup := nodupMapOfInjOn hnd hinjns
  have hgetvsC : WordSemStateFiniteExact.getVars
      ((moves.map Prod.snd).map f) cst = some vs :=
    strongLocalsRelGetVars (moves.map Prod.snd) vs f _ st cst
      ⟨hr, fun x hx => (sptDomain_numsetIns _ _ _).mpr (Or.inr hx), hgv⟩
  have hMfst : (List.zip (moves.map (f ∘ Prod.fst)) (moves.map (f ∘ Prod.snd))).map Prod.fst
      = (moves.map Prod.fst).map f := by
    rw [List.map_fst_zip] <;> simp [List.map_map, Function.comp_def]
  have hMsnd : (List.zip (moves.map (f ∘ Prod.fst)) (moves.map (f ∘ Prod.snd))).map Prod.snd
      = (moves.map Prod.snd).map f := by
    rw [List.map_snd_zip] <;> simp [List.map_map, Function.comp_def]
  have hsrc : evaluate (.move pri moves) st =
      (none, WordSemStateFiniteExact.setVars (moves.map Prod.fst) vs st) := by
    simp only [evaluate, hnd, hgv, if_true]
  have htgt : evaluate
        (.move pri (List.zip (moves.map (f ∘ Prod.fst)) (moves.map (f ∘ Prod.snd)))) cst =
      (none, WordSemStateFiniteExact.setVars ((moves.map Prod.fst).map f) vs cst) := by
    simp only [evaluate, hMfst, hMsnd, hnodupC, hgetvsC, if_true]
  rw [hsrc, htgt]
  refine ⟨rfl, wsrLocals _ _ hs, ?_⟩
  simp only [applyColourLocals, setVars]
  have hbase : ∀ n, sptDomain live n → n ∉ moves.map Prod.fst →
      sptDomain (numsetListInsert (moves.map Prod.snd)
        ((moves.map Prod.fst).foldr sptDelete live)) n :=
    fun n hn hnm => (sptDomain_numsetIns _ _ _).mpr
      (Or.inl ((sptDomain_foldr_sptDelete _ _ _).mpr ⟨hn, hnm⟩))
  have hlen : (moves.map Prod.fst).length = vs.length := by
    have h := getVarsLength (moves.map Prod.snd) st vs hgv
    simp only [List.length_map] at h ⊢
    omega
  exact sptAlistInsertRelLive f (moves.map Prod.fst) vs st.locals cst.locals
    (sptDomain live)
    (sptDomain (numsetListInsert (moves.map Prod.snd) ((moves.map Prod.fst).foldr sptDelete live)))
    (sptDomain (numsetListInsert (moves.map Prod.fst) .ln))
    hnd hlen hinj hns hbase hr

/-- HOL `evaluate_apply_colour`, `StoreConsts` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_StoreConsts {width : Nat} [NeZero width] {C F : Type}
    (a b c d : Nat) (words : List (Bool × BitVec width)) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.storeConsts a b c d words : WordLangProgHOL (BitVec width)) live lt ∧
        wordStateEqRel st cst ∧
        strongLocalsRel f
          (sptDomain (getLive (.storeConsts a b c d words : WordLangProgHOL (BitVec width)) live lt))
          st.locals cst.locals →
      applyColourPost f (.storeConsts a b c d words : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour]
  simp only [colouringOk, getLive, getWrites] at hok hr
  rw [evaluate] at he
  cases hc : WordSemStateFiniteExact.getVar c st with
  | none => rw [hc] at he; exact absurd rfl he
  | some wc =>
    cases hd : WordSemStateFiniteExact.getVar d st with
    | none => rw [hc, hd] at he; cases wc <;> exact absurd rfl he
    | some wd =>
      cases wc with
      | loc _ _ => rw [hc, hd] at he; exact absurd rfl he
      | word ca =>
        cases wd with
        | loc _ _ => rw [hc, hd] at he; exact absurd rfl he
        | word doff =>
          have hmd : cst.mdomain = st.mdomain := by
            unfold wordStateEqRel at hs; exact hs.2.2.2.2.2.2.2.2.1
          have hmem : cst.memory = st.memory := by
            unfold wordStateEqRel at hs; exact hs.2.2.2.2.2.2.2.1
          have hca : wordSemConstAddresses ca words st.mdomain = true := by
            by_cases h : wordSemConstAddresses ca words st.mdomain = true
            · exact h
            · rw [hc, hd] at he; simp [h] at he
          have hcv := strongLocalsRelGetVar f _ st cst c (.word ca)
            ⟨hr, (sptDomain_ins _ _ _ _).mpr (Or.inl rfl), hc⟩
          have hdv := strongLocalsRelGetVar f _ st cst d (.word doff)
            ⟨hr, (sptDomain_ins _ _ _ _).mpr (Or.inr ((sptDomain_ins _ _ _ _).mpr (Or.inl rfl))), hd⟩
          have hgotW : ∀ {x : Nat}, (x = a ∨ x = b ∨ x = c ∨ x = d) →
              sptDomain (sptInsert a () (sptInsert b () (sptInsert c () (sptInsert d () (.ln : NumSet))))) x := by
            intro x hx
            rcases hx with rfl | rfl | rfl | rfl
            · exact (sptDomain_ins _ _ _ _).mpr (Or.inl rfl)
            · exact (sptDomain_ins _ _ _ _).mpr (Or.inr ((sptDomain_ins _ _ _ _).mpr (Or.inl rfl)))
            · exact (sptDomain_ins _ _ _ _).mpr (Or.inr ((sptDomain_ins _ _ _ _).mpr
                (Or.inr ((sptDomain_ins _ _ _ _).mpr (Or.inl rfl)))))
            · exact (sptDomain_ins _ _ _ _).mpr (Or.inr ((sptDomain_ins _ _ _ _).mpr
                (Or.inr ((sptDomain_ins _ _ _ _).mpr (Or.inr ((sptDomain_ins _ _ _ _).mpr (Or.inl rfl)))))))
          have hinjX : ∀ x y, (sptDomain (sptInsert a () (sptInsert b () (sptInsert c () (sptInsert d () (.ln : NumSet))))) x ∨
                sptDomain live x) →
              (sptDomain (sptInsert a () (sptInsert b () (sptInsert c () (sptInsert d () (.ln : NumSet))))) y ∨
                sptDomain live y) → f x = f y → x = y :=
            fun x y hx hy h => hok.2 x y
              ((sptDomain_uni _ _ x).mpr (hx.elim Or.inl Or.inr))
              ((sptDomain_uni _ _ y).mpr (hy.elim Or.inl Or.inr)) h
          have hsrc : evaluate (.storeConsts a b c d words) st =
              (none, WordSemStateFiniteExact.setVar c
                (.word (ca + wordSemBytesInWord * BitVec.ofNat width words.length))
                (WordSemStateFiniteExact.setVar d (.word doff)
                  (WordSemStateFiniteExact.unsetVar a (WordSemStateFiniteExact.unsetVar b
                    { st with memory := wordSemConstWrites ca doff words st.memory })))) := by
            simp only [evaluate, hc, hd, hca, not_true_eq_false, if_false]
          have htgt : evaluate (.storeConsts (f a) (f b) (f c) (f d) words) cst =
              (none, WordSemStateFiniteExact.setVar (f c)
                (.word (ca + wordSemBytesInWord * BitVec.ofNat width words.length))
                (WordSemStateFiniteExact.setVar (f d) (.word doff)
                  (WordSemStateFiniteExact.unsetVar (f a) (WordSemStateFiniteExact.unsetVar (f b)
                    { cst with memory := wordSemConstWrites ca doff words cst.memory })))) := by
            simp only [evaluate, hcv, hdv, hmd, hca, not_true_eq_false, if_false]
          rw [hsrc, htgt]
          refine ⟨rfl, ?_, ?_⟩
          · -- word_state_eq_rel
            simpa [wordStateEqRel, hmem, WordSemStateFiniteExact.setVar,
              WordSemStateFiniteExact.unsetVar] using hs
          · -- live-scoped locals relation
            simp only [applyColourLocals, WordSemStateFiniteExact.setVar,
              WordSemStateFiniteExact.unsetVar]
            apply strongLocalsRelInsert f c (sptDomain live)
            constructor
            · intro x y hx hy hxy
              exact hinjX x y
                (hx.elim (fun hxc => Or.inl (by rw [hxc]; exact hgotW (x := c) (Or.inr (Or.inr (Or.inl rfl))))) Or.inr)
                (hy.elim (fun hyc => Or.inl (by rw [hyc]; exact hgotW (x := c) (Or.inr (Or.inr (Or.inl rfl))))) Or.inr) hxy
            · apply strongLocalsRelInsert f d (fun k => sptDomain live k ∧ k ≠ c)
              constructor
              · intro x y hx hy hxy
                exact hinjX x y
                  (hx.elim (fun hxd => Or.inl (by rw [hxd]; exact hgotW (x := d) (Or.inr (Or.inr (Or.inr rfl)))))
                    (fun hxl => Or.inr hxl.1))
                  (hy.elim (fun hyd => Or.inl (by rw [hyd]; exact hgotW (x := d) (Or.inr (Or.inr (Or.inr rfl)))))
                    (fun hyl => Or.inr hyl.1)) hxy
              · intro n v ⟨hn, hlookup⟩
                have hnLive : sptDomain live n := hn.1.1
                rw [sptLookup_sptDelete, sptLookup_sptDelete] at hlookup
                by_cases hna : n = a
                · rw [if_pos hna] at hlookup; exact absurd hlookup (by simp)
                · rw [if_neg hna] at hlookup
                  by_cases hnb : n = b
                  · rw [if_pos hnb] at hlookup; exact absurd hlookup (by simp)
                  · rw [if_neg hnb] at hlookup
                    have hglive : sptDomain (sptInsert c () (sptInsert d () (sptDelete a (sptDelete b live)))) n :=
                      (sptDomain_ins _ _ _ _).mpr (Or.inr ((sptDomain_ins _ _ _ _).mpr (Or.inr
                        ((sptDomain_del _ _ _).mpr ⟨hna, (sptDomain_del _ _ _).mpr ⟨hnb, hnLive⟩⟩))))
                    have hdst : sptLookup (f n) cst.locals = some v := hr n v ⟨hglive, hlookup⟩
                    have hfna : ¬ f n = f a := fun h => hna (hinjX n a (Or.inr hnLive) (Or.inl (hgotW (Or.inl rfl))) h)
                    have hfnb : ¬ f n = f b := fun h => hnb (hinjX n b (Or.inr hnLive) (Or.inl (hgotW (Or.inr (Or.inl rfl)))) h)
                    rw [sptLookup_sptDelete, sptLookup_sptDelete, if_neg hfna, if_neg hfnb]
                    exact hdst

end Flapjack.WordAlloc
