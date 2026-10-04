import Flapjack.HolRef
import Flapjack.Compiler.Backend.WordAlloc.RemoveDead
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Compiler.Backend.WordAlloc.Proofs.StrongLocalsRel
import Flapjack.Compiler.Backend.Semantics.WordSem.Env
import Flapjack.Misc.Option
import Flapjack.Misc.Sptree.Wf

/-!
# word_alloc dead-code removal correctness

Counterpart of the dead-code removal section of `word_allocProofScript.sml`
(`live_store_rel_def` at line 3492, then `evaluate_remove_dead` and
`evaluate_remove_dead_prog`).
-/

namespace Flapjack.WordAlloc

/-- Exact HOL `live_store_rel_def` (`word_allocProofScript.sml:3492-3497`): the two
stores agree on every name outside the dead-store list. HOL `FLOOKUP` is `.lookup`
on the reviewed canonical finite-map carrier, and the two standalone maps are
recorded as bare relation-qualifier entries. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "live_store_rel_def"
  (fmap_as_finite_support_relation := [sstore, tstore])]
def liveStoreRel {α β : Type} (nlive : List α) (sstore : HolFiniteMapExact α β)
    (tstore : HolFiniteMapExact α β) : Prop :=
  ∀ n, n ∉ nlive → sstore.lookup n = tstore.lookup n

namespace RemoveDeadWitnesses

/-- Canonical imported WordSem carrier roundtrip for the dead-code removal ports. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end RemoveDeadWitnesses

/-- Word locations are inhabited, so HOL `THE` over them is defined (Flapjack
infrastructure, no HOL counterpart). -/
instance wordLocWNonempty {width : Nat} [NeZero width] : Nonempty (WordLocW width) := ⟨.word 0⟩

/-- Exact HOL `live_store_rel_less` (`word_allocProofScript.sml:3499-3506`); HOL
`set ls ⊆ set ls'` is list-membership inclusion. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "live_store_rel_less"
  (fmap_as_finite_support_relation := [st, tt])]
theorem liveStoreRelLess {α β : Type} (ls ls' : List α) (st : HolFiniteMapExact α β)
    (tt : HolFiniteMapExact α β) :
    liveStoreRel ls st tt ∧ (∀ x, x ∈ ls → x ∈ ls') → liveStoreRel ls' st tt :=
  fun ⟨h, hs⟩ n hn => h n (fun hm => hn (hs n hm))

/-- Exact HOL `live_store_rel_FLOOKUP_store` (`word_allocProofScript.sml:3508-3514`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "live_store_rel_FLOOKUP_store"
  (fmap_as_finite_support_relation := [sstore, tstore])]
theorem liveStoreRelFlookupStore {α β : Type} (ls : List α) (sstore : HolFiniteMapExact α β)
    (tstore : HolFiniteMapExact α β) (s : α) :
    liveStoreRel ls sstore tstore ∧ s ∉ ls → tstore.lookup s = sstore.lookup s :=
  fun ⟨h, hs⟩ => (h s hs).symm

/-- Exact HOL `nlive_store_def` (`word_allocProofScript.sml:3516-3527`): an expression
reads no store named in `nlive`. HOL `EVERY` over the `Op` arguments ranges over the
attached argument list. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "nlive_store_def" (words_as_type_indexed_bitvec)]
def nliveStore {width : Nat} [NeZero width] (nlive : List WordStoreHOL) :
    WordLangExpHOL (BitVec width) → Prop
  | .op _ ls => ∀ x : {e // e ∈ ls}, nliveStore nlive x.1
  | .lookup s => s ∉ nlive
  | .load e => nliveStore nlive e
  | .shift _ e1 e2 => nliveStore nlive e1 ∧ nliveStore nlive e2
  | _ => True
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i x; have := List.sizeOf_lt_of_mem x.2; omega)

/-- Exact HOL `strong_locals_rel_I_get_var` (`word_allocProofScript.sml:3529-3535`);
HOL `I` is `id` and `x INSERT live` is `fun k => k = x ∨ live k`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem strongLocalsRelIGetVar {width : Nat} [NeZero width] {C F : Type}
    (x : Nat) (live : Nat → Prop) (st : WordSemStateFiniteExact width C F)
    (t : Spt (WordLocW width)) (tstore : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (v : WordLocW width) :
    WordSemStateFiniteExact.getVar x st = some v ∧
      strongLocalsRel id (fun k => k = x ∨ live k) st.locals t →
    WordSemStateFiniteExact.getVar x { st with locals := t, store := tstore } = some v :=
  fun ⟨hv, hr⟩ => hr x v ⟨Or.inl rfl, hv⟩

/-- Exact HOL `strong_locals_rel_I_get_var'` (`word_allocProofScript.sml:3537-3543`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem strongLocalsRelIGetVar' {width : Nat} [NeZero width] {C F : Type}
    (x : Nat) (live : Nat → Prop) (st : WordSemStateFiniteExact width C F)
    (t : Spt (WordLocW width)) (v : WordLocW width) :
    WordSemStateFiniteExact.getVar x st = some v ∧
      strongLocalsRel id (fun k => k = x ∨ live k) st.locals t →
    WordSemStateFiniteExact.getVar x { st with locals := t } = some v :=
  fun ⟨hv, hr⟩ => hr x v ⟨Or.inl rfl, hv⟩

/-- Each member's domain lies in a `big_union` (Flapjack infrastructure; HOL
`domain_big_union_subset`). -/
private theorem domainBigUnionMem (sets : List (Spt Unit)) (s : Spt Unit) (hs : s ∈ sets)
    (k : Nat) (hk : sptDomain s k) : sptDomain (bigUnion sets) k := by
  induction sets with
  | nil => cases hs
  | cons x xs ih =>
      simp only [bigUnion, List.foldr_cons] at ih ⊢
      rw [sptDomain_sptUnion]
      rcases List.mem_cons.mp hs with rfl | hs
      · exact Or.inl hk
      · exact Or.inr (ih hs)

/-- `the_words` succeeds only when every entry is a word (Flapjack infrastructure;
HOL `the_words_EVERY_IS_SOME`). -/
private theorem theWordsSome {width : Nat} [NeZero width] :
    ∀ (xs : List (Option (WordLocW width))) (ws : List (BitVec width)),
      theWords xs = some ws → ∀ x, x ∈ xs → ∃ w, x = some (.word w)
  | [], _, _, x, hx => by cases hx
  | y :: ys, ws, h, x, hx => by
      simp only [theWords] at h
      split at h
      · rename_i a b hb
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨a, rfl⟩
        · exact theWordsSome ys b hb x hx
      · cases h

/-- Exact HOL `strong_locals_rel_I_word_exp` (`word_allocProofScript.sml:3545-3610`):
an expression evaluates identically in a target state whose locals agree on its
live registers and whose store agrees outside the dead stores it does not read.
HOL's free `t live nlive tstore` are the leading explicit binders. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem strongLocalsRelIWordExp {width : Nat} [NeZero width] {C F : Type}
    (t : Spt (WordLocW width)) (live : NumSet) (nlive : List WordStoreHOL)
    (tstore : HolFiniteMapExact WordStoreHOL (WordLocW width)) :
    ∀ (st : WordSemStateFiniteExact width C F) (exp : WordLangExpHOL (BitVec width))
      (res : WordLocW width),
      WordSemStateFiniteExact.wordExp st exp = some res ∧
        strongLocalsRel id (sptDomain (sptUnion (getLiveExp exp) live)) st.locals t ∧
        liveStoreRel nlive st.store tstore ∧ nliveStore nlive exp →
      WordSemStateFiniteExact.wordExp { st with locals := t, store := tstore } exp = some res
  | st, .const w, res, ⟨h, _⟩ => by simpa [WordSemStateFiniteExact.wordExp] using h
  | st, .var v, res, ⟨h, hr, _⟩ => by
      simp only [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar] at h ⊢
      have := hr v res ⟨by rw [sptDomain_sptUnion]; left; simp [getLiveExp, sptDomain,
        sptLookup_sptInsert_same], h⟩
      simpa using this
  | st, .lookup name, res, ⟨h, _, hs, hn⟩ => by
      simp only [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore] at h ⊢
      simp only [nliveStore] at hn
      rw [← hs name hn]; exact h
  | st, .load a, res, ⟨h, hr, hs, hn⟩ => by
      simp only [WordSemStateFiniteExact.wordExp] at h ⊢
      simp only [nliveStore] at hn
      cases ha : WordSemStateFiniteExact.wordExp st a with
      | none => rw [ha] at h; cases h
      | some r =>
        rw [ha] at h
        have hr' : strongLocalsRel id (sptDomain (sptUnion (getLiveExp a) live)) st.locals t := by
          simpa [getLiveExp] using hr
        rw [strongLocalsRelIWordExp t live nlive tstore st a r ⟨ha, hr', hs, hn⟩]
        cases r with
        | word w => exact h
        | loc _ _ => cases h
  | st, .op o args, res, ⟨h, hr, hs, hn⟩ => by
      simp only [WordSemStateFiniteExact.wordExp] at h ⊢
      simp only [nliveStore] at hn
      cases hw : theWords (args.attach.map fun x => WordSemStateFiniteExact.wordExp st x.1) with
      | none => rw [hw] at h; cases h
      | some ws =>
        rw [hw] at h
        have hmap : (args.attach.map fun x =>
            WordSemStateFiniteExact.wordExp { st with locals := t, store := tstore } x.1) =
            (args.attach.map fun x => WordSemStateFiniteExact.wordExp st x.1) := by
          apply List.map_congr_left
          intro ⟨e, he⟩ hmem
          have := List.sizeOf_lt_of_mem he
          obtain ⟨w, hwv⟩ := theWordsSome _ ws hw _ (List.mem_map_of_mem hmem)
          simp only at hwv ⊢
          rw [hwv]
          refine strongLocalsRelIWordExp t live nlive tstore st e (.word w) ⟨hwv, ?_, hs, hn ⟨e, he⟩⟩
          intro k v ⟨hk, hv⟩
          refine hr k v ⟨?_, hv⟩
          rw [sptDomain_sptUnion] at hk ⊢
          rcases hk with hk | hk
          · left
            simp only [getLiveExp]
            exact domainBigUnionMem _ _ (List.mem_map_of_mem he) k hk
          · exact Or.inr hk
        rw [hmap, hw]; exact h
  | st, .shift sh e1 e2, res, ⟨h, hr, hs, hn⟩ => by
      simp only [WordSemStateFiniteExact.wordExp] at h ⊢
      simp only [nliveStore] at hn
      have sub : ∀ e : WordLangExpHOL (BitVec width), (∀ k, sptDomain (getLiveExp e) k →
          sptDomain (getLiveExp (WordLangExpHOL.shift sh e1 e2)) k) →
          strongLocalsRel id (sptDomain (sptUnion (getLiveExp e) live)) st.locals t := by
        intro e he k v ⟨hk, hv⟩
        refine hr k v ⟨?_, hv⟩
        rw [sptDomain_sptUnion] at hk ⊢
        rcases hk with hk | hk
        · exact Or.inl (he k hk)
        · exact Or.inr hk
      cases h1 : WordSemStateFiniteExact.wordExp st e1 with
      | none => rw [h1] at h; simp at h
      | some r1 =>
        cases h2 : WordSemStateFiniteExact.wordExp st e2 with
        | none => rw [h1, h2] at h; cases r1 <;> simp at h
        | some r2 =>
          rw [h1, h2] at h
          rw [strongLocalsRelIWordExp t live nlive tstore st e1 r1 ⟨h1, sub e1 (fun k hk => by
              simp only [getLiveExp, sptDomain_sptUnion]; exact Or.inl hk), hs, hn.1⟩,
            strongLocalsRelIWordExp t live nlive tstore st e2 r2 ⟨h2, sub e2 (fun k hk => by
              simp only [getLiveExp, sptDomain_sptUnion]; exact Or.inr hk), hs, hn.2⟩]
          exact h
termination_by _ exp _ => sizeOf exp

/-- Exact HOL `strong_locals_rel_insert_notin` (`word_allocProofScript.sml:3612-3619`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_insert_notin"]
theorem strongLocalsRelInsertNotin {α : Type} (f : Nat → Nat) (live : Nat → Prop)
    (s t : Spt α) (n : Nat) (v : α) :
    strongLocalsRel f live s t ∧ ¬ live n → strongLocalsRel f live (sptInsert n v s) t := by
  rintro ⟨h, hn⟩ k w ⟨hk, hw⟩
  by_cases hkn : k = n
  · subst hkn; exact absurd hk hn
  · rw [sptLookup_sptInsert_ne _ _ _ _ hkn] at hw
    exact h k w ⟨hk, hw⟩

/-- Exact HOL `strong_locals_rel_I_get_vars'` (`word_allocProofScript.sml:3621-3638`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem strongLocalsRelIGetVars' {width : Nat} [NeZero width] {C F : Type} :
    ∀ (ls : List Nat) (live : Nat → Prop) (st : WordSemStateFiniteExact width C F)
      (t : Spt (WordLocW width)) (vs : List (WordLocW width)),
      (∀ x, x ∈ ls → live x) ∧ strongLocalsRel id live st.locals t ∧
        WordSemStateFiniteExact.getVars ls st = some vs →
      WordSemStateFiniteExact.getVars ls { st with locals := t } = some vs := by
  intro ls
  induction ls with
  | nil => rintro live st t vs ⟨-, -, h⟩; simpa [WordSemStateFiniteExact.getVars] using h
  | cons n ns ih =>
      rintro live st t vs ⟨hl, hr, h⟩
      cases hv : WordSemStateFiniteExact.getVar n st with
      | none => simp [WordSemStateFiniteExact.getVars, hv] at h
      | some v =>
        cases hvs : WordSemStateFiniteExact.getVars ns st with
        | none => simp [WordSemStateFiniteExact.getVars, hv, hvs] at h
        | some ws =>
          have h1 : WordSemStateFiniteExact.getVar n { st with locals := t } = some v :=
            hr n v ⟨hl n (by simp), hv⟩
          have h2 := ih live st t ws ⟨fun x hx => hl x (by simp [hx]), hr, hvs⟩
          simp [WordSemStateFiniteExact.getVars, hv, hvs] at h
          subst vs
          simp [WordSemStateFiniteExact.getVars, h1, h2]

/-- The `I`-coloured cut of one name set (Flapjack infrastructure for the two
cut lemmas). -/
private theorem cutNamesI {β γ : Type} (names : Spt γ) (sloc tloc x : Spt β)
    (hr : strongLocalsRel id (sptDomain names) sloc tloc)
    (hc : wordSemCutNames names sloc = some x) : wordSemCutNames names tloc = some x := by
  have hsub : LoopSemStateFiniteExact.sptSubsetLive names sloc := by
    by_cases hn : LoopSemStateFiniteExact.sptSubsetLive names sloc
    · exact hn
    · simp [wordSemCutNames, hn] at hc
  have hx : sptInter sloc names = x := by simpa [wordSemCutNames, hsub] using hc
  subst x
  have htsub : LoopSemStateFiniteExact.sptSubsetLive names tloc := by
    intro k hk
    obtain ⟨v, hv⟩ := (sptMem_iff_lookup k sloc).mp (hsub k hk)
    exact (sptMem_iff_lookup k tloc).mpr ⟨v, hr k v ⟨hk, hv⟩⟩
  simp only [wordSemCutNames, htsub, if_true, Option.some.injEq]
  rw [sptEqThm _ _ ⟨sptWfInter _ _, sptWfInter _ _⟩]
  intro k
  rw [sptLookup_sptInterCases, sptLookup_sptInterCases]
  cases hn : sptLookup k names with
  | none => cases sptLookup k tloc <;> cases sptLookup k sloc <;> rfl
  | some w =>
    have hk : sptDomain names k := by simp [sptDomain, hn]
    cases hs : sptLookup k sloc with
    | none =>
      exfalso
      obtain ⟨v, hv⟩ := (sptMem_iff_lookup k sloc).mp (hsub k hk)
      rw [hs] at hv; cases hv
    | some v =>
      have ht := hr k v ⟨hk, hs⟩
      simp only [id] at ht
      rw [ht]

/-- Exact HOL `strong_locals_rel_I_cut_envs` (`word_allocProofScript.sml:3640-3654`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem strongLocalsRelICutEnvs {width : Nat} [NeZero width] {C F : Type}
    (cutset : WordLangCutsetsHOL) (st : WordSemStateFiniteExact width C F)
    (t : Spt (WordLocW width)) (x : Spt (WordLocW width) × Spt (WordLocW width)) :
    strongLocalsRel id (fun k => sptDomain cutset.1 k ∨ sptDomain cutset.2 k) st.locals t ∧
      wordSemCutEnvs cutset st.locals = some x →
    wordSemCutEnvs cutset t = some x := by
  rintro ⟨hr, hc⟩
  unfold wordSemCutEnvs at hc ⊢
  cases h1 : wordSemCutNames cutset.1 st.locals with
  | none => rw [h1] at hc; cases hc
  | some e1 =>
    cases h2 : wordSemCutNames cutset.2 st.locals with
    | none => rw [h1, h2] at hc; cases hc
    | some e2 =>
      rw [h1, h2] at hc
      rw [cutNamesI _ _ _ _ (fun k v hk => hr k v ⟨Or.inl hk.1, hk.2⟩) h1,
        cutNamesI _ _ _ _ (fun k v hk => hr k v ⟨Or.inr hk.1, hk.2⟩) h2]
      exact hc

/-- Exact HOL `strong_locals_rel_I_cut_env` (`word_allocProofScript.sml:3656-3666`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem strongLocalsRelICutEnv {width : Nat} [NeZero width] {C F : Type}
    (cutset : WordLangCutsetsHOL) (st : WordSemStateFiniteExact width C F)
    (t : Spt (WordLocW width)) (x : Spt (WordLocW width)) :
    strongLocalsRel id (fun k => sptDomain cutset.1 k ∨ sptDomain cutset.2 k) st.locals t ∧
      wordSemCutEnv cutset st.locals = some x →
    wordSemCutEnv cutset t = some x := by
  rintro ⟨hr, hc⟩
  unfold wordSemCutEnv at hc ⊢
  cases h : wordSemCutEnvs cutset st.locals with
  | none => rw [h] at hc; cases hc
  | some p =>
    rw [h] at hc
    rw [strongLocalsRelICutEnvs cutset st t p ⟨hr, h⟩]
    exact hc

/-- Exact HOL `get_vars_eq` (`word_allocProofScript.sml:3668-3674`); HOL `THE` is the
tagged `holThe`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getVarsEq {width : Nat} [NeZero width] {C F : Type} :
    ∀ (ls : List Nat) (st : WordSemStateFiniteExact width C F),
      (∀ x, x ∈ ls → sptDomain st.locals x) →
      ∃ z, WordSemStateFiniteExact.getVars ls st = some z ∧
        z = ls.map (fun x => holThe (sptLookup x st.locals)) := by
  intro ls st
  induction ls with
  | nil => intro _; exact ⟨[], rfl, rfl⟩
  | cons n ns ih =>
      intro h
      obtain ⟨z, hz, rfl⟩ := ih (fun x hx => h x (by simp [hx]))
      obtain ⟨v, hv⟩ := (sptMem_iff_lookup n st.locals).mp (h n (by simp))
      refine ⟨v :: ns.map (fun x => holThe (sptLookup x st.locals)), ?_, ?_⟩
      · simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, hv, hz]
      · simp [hv, holThe]

/-- Exact HOL `get_vars_exists` (`word_allocProofScript.sml:3676-3683`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getVarsExists {width : Nat} [NeZero width] {C F : Type}
    (st : WordSemStateFiniteExact width C F) :
    ∀ ls : List Nat,
      (∃ z, WordSemStateFiniteExact.getVars ls st = some z) ↔
        (∀ x, x ∈ ls → sptDomain st.locals x) := by
  intro ls
  induction ls with
  | nil => simp [WordSemStateFiniteExact.getVars]
  | cons n ns ih =>
      cases hv : sptLookup n st.locals with
      | none =>
        simp only [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, hv]
        constructor
        · rintro ⟨z, hz⟩; cases hz
        · intro h; have := h n (by simp); simp [sptDomain, hv] at this
      | some v =>
        simp only [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, hv]
        constructor
        · rintro ⟨z, hz⟩
          cases hvs : WordSemStateFiniteExact.getVars ns st with
          | none => rw [hvs] at hz; cases hz
          | some ws =>
            have := ih.mp ⟨ws, hvs⟩
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · simp [sptDomain, hv]
            · exact this x hx
        · intro h
          obtain ⟨ws, hws⟩ := ih.mpr (fun x hx => h x (by simp [hx]))
          exact ⟨v :: ws, by rw [hws]⟩

/-- Exact HOL `strong_locals_rel_I_insert_insert` (`word_allocProofScript.sml:3685-3692`);
HOL `live DELETE p` is `fun k => live k ∧ k ≠ p`. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_I_insert_insert"]
theorem strongLocalsRelIInsertInsert {α : Type} (live : Nat → Prop) (p : Nat) (A B : Spt α)
    (v v' : α) :
    strongLocalsRel id (fun k => live k ∧ k ≠ p) A B ∧ v = v' →
    strongLocalsRel id live (sptInsert p v A) (sptInsert p v' B) := by
  rintro ⟨h, rfl⟩ k w ⟨hk, hw⟩
  by_cases hkp : k = p
  · subst hkp
    rw [sptLookup_sptInsert_same] at hw
    simp only [id]; rw [sptLookup_sptInsert_same, hw]
  · rw [sptLookup_sptInsert_ne _ _ _ _ hkp] at hw
    simp only [id]; rw [sptLookup_sptInsert_ne _ _ _ _ hkp]
    exact h k w ⟨⟨hk, hkp⟩, hw⟩

/-- Exact HOL `st_eq` (`word_allocProofScript.sml:3694-3700`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stEq {width : Nat} [NeZero width] {C F : Type} (rst : WordSemStateFiniteExact width C F)
    (t t' : Spt (WordLocW width)) (tstore tstore' : HolFiniteMapExact WordStoreHOL (WordLocW width)) :
    { rst with locals := t, store := tstore } = { rst with locals := t', store := tstore' } ↔
      t = t' ∧ tstore = tstore' := by
  constructor
  · intro h
    exact ⟨congrArg WordSemStateFiniteExact.locals h, congrArg WordSemStateFiniteExact.store h⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- Exact HOL `live_store_rel_NIL` (`word_allocProofScript.sml:3702-3708`): with no dead
stores the relation is equality (HOL `fmap_eq_flookup`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "live_store_rel_NIL"
  (fmap_as_finite_support_relation := [sstore, tstore])]
theorem liveStoreRelNil {α β : Type} (sstore : HolFiniteMapExact α β)
    (tstore : HolFiniteMapExact α β) :
    liveStoreRel [] sstore tstore ↔ sstore = tstore := by
  constructor
  · intro h
    cases sstore with
    | mk l1 f1 =>
      cases tstore with
      | mk l2 f2 =>
        have : l1 = l2 := funext fun n => h n (by simp)
        subst this; rfl
  · rintro rfl n _; rfl

/-- Exact HOL `live_store_rel_refl` (`word_allocProofScript.sml:3710-3714`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "live_store_rel_refl"
  (fmap_as_finite_support_relation := [sstore])]
theorem liveStoreRelRefl {α β : Type} (ls : List α) (sstore : HolFiniteMapExact α β) :
    liveStoreRel ls sstore sstore :=
  fun _ _ => rfl

/-- Exact HOL `with_same_store` (`word_allocProofScript.sml:3716-3720`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem withSameStore {width : Nat} [NeZero width] {C F : Type}
    (st : WordSemStateFiniteExact width C F) : { st with store := st.store } = st := rfl

/-- Exact HOL `with_same_locals` (`word_allocProofScript.sml:3722-3726`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem withSameLocals {width : Nat} [NeZero width] {C F : Type}
    (st : WordSemStateFiniteExact width C F) : { st with locals := st.locals } = st := rfl

end Flapjack.WordAlloc
