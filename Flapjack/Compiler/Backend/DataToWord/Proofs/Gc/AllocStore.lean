module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AllocVar

@[expose] public section

/-! The store entries preserved by a successful allocation. -/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord

namespace AllocStoreWitnesses
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end AllocStoreWitnesses

/-- A key holding a word keeps holding a word through a finite-map update list
whose entries for that key are words. Flapjack proof infrastructure. -/
private theorem fupdateList_word {width : Nat} [NeZero width]
    (key : WordStoreHOL) :
    ∀ (entries : List (WordStoreHOL × WordLocW width)) (m : FiniteMap WordStoreHOL (WordLocW width)),
      (∃ w, m key = some (.word w)) →
      (∀ e ∈ entries, e.1 = key → ∃ w, e.2 = .word w) →
      ∃ w, FUPDATE_LIST_HOL m entries key = some (.word w)
  | [], m, hm, _ => hm
  | e :: rest, m, hm, he => by
    rw [FUPDATE_LIST_HOL_cons]
    apply fupdateList_word key rest
    · simp only [FUPDATE_HOL]
      split
      · rename_i hk
        obtain ⟨w, hw⟩ := he e List.mem_cons_self hk.symm
        exact ⟨w, by rw [hw]⟩
      · exact hm
    · intro e' he' hk
      exact he e' (List.mem_cons_of_mem _ he') hk

/-- The collector's result store keeps the four heap-pointer entries as
words. Flapjack proof infrastructure. -/
private theorem wordGcFun_store_word {width : Nat} [NeZero width] (c : Config)
    {roots : List (WordLocW width)} {m : BitVec width → WordLocW width}
    {dm : BitVec width → Bool} {s : HolFiniteMapExact WordStoreHOL (WordLocW width)}
    {roots1 : List (WordLocW width)} {m1 : BitVec width → WordLocW width}
    {s1 : HolFiniteMapExact WordStoreHOL (WordLocW width)}
    (run : WordGcFunctions.wordGcFun c (roots, m, dm, s) = some (roots1, m1, s1))
    (key : WordStoreHOL)
    (hkey : key = .currHeap ∨ key = .triggerGC ∨ key = .nextFree ∨ key = .heapLength)
    (hs : ∃ w, s.lookup key = some (.word w)) :
    ∃ w, s1.lookup key = some (.word w) := by
  simp only [WordGcFunctions.wordGcFun] at run
  split at run
  · split at run
    · simp only [Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨_, _, rfl⟩ := run
      apply fupdateList_word key _ _ hs
      rcases hkey with rfl | rfl | rfl | rfl <;> simp
    · cases run
  · split at run
    · simp only [Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨_, _, rfl⟩ := run
      apply fupdateList_word key _ _ hs
      rcases hkey with rfl | rfl | rfl | rfl <;> simp
    · cases run
  · split at run
    · cases run
    · split at run
      · split at run
        · simp only [Option.some.injEq, Prod.mk.injEq] at run
          obtain ⟨_, _, rfl⟩ := run
          apply fupdateList_word key _ _ hs
          rcases hkey with rfl | rfl | rfl | rfl <;> simp
        · cases run
      · split at run
        · simp only [Option.some.injEq, Prod.mk.injEq] at run
          obtain ⟨_, _, rfl⟩ := run
          apply fupdateList_word key _ _ hs
          rcases hkey with rfl | rfl | rfl | rfl <;> simp
        · cases run

/-- Exact HOL `alloc_store` (`data_to_word_gcProofScript.sml:8195-8217`): a
successful allocation keeps the four heap-pointer store entries as words. HOL
`FLOOKUP` is `HolFiniteMapExact.lookup`; the HOL free variables are universally
quantified and the existential witnesses keep HOL's order. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "alloc_store"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem alloc_store {width : Nat} [NeZero width] {C F : Type} {k : BitVec width}
    {names : WordLangCutsetsHOL} {t s1 : WordSemStateFiniteExact width C F} {c : Config}
    {cu «end» next heap_length1 : BitVec width} :
    WordSemStateFiniteExact.alloc k names t = (none, s1) ∧
        t.gcFun = WordGcFunctions.wordGcFun c ∧
        t.store.lookup .currHeap = some (.word cu) ∧
        t.store.lookup .triggerGC = some (.word «end») ∧
        t.store.lookup .nextFree = some (.word next) ∧
        t.store.lookup .heapLength = some (.word heap_length1) →
      ∃ (end' next' heap_length1' cu' : BitVec width),
        s1.store.lookup .currHeap = some (.word cu') ∧
        s1.store.lookup .triggerGC = some (.word end') ∧
        s1.store.lookup .nextFree = some (.word next') ∧
        s1.store.lookup .heapLength = some (.word heap_length1') := by
  rintro ⟨run, gcEq, hcu, hend, hnext, hlen⟩
  have stored : ∀ key, (key = .currHeap ∨ key = .triggerGC ∨ key = .nextFree ∨
      key = .heapLength) → ∃ w, s1.store.lookup key = some (.word w) := by
    intro key hkey
    have hpre : ∃ w, t.store.lookup key = some (.word w) := by
      rcases hkey with rfl | rfl | rfl | rfl
      exacts [⟨_, hcu⟩, ⟨_, hend⟩, ⟨_, hnext⟩, ⟨_, hlen⟩]
    have hne : key ≠ .allocSize := by rcases hkey with rfl | rfl | rfl | rfl <;> decide
    simp only [WordSemStateFiniteExact.alloc] at run
    cases hcut : wordSemCutEnvs names t.locals with
    | none => simp [hcut] at run
    | some envs =>
      simp only [hcut] at run
      cases hgc : (WordSemStateFiniteExact.pushEnv envs none
          (WordSemStateFiniteExact.setStore .allocSize (.word k) t)).gc with
      | none => simp [hgc] at run
      | some g =>
        simp only [hgc] at run
        cases hpop : g.popEnv with
        | none => simp [hpop] at run
        | some p =>
          simp only [hpop] at run
          have hp : p.store = g.store := by
            unfold WordSemStateFiniteExact.popEnv at hpop
            split at hpop <;> cases hpop <;> rfl
          have hs1 : s1 = p := by
            cases hg2 : WordSemStateFiniteExact.getStore .allocSize p with
            | none => simp [hg2] at run
            | some w =>
              simp only [hg2] at run
              cases hh : WordSemStateFiniteExact.hasSpace w p with
              | none => simp [hh] at run
              | some b =>
                cases b
                · simp [hh] at run
                · simp only [hh, Prod.mk.injEq] at run
                  exact run.2.symm
          subst hs1
          have hPgc : (WordSemStateFiniteExact.pushEnv envs none
              (WordSemStateFiniteExact.setStore .allocSize (.word k) t)).gcFun = t.gcFun := rfl
          have hPst : (WordSemStateFiniteExact.pushEnv envs none
              (WordSemStateFiniteExact.setStore .allocSize (.word k) t)).store =
                t.store.updateEq (.allocSize, .word k) := rfl
          simp only [WordSemStateFiniteExact.gc, hPgc, gcEq, hPst] at hgc
          split at hgc
          · cases hgc
          · rename_i wl mm st hrun
            split at hgc
            · cases hgc
            · simp only [Option.some.injEq] at hgc
              subst hgc
              rw [hp]
              obtain ⟨w, hw⟩ := hpre
              exact wordGcFun_store_word c hrun key hkey
                ⟨w, by simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, hne, hw]⟩
  obtain ⟨w1, h1⟩ := stored .currHeap (Or.inl rfl)
  obtain ⟨w2, h2⟩ := stored .triggerGC (Or.inr (Or.inl rfl))
  obtain ⟨w3, h3⟩ := stored .nextFree (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨w4, h4⟩ := stored .heapLength (Or.inr (Or.inr (Or.inr rfl)))
  exact ⟨w2, w3, w4, w1, h1, h2, h3, h4⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
