import Flapjack.RiscV.CakeSsaSetup
import Flapjack.Compiler.Backend.WordAlloc.SSASetup

/-!
# Executed SSA setup against the reviewed native `setup_ssa`

The executed allocator renames formals with the list-state `wordSsaFreshList`
(`WordSsaState`), while the reviewed native `list_next_var_rename`/`setup_ssa`
(`Flapjack/Compiler/Backend/WordAlloc/SSASetup.lean`) thread an `num_map`.
This module proves the two agree on everything the native definition returns:
the renamed names, the next fresh counter and every key lookup of the map, for
any starting state whose lookups agree with the starting map. Flapjack API
correspondence, with no separate HOL original.

The list state's *order* is not determined by the map: downstream branch
reconciliation enumerates `wordSsaKeys`, so replacing only the setup carrier
would not preserve executed output. Routing the executed pass through the native
`num_map` state therefore belongs to the whole `full_ssa_cc_trans` migration.
-/

namespace Flapjack.RiscV.CakeRegAlloc

open Flapjack Flapjack.Compiler.Backend.WordAlloc

private theorem lookupNatInfo_filter_ne (k name : Nat) :
    ∀ (C : NatInfoMap Nat),
      lookupNatInfo k (C.filter (fun entry => entry.1 != name)) =
        if k = name then none else lookupNatInfo k C
  | [] => by simp [lookupNatInfo]
  | (c, v) :: C => by
      by_cases hc : c = name
      · subst hc
        have ih := lookupNatInfo_filter_ne k c C
        simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, if_false]
        rw [ih]
        by_cases hk : k = c
        · simp [hk]
        · simp [hk, lookupNatInfo, Ne.symm hk]
      · have ih := lookupNatInfo_filter_ne k name C
        have hne : (c != name) = true := by simpa using hc
        simp only [List.filter_cons, hne, if_true, lookupNatInfo]
        rw [ih]
        by_cases hk : k = name
        · subst hk
          have : (c == k) = false := by simpa using hc
          simp [this]
        · simp [hk]

/-- The executed fresh-name step and native `next_var_rename` keep agreeing
lookups. -/
private theorem lookup_fresh (k name next : Nat) (C : NatInfoMap Nat) (s : Spt Nat)
    (h : ∀ k, lookupNatInfo k C = sptLookup k s) :
    lookupNatInfo k ((name, next) :: C.filter (fun entry => entry.1 != name)) =
      sptLookup k (sptInsert name next s) := by
  by_cases hk : k = name
  · subst hk
    simp [lookupNatInfo, sptLookup_sptInsert_same]
  · have hne : (name == k) = false := by simpa using Ne.symm hk
    simp only [lookupNatInfo, hne, Bool.false_eq_true, if_false]
    rw [lookupNatInfo_filter_ne, if_neg hk, h, sptLookup_sptInsert_ne name k next s hk]

/-- Flapjack API correspondence: `wordSsaFreshList` and the reviewed
`listNextVarRename` return the same names and next counter, and keep agreeing
key lookups, from any agreeing start. -/
theorem wordSsaFreshList_listNextVarRename :
    ∀ (names : List Nat) (C : NatInfoMap Nat) (s : Spt Nat) (next : Nat),
      (∀ k, lookupNatInfo k C = sptLookup k s) →
      let r := wordSsaFreshList { current := C, next := next } names
      let q := listNextVarRename names s next
      r.2 = q.1 ∧ r.1.next = q.2.2 ∧ ∀ k, lookupNatInfo k r.1.current = sptLookup k q.2.1 := by
  intro names
  induction names with
  | nil =>
      intro C s next h
      simp only [wordSsaFreshList, listNextVarRename]
      exact ⟨trivial, trivial, h⟩
  | cons name names ih =>
      intro C s next h
      have h' := fun k => lookup_fresh k name next C s h
      obtain ⟨h1, h2, h3⟩ := ih _ (sptInsert name next s) (next + 4) h'
      simp only [wordSsaFreshList, wordSsaFresh, listNextVarRename, nextVarRename] at h1 h2 h3 ⊢
      exact ⟨by rw [h1], h2, h3⟩

/-- The executed `cakeSetupSsa` agrees with the reviewed native `setup_ssa`
on the entry-move pairs, the next counter and every lookup of the renaming
map. -/
theorem cakeSetupSsa_setupSSA {α : Type} {inputWidth outputWidth : Nat}
    [NeZero inputWidth] [NeZero outputWidth]
    (count limit : Nat) (program : WordProg α)
    (hol : WordLangProgHOL (BitVec inputWidth)) :
    let r := cakeSetupSsa count limit program
    let q := (setupSSA (outputWidth := outputWidth) count limit hol)
    (wordSsaFreshList { current := [], next := limit } (cakeEvenList count)).2.zip
        (cakeEvenList count) =
      (listNextVarRename (evenList count) .ln limit).1.zip (evenList count) ∧
    r.2.2 = q.2.2 ∧ ∀ k, lookupNatInfo k r.2.1.current = sptLookup k q.2.1 := by
  have he : cakeEvenList count = evenList count := rfl
  have h := wordSsaFreshList_listNextVarRename (cakeEvenList count) [] .ln limit
    (fun k => by simp [lookupNatInfo, sptLookup])
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, he]
  · simpa [cakeSetupSsa, setupSSA, he] using h2
  · simpa [cakeSetupSsa, setupSSA, he] using h3

end Flapjack.RiscV.CakeRegAlloc
