module

public import Flapjack.Compiler.Backend.WordElim.Proofs.Locations
public import Flapjack.Misc.Sptree.FromList2

@[expose] public section

/-!
# Variable-list lemmas of HOL `word_elimProof`

Counterpart of `cakeml/compiler/backend/proofs/word_elimProofScript.sml:406-475`:
`ALOOKUP_ZIP_SUCCESS`, `get_vars_locals`, `get_vars_get_locals`,
`get_locals_fromList2` and `get_locals_fromList2_FRONT`.  HOL's `get_vars` is
the tagged `getVars` (`WordSem.Accessors`) and `ALOOKUP` is the reviewed
`holAlookup`.

The untagged helper `sptLookup_sptFromList2_mem` renders HOL's
`fromList2_value` (`cakeml/misc/miscScript.sml`, outside this proof script); it
has no separate HOL original in `word_elimProof`.
-/

namespace Flapjack.Compiler.Backend.WordElim

namespace WordElimVarsSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged variable lemmas of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordElimVarsSupport

/-- Flapjack-only helper: a value looked up in `fromList2` appears in the list
    (HOL's `fromList2_value`). -/
theorem sptLookup_sptFromList2_mem {width : Nat} [NeZero width] (values : List (WordLocW width))
    (key : Nat) (value : WordLocW width) :
    sptLookup key (sptFromList2 values) = some value → value ∈ values := by
  induction values using List.reverseRecOn with
  | nil =>
      intro h
      simp [sptFromList2] at h
  | append_singleton values last ih =>
      rw [sptFromList2_append_singleton] at *
      by_cases hkey : key = 2 * values.length
      · rw [hkey, sptLookup_sptInsert_same] at *
        intro h
        rw [Option.some.inj h]
        simp
      · rw [sptLookup_sptInsert_ne (2 * values.length) key last (sptFromList2 values) hkey] at *
        intro h
        exact List.mem_append_left _ (ih h)

/-- Exact HOL `ALOOKUP_ZIP_SUCCESS` (`word_elimProofScript.sml:406-415`): a
    successful lookup in a zipped association list lands in the second list.
    HOL's two premises stay two arrows; `x` and `y` keep their independent
    element types, as in the typed capture. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "ALOOKUP_ZIP_SUCCESS"]
theorem holAlookup_zip_success {α β : Type} [DecidableEq α]
    (x : List α) (y : List β) (k : α) (v : β) :
    x.length = y.length →
      holAlookup (x.zip y) k = some v → v ∈ y := by
  intro hlen halookup
  induction x generalizing y with
  | nil =>
      cases y with
      | nil => simp [holAlookup] at halookup
      | cons head tail => simp at hlen
  | cons head tail ih =>
      cases y with
      | nil => simp at hlen
      | cons headY tailY =>
          simp only [List.zip_cons_cons, holAlookup] at halookup
          split at halookup
          · rename_i hsame
            rw [Option.some.inj halookup]
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem headY (ih tailY (by simpa using hlen) halookup)

/-- Exact HOL `get_vars_locals` (`word_elimProofScript.sml:416-427`): every
    value returned by `get_vars` is in `s.locals`.  HOL's ONE conjunction
    premise is one hypothesis here. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "get_vars_locals"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVars_locals {width : Nat} [NeZero width] {C : Type} {F : Type}
    (args : List Nat) (state : WordSemStateFiniteExact width C F)
    (x : List (WordLocW width)) (y : WordLocW width) :
    (WordSemStateFiniteExact.getVars args state = some x ∧ y ∈ x) →
      ∃ n, sptLookup n state.locals = some y := by
  induction args generalizing x with
  | nil =>
      rintro ⟨hget, hmem⟩
      simp only [WordSemStateFiniteExact.getVars] at hget
      have hx : x = [] := (Option.some.inj hget).symm
      rw [hx] at hmem
      simp at hmem
  | cons head tail ih =>
      rintro ⟨hget, hmem⟩
      simp only [WordSemStateFiniteExact.getVars] at hget
      split at hget
      · simp at hget
      · rename_i value hvalue
        split at hget
        · simp at hget
        · rename_i rest hrest
          have hx : x = value :: rest := (Option.some.inj hget).symm
          rw [hx] at hmem
          rcases List.mem_cons.mp hmem with hsame | htail
          · refine ⟨head, ?_⟩
            rw [hsame]
            exact hvalue
          · exact ih rest ⟨hrest, htail⟩

/-- Exact HOL `get_vars_get_locals` (`word_elimProofScript.sml:429-436`): a
    `Loc` returned by `get_vars` names a location in `s.locals`. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "get_vars_get_locals"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVars_get_locals {width : Nat} [NeZero width] {C : Type} {F : Type}
    (args : List Nat) (state : WordSemStateFiniteExact width C F)
    (x : List (WordLocW width)) (n n1 : Nat) :
    (WordSemStateFiniteExact.getVars args state = some x ∧
      (.loc n n1 : WordLocW width) ∈ x) →
      sptMem n (getLocals state.locals) := by
  rintro ⟨hget, hmem⟩
  obtain ⟨key, hkey⟩ := getVars_locals args state x (.loc n n1) ⟨hget, hmem⟩
  exact (domainGetLocalsLookup n state.locals).mpr ⟨key, n1, hkey⟩

/-- Exact HOL `get_locals_fromList2` (`word_elimProofScript.sml:438-446`): the
    locations of the `fromList2` binding of the returned values stay inside
    `s.locals`.  HOL's three conjuncts are ONE premise in HOL's order. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "get_locals_fromList2"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getLocals_fromList2 {width : Nat} [NeZero width] {C : Type} {F : Type}
    (args : List Nat) (state : WordSemStateFiniteExact width C F)
    (x : List (WordLocW width)) (t : Spt (WordLocW width)) :
    (WordSemStateFiniteExact.getVars args state = some x ∧ x ≠ [] ∧
      t = sptFromList2 x) →
      sptDomainSet (getLocals t) ⊆ sptDomainSet (getLocals state.locals) := by
  rintro ⟨hget, _, rfl⟩
  intro location hmem
  obtain ⟨key, offset, hkey⟩ := (domainGetLocalsLookup location (sptFromList2 x)).mp hmem
  exact getVars_get_locals args state x location offset
    ⟨hget, sptLookup_sptFromList2_mem x key (.loc location offset) hkey⟩

/-- Exact HOL `get_locals_fromList2_FRONT` (`word_elimProofScript.sml:463-475`):
    the same bound for the `FRONT` of the returned values.  HOL's four
    conjuncts are ONE premise; `FRONT` is `List.dropLast`. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "get_locals_fromList2_FRONT"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getLocals_fromList2_FRONT {width : Nat} [NeZero width] {C : Type} {F : Type}
    (args : List Nat) (state : WordSemStateFiniteExact width C F)
    (x xf : List (WordLocW width)) (t : Spt (WordLocW width)) :
    (WordSemStateFiniteExact.getVars args state = some x ∧ x ≠ [] ∧
      xf = x.dropLast ∧ t = sptFromList2 xf) →
      sptDomainSet (getLocals t) ⊆ sptDomainSet (getLocals state.locals) := by
  rintro ⟨hget, hnil, rfl, rfl⟩
  obtain ⟨ys, y, rfl⟩ : ∃ ys y, x = ys ++ [y] := by
    rcases List.eq_nil_or_concat x with rfl | ⟨ys, y, rfl⟩
    · simp at hnil
    · exact ⟨ys, y, by rw [List.concat_eq_append]⟩
  rw [List.dropLast_concat]
  refine (Set.Subset.trans (by
    intro location hmem
    exact getLocals_fromList2_extension location y ys hmem)
    (getLocals_fromList2 args state (ys ++ [y]) (sptFromList2 (ys ++ [y]))
      ⟨hget, by simp, rfl⟩))

end Flapjack.Compiler.Backend.WordElim
