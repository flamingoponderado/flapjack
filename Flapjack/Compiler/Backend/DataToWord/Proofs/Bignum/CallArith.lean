module

public import Flapjack.Compiler.Backend.DataToWord.CallTree
public import Flapjack.Compiler.Backend.DataToWord.Variables
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.SizeValues
public import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport
public import Flapjack.Compiler.Backend.BackendProps
public import Flapjack.FiniteMap.AlistExact.Lookup
public import Flapjack.Misc.Sptree.ToAList

@[expose] public section

/-! Supporting lemmas of the bignum arithmetic call proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.BackendProps

namespace CallArithWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end CallArithWitness

/-- Association lists with the same keys define the same lookup domain. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml"
  "MAP_FST_EQ_IMP_IS_SOME_ALOOKUP"]
theorem mapFst_eq_imp_isSome_alookup {α β γ : Type} {n : α} :
    ∀ (xs : List (α × β)) (ys : List (α × γ)),
      xs.map Prod.fst = ys.map Prod.fst →
      ((holALookup xs n).isSome ↔ (holALookup ys n).isSome) := by
  classical
  intro xs
  induction xs with
  | nil =>
    intro ys keys
    cases ys with
    | nil => exact Iff.rfl
    | cons _ _ => simp at keys
  | cons x xs ih =>
    intro ys keys
    cases ys with
    | nil => simp at keys
    | cons y ys =>
      obtain ⟨xk, xv⟩ := x
      obtain ⟨yk, yv⟩ := y
      simp only [List.map_cons, List.cons.injEq] at keys
      obtain ⟨rfl, rest⟩ := keys
      by_cases eq : n = xk
      · simp [holALookup, eq]
      · simp only [holALookup, eq, if_false]
        exact ih ys rest

/-- The first adjusted cut set always contains variable zero. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "domain_adjust_sets"]
theorem domain_adjustSets {α : Type} {keptNames : Spt α} :
    sptDomain (adjustSets keptNames).1 ≠ (fun _ => False) := by
  intro empty
  have := congrFun empty 0
  simp [adjustSets, sptDomain, sptLookup] at this

private theorem isSome_sptAListLookup_iff {α : Type} (key : Nat) :
    ∀ entries : List (Nat × α),
      (sptAListLookup key entries).isSome ↔ key ∈ entries.map Prod.fst := by
  intro entries
  induction entries with
  | nil => simp [sptAListLookup]
  | cons entry entries ih =>
    obtain ⟨other, value⟩ := entry
    by_cases eq : key = other
    · simp [sptAListLookup, eq]
    · simp [sptAListLookup, eq, ih]

/-- A list with the keys of an environment listing has that environment's
domain. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "env_to_list_domain_eq"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem envToList_domain_eq {width : Nat} [NeZero width] {tw : Nat} [NeZero tw]
    {C F ε : Type} {y2 : Spt (WordLocW width)} {t : WordSemStateFiniteExact tw C F}
    {l' : List (Nat × WordLocW width)} {permute : Nat → Nat → Nat}
    {ms : List (Nat × ε)} :
    wordSemEnvToList y2 t.permute = (l', permute) ∧ l'.map Prod.fst = ms.map Prod.fst →
      sptDomain (sptFromAList ms) = sptDomain y2 := by
  rintro ⟨listing, keys⟩
  have lookups := (wordSemEnvToListLookupEquiv y2 t.permute l' permute listing).1
  rw [sptDomainFromAList, ← keys]
  funext key
  apply propext
  rw [← isSome_sptAListLookup_iff, lookups]
  rfl

/-- Sizing more roots never sizes less of the original suffix. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "size_of_LE_append"]
theorem sizeOf_le_append :
    ∀ (vs ys : List DataSem.Value) (lims : DataSem.Limits)
      (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit),
      (DataSem.sizeOfValues lims ys refs seen).1 ≤
        (DataSem.sizeOfValues lims (vs ++ ys) refs seen).1 := by
  intro vs
  induction vs with
  | nil => intro ys lims refs seen; exact Nat.le_refl _
  | cons h vs ih =>
    intro ys lims refs seen
    rw [List.cons_append, Proofs.Gc.sizeOfValues_cons]
    exact Nat.le_trans (ih ys lims refs seen) (Nat.le_add_right _ _)

/-- Explicit operation arguments only add to the sized heap. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "size_of_heap_LE_args"]
theorem sizeOfHeap_le_args {C F : Type} :
    ∀ (vs : List DataSem.Value) (s : DataSem.State C F),
      DataSem.sizeOfHeap s ≤ DataSem.sizeOfHeapArgs vs s := by
  intro vs s
  exact sizeOf_le_append vs _ s.limits s.refs .ln

/-- Every association found by lookup satisfies a property of every entry. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "EVERY_IMP_ALOOKUP"]
theorem every_imp_alookup {α β : Type} :
    ∀ (xs : List (α × β)) (P : α × β → Prop),
      (∀ entry ∈ xs, P entry) → ∀ (x : α) (y : β), holALookup xs x = some y → P (x, y) := by
  classical
  intro xs
  induction xs with
  | nil => intro P _ x y found; simp [holALookup] at found
  | cons entry xs ih =>
    intro P every x y found
    obtain ⟨key, value⟩ := entry
    by_cases eq : x = key
    · subst eq
      simp only [holALookup, if_true, Option.some.injEq] at found
      subst found
      exact every _ List.mem_cons_self
    · simp only [holALookup, eq, if_false] at found
      exact ih P (fun e mem => every e (List.mem_cons_of_mem _ mem)) x y found

/-- A structurally smaller call tree has no larger maximum stack depth. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml"
  "structure_le_IMP_option_le"]
theorem structureLe_imp_optionLe :
    ∀ (l : Spt Nat) (x y : WordDepth.CallTree),
      structureLe x y → optionLe (WordDepth.maxDepth l x) (WordDepth.maxDepth l y) := by
  intro l x
  induction x with
  | leaf =>
    intro y _
    cases h : WordDepth.maxDepth l y <;> simp [WordDepth.maxDepth, optionLe]
  | unknown =>
    intro y le
    cases y <;> simp_all [structureLe, WordDepth.maxDepth, optionLe]
  | const k t ih =>
    intro y le
    cases y with
    | unknown => simp [WordDepth.maxDepth, optionLe]
    | const k2 t2 =>
      obtain ⟨kle, tle⟩ := le
      have := ih t2 tle
      simp only [WordDepth.maxDepth]
      cases a : WordDepth.maxDepth l t <;> cases b : WordDepth.maxDepth l t2 <;>
        simp_all [optionLe]
      omega
    | _ => simp [structureLe] at le
  | call n t ih =>
    intro y le
    cases y with
    | unknown => simp [WordDepth.maxDepth, optionLe]
    | call m u =>
      obtain ⟨rfl, tle⟩ := le
      have := ih u tle
      simp only [WordDepth.maxDepth]
      cases sptLookup n l <;> cases a : WordDepth.maxDepth l t <;>
        cases b : WordDepth.maxDepth l u <;> simp_all [optionLe, WordDepth.optionMap₂]
    | _ => simp [structureLe] at le
  | branch t1 t2 ih1 ih2 =>
    intro y le
    cases y with
    | unknown => simp [WordDepth.maxDepth, optionLe]
    | branch u1 u2 =>
      obtain ⟨le1, le2⟩ := le
      have h1 := ih1 u1 le1
      have h2 := ih2 u2 le2
      simp only [WordDepth.maxDepth]
      cases a : WordDepth.maxDepth l t1 <;> cases b : WordDepth.maxDepth l u1 <;>
        cases c : WordDepth.maxDepth l t2 <;> cases d : WordDepth.maxDepth l u2 <;>
        simp_all [optionLe, WordDepth.optionMap₂]
      omega
    | _ => simp [structureLe] at le

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
