module

public import Flapjack.Compiler.Backend.WordBignum.Proofs.Syntax
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Insert
public import Batteries.Data.List.Basic

@[expose] public section

/-! Simplification facts for the bignum mini-language state operations, ported
from `cakeml/compiler/backend/proofs/word_bignumProofScript.sml`. HOL's `FDOM`
of a finite map is stated here as the set of keys with a defined lookup on the
canonical carrier. -/
namespace Flapjack

/-- HOL `FDOM` for the canonical finite-map carrier: the keys with a defined
value. Flapjack helper mirroring the HOL library domain function. -/
def HolFiniteMapExact.dom {α β : Type} (map : HolFiniteMapExact α β) : Set α :=
  { key | map.lookup key ≠ none }

/-- Flapjack helper: domain membership is decidable from the value type's
`DecidableEq`, so HOL's `IN FDOM` guards can be written literally inside an
`if`. -/
instance HolFiniteMapExact.decidableMemDom {α β : Type} [DecidableEq β]
    (map : HolFiniteMapExact α β) (key : α) : Decidable (key ∈ map.dom) :=
  decidable_of_iff (map.lookup key ≠ none) Iff.rfl

/-- Flapjack helper: two canonical finite maps with the same lookup are equal.
This module's own form of `HolFiniteMapExact.ext`, renamed to avoid the
imported PanSem extensionality lemma of that name. -/
theorem HolFiniteMapExact.ext_of_lookup {α β : Type} {m n : HolFiniteMapExact α β}
    (h : ∀ k, m.lookup k = n.lookup k) : m = n := by
  cases m with
  | mk lookup₁ fs₁ =>
    cases n with
    | mk lookup₂ fs₂ =>
      simp only at h
      have hl : lookup₁ = lookup₂ := funext h
      subst lookup₁
      have hp : fs₁ = fs₂ := Subsingleton.elim _ _
      rw [hp]

/-- Flapjack helper: HOL `FAPPLY` is determined by the canonical lookup. -/
theorem holFapply_congr {α β : Type} [Nonempty β] {f g : HolFiniteMapExact α β} {x : α}
    (h : f.lookup x = g.lookup x) : holFapply f x = holFapply g x := by
  simp only [holFapply, h]

/-- Flapjack helper: domain subtraction removes exactly the given key. -/
theorem HolFiniteMapExact.dom_eraseEq {α β : Type} [DecidableEq α]
    (map : HolFiniteMapExact α β) (key : α) :
    (map.eraseEq key).dom = map.dom \ {key} := by
  ext k
  by_cases h : k = key
  · simp [HolFiniteMapExact.dom, HolFiniteMapExact.eraseEq, FDOMSUB_HOL, h]
  · simp [HolFiniteMapExact.dom, HolFiniteMapExact.eraseEq, FDOMSUB_HOL, h]

/-- Flapjack helper: an update adds its key to the domain. -/
theorem HolFiniteMapExact.dom_updateEq {α β : Type} [DecidableEq α]
    (map : HolFiniteMapExact α β) (entry : α × β) :
    (map.updateEq entry).dom = insert entry.1 map.dom := by
  ext k
  by_cases h : k = entry.1
  · simp [HolFiniteMapExact.dom, HolFiniteMapExact.updateEq, FUPDATE_HOL, h]
  · simp [HolFiniteMapExact.dom, HolFiniteMapExact.updateEq, FUPDATE_HOL, h]

/-- Flapjack helper: updating a key with its current value leaves the map
unchanged. -/
theorem HolFiniteMapExact.updateEq_eq_self {α β : Type} [DecidableEq α]
    {map : HolFiniteMapExact α β} {key : α} {value : β} (h : map.lookup key = some value) :
    map.updateEq (key, value) = map := by
  apply HolFiniteMapExact.ext_of_lookup
  intro k
  simp only [HolFiniteMapExact.updateEq, FUPDATE_HOL]
  by_cases hk : k = key
  · subst hk
    simp [h]
  · simp [hk]

/-- Flapjack helper: removing an absent key leaves the map unchanged. -/
theorem HolFiniteMapExact.eraseEq_eq_self {α β : Type} [DecidableEq α]
    {map : HolFiniteMapExact α β} {key : α} (h : map.lookup key = none) :
    map.eraseEq key = map := by
  apply HolFiniteMapExact.ext_of_lookup
  intro k
  simp only [HolFiniteMapExact.eraseEq, FDOMSUB_HOL]
  by_cases hk : k = key
  · subst hk
    simp [h]
  · simp [hk]

end Flapjack

namespace Flapjack.Compiler.Backend.WordBignum

open Flapjack

namespace MiniStateOpsWitness

/-- The mini-language state and its explicit finite-support view roundtrip,
restated locally so the state-operation lemmas in this module carry the same
canonical finite-map witness as the `Semantics` module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] :
    (∀ s : MiniStateBroad width, (MiniState.ofBroad s).toBroad = s) ∧
      (∀ s : MiniState width, MiniState.ofBroad s.toBroad = s) :=
  Flapjack.Compiler.Backend.WordBignum.holFmapAsFiniteSupportWitness

end MiniStateOpsWitness

/-- Overwriting an array with its current contents leaves the state unchanged. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "array_write_cancel"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem arrayWrite_cancel {width : Nat} [NeZero width] (n : Address) (s : MiniState width) :
    arrayWrite n (s.arrays n) s = s := by
  cases s with
  | mk regs arrays clock =>
    simp only [arrayWrite, Function.update_eq_self]

/-- Writing a register with its current value, or deleting an absent register,
leaves the state unchanged. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "reg_write_cancel"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem regWrite_cancel {width : Nat} [NeZero width] (n : Nat) (s : MiniState width) :
    (n ∈ s.regs.dom → regWrite n (some (holFapply s.regs n)) s = s) ∧
      (n ∉ s.regs.dom → regWrite n none s = s) := by
  constructor
  · intro h
    have hv : s.regs.lookup n ≠ none := by
      simpa [HolFiniteMapExact.dom] using h
    cases hlookup : s.regs.lookup n with
    | none => exact absurd hlookup hv
    | some w =>
      simp only [regWrite, holFapply, hlookup]
      rw [HolFiniteMapExact.updateEq_eq_self hlookup]
  · intro h
    have hnone : s.regs.lookup n = none := by
      simpa [HolFiniteMapExact.dom] using h
    simp only [regWrite]
    rw [HolFiniteMapExact.eraseEq_eq_self hnone]

/-- Two mini-language states are equal exactly when their clocks, register
domains, register values on the domain, and array contents agree. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "state_eq_lemma"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem stateEqLemma {width : Nat} [NeZero width] (s0 s1 : MiniState width) :
    s0 = s1 ↔ s0.clock = s1.clock ∧ s0.regs.dom = s1.regs.dom ∧
      (∀ n, n ∈ s0.regs.dom → holFapply s0.regs n = holFapply s1.regs n) ∧
      (∀ n, s0.arrays n = s1.arrays n) := by
  constructor
  · intro h
    subst h
    simp
  · intro ⟨hclock, hdom, hval, harrays⟩
    have hregs : s0.regs = s1.regs := by
      apply HolFiniteMapExact.ext_of_lookup
      intro k
      by_cases hk : s0.regs.lookup k = none
      · have hkdom : k ∉ s0.regs.dom := by
          simp [HolFiniteMapExact.dom, hk]
        have hkdom1 : k ∉ s1.regs.dom := hdom ▸ hkdom
        have hk1 : s1.regs.lookup k = none := by
          simpa [HolFiniteMapExact.dom] using hkdom1
        rw [hk, hk1]
      · have hkdom : k ∈ s0.regs.dom := by
          simpa [HolFiniteMapExact.dom] using hk
        have hvalues := hval k hkdom
        have hk1dom : k ∈ s1.regs.dom := hdom ▸ hkdom
        have hk1 : s1.regs.lookup k ≠ none := by
          simpa [HolFiniteMapExact.dom] using hk1dom
        cases h0 : s0.regs.lookup k with
        | none => exact absurd h0 hk
        | some v =>
          cases h1 : s1.regs.lookup k with
          | none => exact absurd h1 hk1
          | some w =>
            simp only [holFapply, h0, h1] at hvalues ⊢
            rw [hvalues]
    have harrays' : s0.arrays = s1.arrays := funext harrays
    cases s0 with
    | mk regs0 arrays0 clock0 =>
      cases s1 with
      | mk regs1 arrays1 clock1 =>
        simp only at hregs hclock harrays' ⊢
        rw [hregs, hclock, harrays']

/-- Overwriting the clock leaves the registers and arrays untouched. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "clock_write_simp"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem clockWrite_simp {width : Nat} [NeZero width] (n : Nat) (s : MiniState width) :
    (clockWrite n s).regs = s.regs ∧ (clockWrite n s).arrays = s.arrays ∧
      (clockWrite n s).clock = n := by
  simp [clockWrite]

/-- Decrementing the clock leaves the registers and arrays untouched. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "dec_clock_write_simp"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem decClock_write_simp {width : Nat} [NeZero width] (s : MiniState width) :
    (decClock s).regs = s.regs ∧ (decClock s).arrays = s.arrays ∧
      (decClock s).clock = s.clock - 1 := by
  simp [decClock]

/-- A register write touches only the register map. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "reg_write_simp"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem regWrite_simp {width : Nat} [NeZero width] (n : Nat) (w : BitVec width)
    (v : Option (BitVec width)) (s : MiniState width) :
    (regWrite n none s).regs = s.regs.eraseEq n ∧
      (regWrite n (some w) s).regs = s.regs.updateEq (n, w) ∧
      (regWrite n v s).arrays = s.arrays ∧ (regWrite n v s).clock = s.clock := by
  cases v <;> simp [regWrite]

/-- Lookup and domain effects of a register write. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "reg_write_simp_alt"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem regWrite_simp_alt {width : Nat} [NeZero width] (n m : Nat) (w : BitVec width)
    (s : MiniState width) :
    holFapply (regWrite n none s).regs m =
        (if n = m then
          holFapply (HolFiniteMapExact.empty : HolFiniteMapExact Nat (BitVec width)) m
        else holFapply s.regs m) ∧
      holFapply (regWrite n (some w) s).regs m =
        (if n = m then w else holFapply s.regs m) ∧
      (regWrite n none s).regs.dom = s.regs.dom \ {n} ∧
      (regWrite n (some w) s).regs.dom = insert n s.regs.dom := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [regWrite, HolFiniteMapExact.eraseEq, FDOMSUB_HOL, holFapply]
    by_cases h : n = m
    · simp [h]
    · have hm : ¬ m = n := fun hm => h hm.symm
      simp [h, hm]
  · simp only [regWrite, HolFiniteMapExact.updateEq, FUPDATE_HOL, holFapply]
    by_cases h : n = m
    · simp [h]
    · have hm : ¬ m = n := fun hm => h hm.symm
      simp [h, hm]
  · simp only [regWrite, HolFiniteMapExact.dom_eraseEq]
  · simp only [regWrite, HolFiniteMapExact.dom_updateEq]

/-- Writing an array touches only the array contents. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "array_write_simp"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem arrayWrite_simp {width : Nat} [NeZero width] (n : Address)
    (w : List (BitVec width)) (s : MiniState width) :
    (arrayWrite n w s).regs = s.regs ∧
      (arrayWrite n w s).arrays = Function.update s.arrays n w ∧
      (arrayWrite n w s).clock = s.clock := by
  simp [arrayWrite]

/-- Deleting registers leaves the clock and arrays untouched and clears exactly
the listed registers. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "delete_vars_simp"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem deleteVars_simp {width : Nat} [NeZero width] (vs : List Nat)
    (s : MiniState width) (n : Nat) :
    (deleteVars vs s).clock = s.clock ∧ (deleteVars vs s).arrays = s.arrays ∧
      (deleteVars vs s).regs.lookup n =
        (if n ∈ vs then (none : Option (BitVec width)) else s.regs.lookup n) ∧
      (n ∈ (deleteVars vs s).regs.dom ↔ if n ∈ vs then False else n ∈ s.regs.dom) := by
  induction vs generalizing s with
  | nil => simp [deleteVars]
  | cons v vs ih =>
    obtain ⟨hc, ha, hl, hd⟩ := ih s
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [deleteVars, regWrite]
      exact hc
    · simp only [deleteVars, regWrite]
      exact ha
    · simp only [deleteVars, regWrite, HolFiniteMapExact.eraseEq, FDOMSUB_HOL, hl,
        List.mem_cons]
      by_cases hnv : n = v
      · simp [hnv]
      · simp [hnv]
    · simp only [deleteVars, regWrite, HolFiniteMapExact.dom_eraseEq, Set.mem_sdiff,
        List.mem_cons]
      rw [hd]
      by_cases hnv : n = v
      · simp [hnv]
      · by_cases hmem : n ∈ vs
        · simp [hnv, hmem]
        · simp [hnv, hmem]

/-- A defined register lookup implies domain membership. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "reg_read_lemma1"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem regReadLemma1 {width : Nat} [NeZero width] (v : BitVec width) (n : Nat)
    (s : MiniState width) :
    s.regs.lookup n = some v → (n ∈ s.regs.dom ↔ True) := by
  intro h
  simp [HolFiniteMapExact.dom, h]

/-- A defined register lookup reads back its value. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "reg_read_lemma2"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem regReadLemma2 {width : Nat} [NeZero width] (v : BitVec width) (n : Nat)
    (s : MiniState width) :
    s.regs.lookup n = some v → holFapply s.regs n = v := by
  intro h
  rw [holFapply_of_lookup h]

/-- Reading an array returns its contents. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "array_read_lemma"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem arrayReadLemma {width : Nat} [NeZero width] (v : List (BitVec width))
    (n : Address) (s : MiniState width) :
    s.arrays n = v → s.arrays n = v := by
  intro h
  exact h

/-- Reading the clock returns its value. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "clock_read_lemma"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem clockReadLemma {width : Nat} [NeZero width] (s : MiniState width) (l : Nat) :
    s.clock = l → s.clock = l := by
  intro h
  exact h

/-- Copying registers leaves the clock and arrays untouched. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "copy_vars_const"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem copyVars_const {width : Nat} [NeZero width]
    (source : HolFiniteMapExact Nat (BitVec width)) (saveRegs : List Nat)
    (s2 s3 : MiniState width) :
    copyVars saveRegs source s2 = some s3 → s3.clock = s2.clock ∧ s3.arrays = s2.arrays := by
  induction saveRegs generalizing s2 s3 with
  | nil =>
    intro h
    simp only [copyVars, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  | cons n ns ih =>
    intro h
    simp only [copyVars] at h
    cases hsource : source.lookup n with
    | none => simp [hsource] at h
    | some x =>
      simp only [hsource] at h
      obtain ⟨hc, ha⟩ := ih (regWrite n (some x) s2) s3 h
      refine ⟨?_, ?_⟩
      · rw [hc]
        simp only [regWrite]
      · rw [ha]
        simp only [regWrite]

/-- Copying registers does not disturb a register that is not saved. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "copy_vars_ignore"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem copyVars_ignore {width : Nat} [NeZero width]
    (source : HolFiniteMapExact Nat (BitVec width)) (saveRegs : List Nat)
    (s2 s3 : MiniState width) (a : Nat) :
    copyVars saveRegs source s2 = some s3 → a ∉ saveRegs → a < 25 →
      (∀ n ∈ saveRegs, n < 25) → holFapply s3.regs a = holFapply s2.regs a := by
  induction saveRegs generalizing s2 s3 with
  | nil =>
    intro h _ _ _
    simp only [copyVars, Option.some.injEq] at h
    subst h
    rfl
  | cons n ns ih =>
    intro h hnot hbound hall
    simp only [List.mem_cons, not_or] at hnot
    obtain ⟨hne, hnot⟩ := hnot
    have hnbound : n < 25 := hall n (by simp)
    have hall' : ∀ m ∈ ns, m < 25 := fun m hm => hall m (by simp [hm])
    simp only [copyVars] at h
    cases hsource : source.lookup n with
    | none => simp [hsource] at h
    | some x =>
      simp only [hsource] at h
      have hlookup := ih (regWrite n (some x) s2) s3 h hnot hbound hall'
      have hreg : (regWrite n (some x) s2).regs.lookup a = s2.regs.lookup a := by
        simp only [regWrite, HolFiniteMapExact.updateEq, FUPDATE_HOL]
        simp [hne]
      have hreg' : holFapply (regWrite n (some x) s2).regs a = holFapply s2.regs a :=
        holFapply_congr hreg
      exact hlookup.trans hreg'

/-- A successful register copy supplies the values of every saved register in
the source map. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "copy_vars_IMP"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem copyVars_IMP {width : Nat} [NeZero width]
    (source : HolFiniteMapExact Nat (BitVec width)) (saveRegs : List Nat)
    (s2 s3 : MiniState width) :
    copyVars saveRegs source s2 = some s3 →
      ∃ vals : List (BitVec width),
        List.Forall₂ (fun n v => source.lookup n = some v) saveRegs vals := by
  induction saveRegs generalizing s2 s3 with
  | nil =>
    intro _
    exact ⟨[], List.Forall₂.nil⟩
  | cons n ns ih =>
    intro h
    simp only [copyVars] at h
    cases hsource : source.lookup n with
    | none => simp [hsource] at h
    | some x =>
      simp only [hsource] at h
      obtain ⟨vals, hvals⟩ := ih (regWrite n (some x) s2) s3 h
      exact ⟨x :: vals, List.Forall₂.cons hsource hvals⟩

/-- Decrementing the clock is overwriting it with the decremented value. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "dec_clock_thm"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem decClock_thm {width : Nat} [NeZero width] (s : MiniState width) :
    decClock s = clockWrite (s.clock - 1) s := by
  rfl

end Flapjack.Compiler.Backend.WordBignum
