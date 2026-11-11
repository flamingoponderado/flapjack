module

public import Flapjack.HolRef

@[expose] public section

/-! Association-list lookup from the pinned HOL alist theory. -/
namespace Flapjack

/-- HOL association-list lookup, using propositional key equality. The test
reverses HOL's equality operands, which does not change the result. -/
@[hol "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_def"]
noncomputable def holALookup {K V : Type} (entries : List (K × V)) (key : K) : Option V :=
  open Classical in
  match entries with
  | [] => none
  | (entryKey, value) :: rest => if key = entryKey then some value else holALookup rest key

/-- Lookup in an appended association list first searches the left side. -/
@[hol "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_APPEND"]
theorem holALookup_append {K V : Type} (left right : List (K × V)) (key : K) :
    holALookup (left ++ right) key =
      match holALookup left key with
      | none => holALookup right key
      | some value => some value := by
  classical
  induction left with
  | nil => simp [holALookup]
  | cons entry rest ih =>
    obtain ⟨entryKey, value⟩ := entry
    by_cases same : key = entryKey <;> simp [holALookup, same, ih]

/-- Core association-list lookup succeeds exactly at a listed key. This
Flapjack helper connects native lookup with key-domain reasoning used in the
HOL proofs; it is not a port of a theorem about HOL ALOOKUP. Native lookup
uses the BEq instance derived from the stated DecidableEq instance. -/
theorem lookup_exists_iff_mem_keys {K V : Type} [DecidableEq K]
    (entries : List (K × V)) (key : K) :
    (∃ value, entries.lookup key = some value) ↔ key ∈ entries.map Prod.fst := by
  rw [← Option.isSome_iff_exists, List.lookup_isSome_iff, List.mem_map]
  constructor
  · rintro ⟨p, mem, h⟩
    exact ⟨p, mem, (beq_iff_eq.mp h).symm⟩
  · rintro ⟨p, mem, rfl⟩
    exact ⟨p, mem, beq_self_eq_true _⟩

/-- A successful association-list lookup identifies an actual list member. -/
@[hol "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_MEM"]
theorem holALookup_member {K V : Type} (entries : List (K × V)) (key : K) (value : V)
    (found : holALookup entries key = some value) : (key, value) ∈ entries := by
  classical
  induction entries with
  | nil => simp [holALookup] at found
  | cons entry rest ih =>
    obtain ⟨entryKey, entryValue⟩ := entry
    by_cases same : key = entryKey
    · subst entryKey
      simp [holALookup] at found
      subst entryValue
      simp
    · simp [holALookup, same] at found
      exact List.mem_cons_of_mem _ (ih found)

/-- A member of an association list with distinct keys is found by lookup. -/
@[hol "HOL/src/finite_maps/alistScript.sml" "ALOOKUP_ALL_DISTINCT_MEM"]
theorem holALookup_of_distinct_member {K V : Type} (entries : List (K × V)) (key : K) (value : V)
    (h : (entries.map Prod.fst).Nodup ∧ (key, value) ∈ entries) :
    holALookup entries key = some value := by
  classical
  induction entries with
  | nil => simp at h
  | cons entry rest ih =>
    obtain ⟨entryKey, entryValue⟩ := entry
    simp only [List.map_cons, List.nodup_cons] at h
    simp only [List.mem_cons, Prod.mk.injEq] at h
    obtain ⟨⟨outside, distinct⟩, member⟩ := h
    by_cases same : key = entryKey
    · subst entryKey
      rcases member with ⟨_, rfl⟩ | member
      · simp [holALookup]
      · exact False.elim (outside (List.mem_map.mpr ⟨(key, value), member, rfl⟩))
    · rcases member with ⟨equal, _⟩ | member
      · exact (same equal).elim
      · simpa [holALookup, same] using ih ⟨distinct, member⟩


end Flapjack
