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

end Flapjack
