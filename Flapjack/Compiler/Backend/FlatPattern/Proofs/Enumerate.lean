module

public import Flapjack.Misc.Enumerate
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Enumerated-list properties used in the flat pattern proof. -/
namespace Flapjack.Compiler.Backend.FlatPattern

/-- An enumerated member has the corresponding offset and list element.
`Nonempty A` supplies the arbitrary out-of-bounds value of HOL's total EL;
the stated index is in bounds. HOL type variables are inhabited. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "MEM_enumerate_EL"]
theorem memEnumerateEl {A : Type} [Nonempty A] (xs : List A) (offset : Nat) (entry : Nat × A) :
    entry ∈ Flapjack.enumerate offset xs ↔
      ∃ index, index < xs.length ∧ entry = (offset + index, Flapjack.holEl index xs) := by
  induction xs generalizing offset with
  | nil => simp [Flapjack.enumerate]
  | cons x xs ih =>
    simp only [Flapjack.enumerate, List.mem_cons, List.length_cons]
    constructor
    · intro member
      rcases member with same | later
      · refine ⟨0, by simp, ?_⟩
        simpa [Flapjack.holEl, Flapjack.holHd] using same
      · obtain ⟨index, bound, same⟩ := (ih (offset + 1)).mp later
        refine ⟨index + 1, by omega, ?_⟩
        simpa [Flapjack.holEl_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using same
    · rintro ⟨index, bound, same⟩
      cases index with
      | zero =>
        left
        simpa [Flapjack.holEl, Flapjack.holHd] using same
      | succ index =>
        right
        apply (ih (offset + 1)).mpr
        refine ⟨index, by omega, ?_⟩
        simpa [Flapjack.holEl_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using same

/-- Enumerating a list produces no duplicate indexed entries. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "ALL_DISTINCT_enumerate"]
theorem allDistinctEnumerate {A : Type} (xs : List A) (offset : Nat) :
    (Flapjack.enumerate offset xs).Nodup := by
  induction xs generalizing offset with
  | nil => exact .nil
  | cons x xs ih =>
    simp only [Flapjack.enumerate]
    apply List.nodup_cons.mpr
    constructor
    · intro member
      letI : Nonempty A := ⟨x⟩
      obtain ⟨index, _, same⟩ := (memEnumerateEl xs (offset + 1) (offset, x)).mp member
      have indexEq := congrArg Prod.fst same
      change offset = offset + 1 + index at indexEq
      omega
    · exact ih (offset + 1)

end Flapjack.Compiler.Backend.FlatPattern
