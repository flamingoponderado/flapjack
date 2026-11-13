module

public import Flapjack.Compiler.Backend.WordAlloc.ProductionStackOnlyCache
public import Flapjack.Compiler.Backend.WordAlloc.HeuCall
public import Flapjack.RiscV.Heuristics

@[expose] public section

namespace Flapjack.WordAlloc
open RiscV

/-! The actual self-call cache and its duplicate scan. These implementation
invariants have no independent HOL original. Cache membership is derived
from the real updates, rather than assumed for a resulting call set. -/

theorem dedupAux_member (seen : Std.TreeSet Nat) (names : List Nat) (key : Nat) :
    key ∈ natEraseDupsAux seen names ↔ key ∈ names ∧ key ∉ seen := by
  induction names generalizing seen with
  | nil => simp [natEraseDupsAux]
  | cons name rest ih =>
      by_cases present : name ∈ seen
      · have contains := Std.TreeSet.contains_iff_mem.mpr present
        simp only [natEraseDupsAux, contains, ite_true, ih, List.mem_cons]
        constructor
        · intro h; exact ⟨Or.inr h.1, h.2⟩
        · rintro ⟨equal | member, missing⟩
          · exact False.elim (missing (equal ▸ present))
          · exact ⟨member, missing⟩
      · have contains : seen.contains name = false :=
          Bool.eq_false_iff.mpr (fun h => present (Std.TreeSet.contains_iff_mem.mp h))
        simp only [natEraseDupsAux, contains, Bool.false_eq_true, ite_false,
          List.mem_cons, ih, Std.TreeSet.mem_insert,
          Std.LawfulEqCmp.compare_eq_iff_eq]
        by_cases same : key = name <;> simp [same, present, eq_comm]

theorem dedupAux_nodup (seen : Std.TreeSet Nat) (names : List Nat) :
    (natEraseDupsAux seen names).Nodup := by
  induction names generalizing seen with
  | nil => simp [natEraseDupsAux]
  | cons name rest ih =>
      unfold natEraseDupsAux
      split
      · exact ih seen
      · apply List.nodup_cons.mpr
        refine ⟨?_, ih _⟩
        rw [dedupAux_member]
        simp

theorem dedupAppendAux_eq (seen : Std.TreeSet Nat) (left right : List Nat) :
    natEraseDupsAppendAux seen left right = natEraseDupsAux seen (left ++ right) := by
  induction left generalizing seen with
  | nil => simp [natEraseDupsAppendAux]
  | cons name rest ih =>
      simp only [natEraseDupsAppendAux, List.cons_append, natEraseDupsAux]
      split <;> simp only [ih]

theorem dedupAppend_member (left right : List Nat) (key : Nat) :
    key ∈ natEraseDupsAppend left right ↔ key ∈ left ∨ key ∈ right := by
  rw [natEraseDupsAppend, dedupAppendAux_eq, dedupAux_member]
  simp

theorem dedupAppend_nodup (left right : List Nat) :
    (natEraseDupsAppend left right).Nodup := by
  rw [natEraseDupsAppend, dedupAppendAux_eq]
  exact dedupAux_nodup _ _

end Flapjack.WordAlloc
