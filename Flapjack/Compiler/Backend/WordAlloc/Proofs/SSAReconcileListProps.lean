import Flapjack.Compiler.Backend.WordAlloc.SSAHelpers
import Flapjack.Misc.Sptree.ToAList
import Flapjack.Misc.Option

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Original generic reconciliation move-list rewrite. HOL payloads are
arbitrary inhabited types; THE NONE remains the opaque library value. No
lookup-success/domain/distinctness premise is added. Nonempty alpha renders
HOL type inhabitance; DecidableEq alpha supplies lawful classical equality
for filtering, available for any type, not an added BEq law. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_reconcile_moves_eq"]
theorem ssaReconcileMovesEq {α : Type} [Nonempty α] [DecidableEq α]
    (m : Spt α) (f : Nat → α) :
    ∀ (names : List Nat),
      (((names.map fun v => match sptLookup v m with
          | none => []
          | some cv => [(f v, cv)]).flatten).filter
          (fun (a, b) => decide (a ≠ b))) =
      ((names.filter fun v => match sptLookup v m with
          | none => false
          | some cv => decide (f v ≠ cv)).map
          (fun v => (f v, holThe (sptLookup v m)))) := by
  intro names
  induction names with
  | nil => rfl
  | cons v names ih =>
      cases hlook : sptLookup v m with
      | none => simpa [hlook] using ih
      | some cv =>
          by_cases hne : f v ≠ cv
          · simpa [hlook, hne, holThe] using (congrArg (List.cons (f v, cv)) ih)
          · simpa [hlook, hne] using ih

/-- Original unconditional distinctness of filtered native name keys. The
name-set payload remains arbitrary; current/target register maps are native Nat
maps as required by option_lookup. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_reconcile_filtered_all_distinct"]
theorem ssaReconcileFilteredAllDistinct {α : Type}
    (curSSA tgtSSA : Spt Nat) (names : Spt α) :
    (((sptToAList names).map Prod.fst).filter fun v =>
      match sptLookup v curSSA with
      | none => false
      | some cv => decide (optionLookup tgtSSA v ≠ cv)).Nodup := by
  exact (sptAllDistinctMapFstToAList names).filter _

end Flapjack.Compiler.Backend.WordAlloc
