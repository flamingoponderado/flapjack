import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMap

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Intersection retains left register payloads; the right map has an independent
payload type, as in the original inferred HOL statement. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_map_ok_inter"]
theorem ssaMapOKInter {α : Type} (next : Nat) (ssa : Spt Nat) (other : Spt α)
    (h : ssaMapOK next ssa) : ssaMapOK next (sptInter ssa other) := by
  intro x y hlookup
  rw [sptLookup_sptInterCases] at hlookup
  cases hl : sptLookup x ssa with
  | none => simp [hl] at hlookup
  | some value =>
    cases hr : sptLookup x other with
    | none => simp [hl, hr] at hlookup
    | some _ =>
      simp [hl, hr] at hlookup
      subst value
      exact h x y hl

@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_map_ok_insert"]
theorem ssaMapOKInsert (next : Nat) (ssa : Spt Nat) (x y : Nat)
    (h : ssaMapOK next ssa ∧ y < next ∧ ¬ isPhyVar y) :
    ssaMapOK next (sptInsert x y ssa) := by
  intro key value hlookup
  by_cases hk : key = x
  · subst key
    rw [sptLookup_sptInsert_same] at hlookup
    cases hlookup
    exact ⟨h.2.2, h.2.1⟩
  · rw [sptLookup_sptInsert_ne _ _ _ _ hk] at hlookup
    exact h.1 key value hlookup

end Flapjack.Compiler.Backend.WordAlloc
