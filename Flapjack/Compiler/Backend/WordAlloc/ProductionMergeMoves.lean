import Flapjack.RiscV.Allocator

namespace Flapjack.Compiler.Backend.WordAlloc

/-- First-match production list lookup equals the canonical map codec, on
arbitrary lists including duplicates. Flapjack-only representation law. -/
theorem productionMergeMapLookup (entries : List (Nat × Nat)) (key : Nat) :
    lookupNatInfo key entries = sptAListLookup key entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨name,value⟩
    by_cases h : name = key
    · subst name; simp [lookupNatInfo,sptAListLookup]
    · have hk : key ≠ name := Ne.symm h
      simp [lookupNatInfo,sptAListLookup,h,hk,ih]

end Flapjack.Compiler.Backend.WordAlloc
