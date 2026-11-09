module

public import Flapjack.Misc.Sptree.Enumeration
public import Flapjack.Compiler.Backend.WordAlloc.SSASetup
public import Flapjack.Compiler.Backend.WordAlloc.SSAHelpers
public import Flapjack.Compiler.Backend.WordAlloc.Proofs.KeyMaps

@[expose] public section

namespace Flapjack.Compiler.Backend.WordAlloc

/-- The cutset list codec records precisely membership, including repetitions.
Flapjack codec infrastructure rather than a separate HOL port. -/
theorem ssaCutsetLookup (names : List Nat) (key : Nat) :
    sptLookup key (sptFromAList (names.map (fun name => (name, ())))) =
      if key ∈ names then some () else none := by
  rw [sptLookup_sptFromAList]
  induction names with
  | nil => simp [sptAListLookup]
  | cons name names ih =>
    by_cases same : key = name
    · subst key; simp [sptAListLookup]
    · simp [sptAListLookup, same, ih]

end Flapjack.Compiler.Backend.WordAlloc
