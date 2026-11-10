module

public import Flapjack.Compiler.Backend.WordAlloc.ProductionSSAStateRoute
public import Flapjack.RiscV.LocValue
public import Flapjack.RiscV.CorrectnessColour

@[expose] public section

/-!
# SSA-renaming to colouring boundary

CakeML's SSA pass gives each assignment a fresh destination, while the
colouring pass applies one fixed name map to a whole program.  These are the
same transformation for a straight-line assignment when its RHS does not
read the destination.  This module records that equation and immediately
feeds it into the executable colouring simulation.
-/

namespace Flapjack.RiscV

theorem lookupNatInfo_filter_ne (entries : NatInfoMap α) (current name : Nat)
    (hne : current ≠ name) :
    lookupNatInfo current (entries.filter (fun entry => entry.1 != name)) =
      lookupNatInfo current entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      by_cases hcurrent : entry.1 = current
      · have hentryName : entry.1 ≠ name := by
          intro heq
          exact hne (hcurrent.symm.trans heq)
        rw [show (entry :: entries).filter (fun entry => entry.1 != name) =
            entry :: entries.filter (fun entry => entry.1 != name) by
          simp [hentryName]]
        simp [lookupNatInfo, hcurrent]
      · by_cases hentry : entry.1 = name
        · have hnameCurrent : name ≠ current := Ne.symm hne
          simp [List.filter, lookupNatInfo, hentry, hnameCurrent, ih]
        · simp [lookupNatInfo, hcurrent, hentry, ih]

end Flapjack.RiscV
