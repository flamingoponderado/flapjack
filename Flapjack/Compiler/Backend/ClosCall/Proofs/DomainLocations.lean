module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.LocationMembership
public import Flapjack.Compiler.Backend.ClosCall.Proofs.StateGrowth
public import Flapjack.Compiler.Backend.ClosCall.Proofs.Wellformed
public import Flapjack.Compiler.Backend.ClosCall.Compile
public import Mathlib.Data.Set.Defs

@[expose] public section

/-! Origins of direct-call compiler state locations. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

/-- A location in a disjoint input remains fresh after compiling the other input. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "NOT_IN_domain_FST_g"]
theorem calls_preservesFreshLocation (xs ys : List Exp) (initial : State)
    (out : List Exp) (final : State) (x : Nat)
    (distinct : (codeLocations xs ++ codeLocations ys).Nodup)
    (run : calls ys initial = (out, final))
    (_well : wellFormed initial) (member : x ∈ codeLocations xs)
    (fresh : ¬ sptDomain initial.1 x) : ¬ sptDomain final.1 x := by
  intro present
  have bound := calls_domainLocations ys initial out final run present
  rcases bound with old | new
  · exact fresh old
  · exact (List.nodup_append.mp distinct).2.2 x member x new rfl

end Flapjack.Compiler.Backend.ClosCall
