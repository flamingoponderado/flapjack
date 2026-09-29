import Flapjack.Pancake.CrepToLoop.ContextExact

/-!
# Crep-to-Loop exact context lookup characterization and precompute boundary

Kernel-checked guards for `productionLoopContextToExact` (bead
`flapjack-pji9.3`): its `vars`/`funcs` lookups agree with the production
first-match lists, and the `ofString`-keyed precomputed alternative is NOT a
semantics-preserving replacement outside the byte-ranged `CrepNameRanged`
fragment. The non-ranged witness uses `"€"` (U+20AC), whose low byte truncates
under `MlString.ofString`.
-/

namespace Flapjack.Test.CrepToLoopContextLookupParity

open Flapjack
open Flapjack.Basis.Pure.MlString

private def mainCtx : LoopContext Unit :=
  { vars := [(2, 7)], functions := [("main", (1, 2))], maxVar := 0,
    target := .rv32i }

private def euroCtx : LoopContext Unit :=
  { vars := [], functions := [("€", (7, 8))], maxVar := 0, target := .rv32i }

/-- `vars` lookup agrees with `lookupNatInfo` on a concrete context. -/
theorem vars_lookup_agrees :
    (productionLoopContextToExact mainCtx).vars.lookup 2 = some 7 ∧
      (productionLoopContextToExact mainCtx).vars.lookup 3 = none ∧
      lookupNatInfo 2 mainCtx.vars = some 7 ∧
      lookupNatInfo 3 mainCtx.vars = none := by
  decide +kernel

/-- `funcs` lookup agrees with the production list for byte-ranged names. -/
theorem funcs_lookup_agrees :
    (productionLoopContextToExact mainCtx).funcs.lookup (ofString "main") =
        some (1, 2) ∧
      (productionLoopContextToExact mainCtx).funcs.lookup (ofString "nope") =
        none := by
  decide +kernel

/-- The `ofString`-keyed precompute agrees with the total definition on the
    ranged fragment (via the checked `precomputedFuncsLookup_eq_of_ranged`). -/
example :
    precomputedFuncsLookup [("main", (1, 2))] (ofString "main") =
      lookupInfo (toStringOfBytes (ofString "main")) [("main", (1, 2))] :=
  precomputedFuncsLookup_eq_of_ranged [("main", (1, 2))] (ofString "main")
    (by
      intro e he
      simp only [List.mem_singleton] at he
      subst he
      simp [CrepNameRanged])
    (crepNameRanged_toStringOfBytes _)

/-- Negative non-ranged witness: the total definition finds no match for the
    truncated `"€"` query, while the `ofString`-keyed precompute does. This
    shows precompute is not a semantics-preserving replacement in general. -/
theorem precompute_not_semantics_preserving :
    (productionLoopContextToExact euroCtx).funcs.lookup (ofString "€") = none ∧
      precomputedFuncsLookup [("€", (7, 8))] (ofString "€") = some (7, 8) := by
  decide +kernel

#guard (productionLoopContextToExact mainCtx).vars.lookup 2 = some 7
#guard (productionLoopContextToExact mainCtx).vars.lookup 3 = none
#guard (productionLoopContextToExact mainCtx).funcs.lookup (ofString "main") =
  some (1, 2)
#guard (productionLoopContextToExact mainCtx).funcs.lookup (ofString "nope") = none
#guard (productionLoopContextToExact euroCtx).funcs.lookup (ofString "€") = none
#guard precomputedFuncsLookup [("€", (7, 8))] (ofString "€") = some (7, 8)

def runChecks : IO Bool := do
  let ok := true
  IO.println
    "PASS Crep-to-Loop exact context lookup characterization and precompute boundary"
  return ok

end Flapjack.Test.CrepToLoopContextLookupParity
