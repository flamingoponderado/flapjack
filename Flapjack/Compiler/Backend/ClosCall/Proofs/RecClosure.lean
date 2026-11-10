module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLocations
public import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations
public import Mathlib.Data.Set.Disjoint

@[expose] public section

/-! Well-formed recursive closures for the direct-call simulation. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang ClosProps

/-- A recursive group has location annotations, no captured-variable
annotations, distinct nested closure locations, and no overlap between
those nested locations and the group's own range. The first component of
each function pair is polymorphic, as in the original declaration. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "recclosure_wf_def"]
def recClosureWellFormed {A : Type} (loc : Nat) (fns : List (A × Exp)) : Prop :=
  everyFnLocationSome (fns.map Prod.snd) ∧
    everyFnVarsNone (fns.map Prod.snd) ∧
    Disjoint { n | n ∈ (List.range fns.length).map (fun i => 2 * i + loc) }
      { n | n ∈ codeLocations (fns.map Prod.snd) } ∧
    (codeLocations (fns.map Prod.snd)).Nodup

end Flapjack.Compiler.Backend.ClosCall
