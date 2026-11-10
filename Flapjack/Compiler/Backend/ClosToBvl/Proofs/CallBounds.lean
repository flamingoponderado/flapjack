module

public import Flapjack.Compiler.Backend.ClosToBvl.Config
public import Flapjack.Compiler.Backend.ClosCall.Proofs.LabelsOriginal
public import Flapjack.Compiler.Backend.ClosCall.Proofs.LocationMembership

@[expose] public section

/-! Label bounds for optional direct-call compilation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open ClosLang ClosProps

/-- Emitted auxiliary labels are successors of input code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "ccompile_aux_subset"]
theorem ccompile_aux_subset (c : Config) (exps exps' : List Exp) (g : NumSet)
    (aux : List (Nat × Nat × Exp))
    (run : ClosCall.compile c.doCall exps = (exps', g, aux)) :
    {x | x ∈ aux.map Prod.fst} ⊆ Set.image Nat.succ {x | x ∈ codeLocations exps} := by
  cases enabled : c.doCall with
  | false =>
    simp [ClosCall.compile, enabled] at run
    obtain ⟨_, _, rfl⟩ := run
    simp
  | true =>
    have result : ClosCall.calls exps (.ln, []) = (exps', g, aux) := by
      simpa [ClosCall.compile, enabled] using run
    have bound := ClosCall.calls_addSucc_codeLocations exps (.ln, []) exps' (g, aux) result
    simpa using bound

/-- Direct-call compilation introduces no new closure code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "ccompile_locs_subset"]
theorem ccompile_locs_subset (c : Config) (exps exps' : List Exp) (g : NumSet)
    (aux : List (Nat × Nat × Exp))
    (run : ClosCall.compile c.doCall exps = (exps', g, aux)) :
    {x | x ∈ codeLocations (exps' ++ aux.map (fun t => t.2.2))} ⊆
      {x | x ∈ codeLocations exps} := by
  cases enabled : c.doCall with
  | false =>
    simp [ClosCall.compile, enabled] at run
    obtain ⟨rfl, _, rfl⟩ := run
    simp
  | true =>
    have result : ClosCall.calls exps (.ln, []) = (exps', g, aux) := by
      simpa [ClosCall.compile, enabled] using run
    intro x member
    have h := ClosCall.calls_codeLocations_mem exps (.ln, []) exps' (g, aux) result x
    have hmem : x ∈ codeLocations exps' ∨ x ∈ codeLocations (aux.map (fun t => t.2.2)) := by
      simpa [codeLocations_append] using member
    simpa [codeLocations] using h hmem

end Flapjack.Compiler.Backend.ClosToBvl
