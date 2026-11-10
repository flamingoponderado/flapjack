module

public import Flapjack.Compiler.Backend.ClosToBvl.Config
public import Flapjack.Compiler.Backend.ClosCall.Proofs.LabelsOriginal
public import Flapjack.Compiler.Backend.ClosCall.Proofs.LocationMembership

@[expose] public section

/-! Label bounds for optional direct-call compilation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open ClosLang ClosProps

/-- Whole-program direct-call conversion preserves function locations in the
    transformed expressions and generated auxiliary code. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "ccompile_every_Fn_SOME"]
theorem ccompile_everyFnLocationSome (es : List Exp) (doCall : Bool)
    (es' : List Exp) (g : NumSet) (aux : List (Nat × Nat × Exp))
    (h : everyFnLocationSome es ∧ ClosCall.compile doCall es = (es', g, aux)) :
    everyFnLocationSome es' ∧ everyFnLocationSome (aux.map (fun p => p.2.2)) := by
  cases doCall with
  | false =>
    simp [ClosCall.compile] at h
    obtain ⟨annotated, rfl, _, rfl⟩ := h
    simpa [everyFnLocationSome] using annotated
  | true =>
    have run : ClosCall.calls es (.ln, []) = (es', g, aux) := by
      simpa [ClosCall.compile] using h.2
    have result := ClosCall.calls_preserves_everyFnLocationSome es (.ln, []) es' (g, aux) run
    simpa [everyFnLocationSome] using result ⟨h.1, by simp [everyFnLocationSome]⟩

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
