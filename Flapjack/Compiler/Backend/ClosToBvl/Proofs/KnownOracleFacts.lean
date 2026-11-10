module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.SyntaxOracle
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.TraversalLocationsTotal
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.TraversalSyntaxTotal

@[expose] public section

/-! Annotation invariants for the known-function state oracle. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open ClosLang ClosProps BackendProps ClosKnown

/-- Every known-function oracle state preserves both global annotation invariants. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "known_state_oracle_globals_approx"]
theorem knownStateOracle_globalsApprox {α : Type} (cfg' : ClosKnown.Config)
    (co : Nat → (Spt ValApprox × α) × ClosSem.Program) (spt : Spt ValApprox)
    (cfg : ClosKnown.Config) (exps : List ClosLang.Exp) (kExps : List (ClosLang.Exp × ValApprox))
    (h : isStateOracle (ClosKnown.compileInc cfg')
        (pureCo (ClosFvs.compileInc (α := List (Nat × Nat × ClosLang.Exp))
          (β := Nat × Nat × ClosLang.Exp)) ∘ co) ∧
      (co 0).1.1 = spt ∧ knownListTotal cfg exps [] .ln = (kExps, spt) ∧
      everyFnVarsNone exps ∧ everyFnLocationSome exps ∧
      (∀ k, everyFnVarsNone (co k).2.1 ∧ everyFnLocationSome (co k).2.1)) :
    ∀ k, globalsApproxVarsNone (co k).1.1 ∧ globalsApproxLocations (co k).1.1 := by
  obtain ⟨recurrence, first, initial, vars, locations, future⟩ := h
  intro k
  induction k with
  | zero =>
    have initialVars := TraversalSyntax.knownEveryFnVarsNone cfg exps [] .ln
      ⟨vars, by simp, by simp [globalsApproxVarsNone, sptLookup]⟩
    have initialLocations := TraversalLocations.knownEveryFnLocations cfg exps [] .ln
      ⟨locations, by simp, by simp [globalsApproxLocations, sptLookup]⟩
    rw [initial] at initialVars initialLocations
    simpa [first] using And.intro initialVars.2.2 initialLocations.2.2
  | succ k ih =>
    have inputVars : everyFnVarsNone (ClosFvs.compile (co k).2.1) := by
      simpa [ClosFvs.compile] using (ClosFvs.removeList_varsNone (co k).2.1 0).mpr (future k).1
    have inputLocations : everyFnLocationSome (ClosFvs.compile (co k).2.1) := by
      simpa [ClosFvs.compile] using (ClosFvs.removeList_locations (co k).2.1 0).mpr (future k).2
    cases hk : knownListTotal (resetInlineFactor cfg') (ClosFvs.compile (co k).2.1) [] (co k).1.1 with
    | mk output next =>
      have varsStep := TraversalSyntax.knownEveryFnVarsNone (resetInlineFactor cfg')
        (ClosFvs.compile (co k).2.1) [] (co k).1.1 ⟨inputVars, by simp, ih.1⟩
      have locationsStep := TraversalLocations.knownEveryFnLocations (resetInlineFactor cfg')
        (ClosFvs.compile (co k).2.1) [] (co k).1.1 ⟨inputLocations, by simp, ih.2⟩
      rw [hk] at varsStep locationsStep
      have eq := recurrence k
      simp [pureCo, ClosFvs.compileInc, ClosKnown.compileInc, hk] at eq
      simpa [eq] using And.intro varsStep.2.2 locationsStep.2.2

end Flapjack.Compiler.Backend.ClosToBvl
