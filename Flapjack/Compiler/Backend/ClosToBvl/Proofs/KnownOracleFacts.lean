module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.SyntaxOracle
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.TraversalLocationsTotal
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.TraversalSyntaxTotal
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CodeLocations
public import Flapjack.Compiler.Backend.ClosCall.Proofs.SyntaxOk
public import Flapjack.Compiler.Backend.ClosTicks.Proofs.Syntax
public import Flapjack.Compiler.Backend.ClosLetop.Proofs.Syntax
public import Flapjack.Compiler.Backend.ClosFvs.Proofs.Syntax

@[expose] public section

/-! Annotation invariants for the known-function state oracle. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open ClosLang ClosProps BackendProps ClosKnown
local instance : Nonempty ClosKnown.Config := ⟨ClosKnown.defaultConfig 0⟩

/-- The known-function oracle preserves absent variable annotations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "every_Fn_vs_NONE_known_co"]
theorem everyFnVarsNone_knownCo {α : Type}
    (f : Nat → (Spt ValApprox × α) × ClosSem.Program) (n : Nat) (conf : Option ClosKnown.Config) :
    (everyFnVarsNone (f n).2.1 ∧ globalsApproxVarsNone (f n).1.1 →
      everyFnVarsNone (ClosKnown.knownCo conf f n).2.1) ∧
    (everyFnVarsNone ((f n).2.2.map (fun p => p.2.2)) →
      everyFnVarsNone ((ClosKnown.knownCo conf f n).2.2.map (fun p => p.2.2))) := by
  cases conf with
  | none => simp [ClosKnown.knownCo, stateCo]; tauto
  | some c =>
    have preserve (h : everyFnVarsNone (f n).2.1 ∧ globalsApproxVarsNone (f n).1.1) :=
      TraversalSyntax.knownEveryFnVarsNone (resetInlineFactor c)
        (ClosFvs.compile (f n).2.1) [] (f n).1.1
        ⟨by simpa [ClosFvs.compile, ClosFvs.removeList_varsNone] using h.1, by simp, h.2⟩
    simp only [ClosKnown.knownCo, Function.comp_apply, pureCo, stateCo,
      ClosFvs.compileIncSource_eq, ClosFvs.compileInc, ClosKnown.compileInc, ClosTicks.compileIncSource_eq,
      ClosLetop.compileIncSource_eq, ClosTicks.compileInc, ClosLetop.compileInc]
    constructor
    · intro h
      simpa [ClosLetop.compileList_varsNone, ClosTicks.removeList_varsNone] using (preserve h).1
    · intro _
      simp [everyFnVarsNone]

/-- The known-function oracle preserves present function locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "every_Fn_SOME_known_co"]
theorem everyFnLocationSome_knownCo {α : Type}
    (f : Nat → (Spt ValApprox × α) × ClosSem.Program) (n : Nat) (conf : Option ClosKnown.Config) :
    (everyFnLocationSome (f n).2.1 ∧ globalsApproxLocations (f n).1.1 →
      everyFnLocationSome (ClosKnown.knownCo conf f n).2.1) ∧
    (everyFnLocationSome ((f n).2.2.map (fun p => p.2.2)) →
      everyFnLocationSome ((ClosKnown.knownCo conf f n).2.2.map (fun p => p.2.2))) := by
  cases conf with
  | none => simp [ClosKnown.knownCo, stateCo]; tauto
  | some c =>
    have preserve (h : everyFnLocationSome (f n).2.1 ∧ globalsApproxLocations (f n).1.1) :=
      TraversalLocations.knownEveryFnLocations (resetInlineFactor c)
        (ClosFvs.compile (f n).2.1) [] (f n).1.1
        ⟨by simpa [ClosFvs.compile, ClosFvs.removeList_locations] using h.1, by simp, h.2⟩
    simp only [ClosKnown.knownCo, Function.comp_apply, pureCo, stateCo,
      ClosFvs.compileIncSource_eq, ClosFvs.compileInc, ClosKnown.compileInc, ClosTicks.compileIncSource_eq,
      ClosLetop.compileIncSource_eq, ClosTicks.compileInc, ClosLetop.compileInc]
    constructor
    · intro h
      simpa [ClosLetop.compileList_locations, ClosTicks.removeList_locations] using (preserve h).1
    · intro _
      simp [everyFnLocationSome]

/-- Every known-function oracle state preserves both global annotation invariants. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "known_state_oracle_globals_approx"]
theorem knownStateOracle_globalsApprox {α : Type} (cfg' : ClosKnown.Config)
    (co : Nat → (Spt ValApprox × α) × ClosSem.Program) (spt : Spt ValApprox)
    (cfg : ClosKnown.Config) (exps : List ClosLang.Exp) (kExps : List (ClosLang.Exp × ValApprox))
    (h : isStateOracle (ClosKnown.compileInc cfg')
        (pureCo (ClosFvs.compileIncSource (α := List (Nat × Nat × ClosLang.Exp))
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

/-- Known-function preprocessing preserves the oracle properties needed by later passes. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "known_co_facts"]
theorem knownCo_facts {α : Type} (kc : Option ClosKnown.Config)
    (co : Nat → (Spt ValApprox × α) × ClosSem.Program) (exps : List ClosLang.Exp)
    (kc' : Option ClosKnown.Config) (exps' : List ClosLang.Exp) :
    let co2 := ClosKnown.knownCo kc co
    ClosKnown.compileSource kc exps = (kc', exps') →
    (kc.isSome →
      isStateOracle (ClosKnown.compileInc (holThe kc))
        (pureCo (ClosFvs.compileIncSource (α := List (Nat × Nat × ClosLang.Exp))
          (β := Nat × Nat × ClosLang.Exp)) ∘ co) ∧
      (co 0).1.1 = (holThe kc').valApproxSpt ∧
      everyFnVarsNone exps ∧ everyFnLocationSome exps ∧
      (∀ k, everyFnVarsNone (co k).2.1 ∧ everyFnLocationSome (co k).2.1)) →
    (oracleMonotonic (fun entry => {x | x ∈ codeLocations entry.2.1}) (· < ·)
        {x | x ∈ codeLocations exps} co →
      oracleMonotonic (fun entry => {x | x ∈ codeLocations entry.2.1}) (· < ·)
        {x | x ∈ codeLocations exps'} co2) ∧
    (∀ k, ClosCall.syntaxOk (co k).2.1 → ClosCall.syntaxOk (co2 k).2.1) ∧
    (∀ k, (co k).2.2 = [] → (co2 k).2.2 = []) ∧
    (∀ k, (∀ j, everyFnLocationSome (co j).2.1 ∧ (co j).2.2 = []) →
      everyFnLocationSome (co2 k).2.1 ∧
      everyFnLocationSome ((co2 k).2.2.map (fun entry => entry.2.2))) := by
  dsimp only
  intro compiled guarded
  rw [ClosKnown.compileSource_eq_compile] at compiled
  cases kc with
  | none =>
    simp only [ClosKnown.compile, Prod.mk.injEq] at compiled
    obtain ⟨_, rfl⟩ := compiled
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ordered
      simpa [ClosKnown.knownCo, stateCo, oracleMonotonic] using ordered
    · intro k safe
      simpa [ClosKnown.knownCo, stateCo] using safe
    · intro k empty
      simpa [ClosKnown.knownCo, stateCo] using empty
    · intro k all
      simpa [ClosKnown.knownCo, stateCo, (all k).2, everyFnLocationSome] using (all k).1
  | some c =>
    cases initial : knownListTotal c (ClosFvs.compile exps) [] .ln with
    | mk eas g =>
      have compiled' :
          (some { c with valApproxSpt := g },
            ClosLetop.compileList (ClosTicks.removeList (eas.map Prod.fst))) = (kc', exps') := by
        simpa only [ClosKnown.compile, initial] using compiled
      cases compiled'
      have guard := guarded (by simp)
      simp only [holThe] at guard
      have initialVars : everyFnVarsNone (ClosFvs.compile exps) := by
        simpa [ClosFvs.compile] using (ClosFvs.removeList_varsNone exps 0).mpr guard.2.2.1
      have initialLocations : everyFnLocationSome (ClosFvs.compile exps) := by
        simpa [ClosFvs.compile] using (ClosFvs.removeList_locations exps 0).mpr guard.2.2.2.1
      have globalSafe := knownStateOracle_globalsApprox c co g c (ClosFvs.compile exps) eas
        ⟨guard.1, guard.2.1, initial, initialVars, initialLocations, guard.2.2.2.2⟩
      have counts : ∀ k x, (codeLocations (ClosKnown.knownCo (some c) co k).2.1).count x ≤
          (codeLocations (co k).2.1).count x := by
        intro k x
        cases hk : knownListTotal (resetInlineFactor c) (ClosFvs.compile (co k).2.1) [] (co k).1.1 with
        | mk output next =>
          have bound := TraversalCodeBag.knownCodeLocationsBag (resetInlineFactor c)
            (ClosFvs.compile (co k).2.1) [] (co k).1.1 output next hk x
          simp only [ClosKnown.knownCo, Function.comp_apply, pureCo, stateCo,
            ClosTicks.compileIncSource_eq, ClosLetop.compileIncSource_eq,
            ClosFvs.compileIncSource_eq, ClosFvs.compileInc, ClosKnown.compileInc, ClosTicks.compileInc, ClosLetop.compileInc]
          change (codeLocations (ClosLetop.compileList (ClosTicks.removeList
            ((knownListTotal (resetInlineFactor c) (ClosFvs.compile (co k).2.1) [] (co k).1.1).1.map Prod.fst)))).count x ≤ _
          rw [hk]
          simpa [ClosLetop.compileList_codeLocations, ClosTicks.removeList_codeLocations,
            ClosFvs.compile, ClosFvs.removeList_codeLocations] using bound
      have outVars : ∀ k, everyFnVarsNone (ClosKnown.knownCo (some c) co k).2.1 := by
        intro k
        have input : everyFnVarsNone (ClosFvs.compile (co k).2.1) := by
          simpa [ClosFvs.compile] using (ClosFvs.removeList_varsNone (co k).2.1 0).mpr (guard.2.2.2.2 k).1
        have safe := TraversalSyntax.knownEveryFnVarsNone (resetInlineFactor c)
          (ClosFvs.compile (co k).2.1) [] (co k).1.1 ⟨input, by simp, (globalSafe k).1⟩
        simp only [ClosKnown.knownCo, Function.comp_apply, pureCo, stateCo,
          ClosTicks.compileIncSource_eq, ClosLetop.compileIncSource_eq,
          ClosFvs.compileIncSource_eq, ClosFvs.compileInc, ClosKnown.compileInc, ClosTicks.compileInc, ClosLetop.compileInc]
        change everyFnVarsNone (ClosLetop.compileList (ClosTicks.removeList
          ((knownListTotal (resetInlineFactor c) (ClosFvs.compile (co k).2.1) [] (co k).1.1).1.map Prod.fst)))
        simpa [ClosLetop.compileList_varsNone, ClosTicks.removeList_varsNone] using safe.1
      have outLocations : ∀ k, everyFnLocationSome (ClosKnown.knownCo (some c) co k).2.1 := by
        intro k
        have input : everyFnLocationSome (ClosFvs.compile (co k).2.1) := by
          simpa [ClosFvs.compile] using (ClosFvs.removeList_locations (co k).2.1 0).mpr (guard.2.2.2.2 k).2
        have safe := TraversalLocations.knownEveryFnLocations (resetInlineFactor c)
          (ClosFvs.compile (co k).2.1) [] (co k).1.1 ⟨input, by simp, (globalSafe k).2⟩
        simp only [ClosKnown.knownCo, Function.comp_apply, pureCo, stateCo,
          ClosTicks.compileIncSource_eq, ClosLetop.compileIncSource_eq,
          ClosFvs.compileIncSource_eq, ClosFvs.compileInc, ClosKnown.compileInc, ClosTicks.compileInc, ClosLetop.compileInc]
        change everyFnLocationSome (ClosLetop.compileList (ClosTicks.removeList
          ((knownListTotal (resetInlineFactor c) (ClosFvs.compile (co k).2.1) [] (co k).1.1).1.map Prod.fst)))
        simpa [ClosLetop.compileList_locations, ClosTicks.removeList_locations] using safe.1
      have outAux : ∀ k, (ClosKnown.knownCo (some c) co k).2.2 = [] := by
        intro k
        simp [ClosKnown.knownCo, pureCo, stateCo, ClosKnown.compileInc, ClosFvs.compileInc, ClosTicks.compileInc, ClosLetop.compileInc]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro ordered
        apply oracleMonotonic_subset _ _ _ _ _ _ _ ?_ ordered
        constructor
        · intro x mem
          have bound := ClosKnown.compile_codeLocationsBag (some c)
            (some { c with valApproxSpt := g }) exps
            (ClosLetop.compileList (ClosTicks.removeList (eas.map Prod.fst))) compiled x
          have positive : 0 < (codeLocations (ClosLetop.compileList (ClosTicks.removeList (eas.map Prod.fst)))).count x :=
            List.count_pos_iff.mpr mem
          exact List.count_pos_iff.mp (by omega)
        · intro k x mem
          have positive : 0 < (codeLocations (ClosKnown.knownCo (some c) co k).2.1).count x :=
            List.count_pos_iff.mpr mem
          have bound := counts k x
          exact List.count_pos_iff.mp (by omega)
      · intro k safe
        obtain ⟨_, _, nodup⟩ := safe
        refine ⟨outLocations k, outVars k, ?_⟩
        apply List.nodup_iff_count_le_one.mpr
        intro x
        exact Nat.le_trans (counts k x) (List.nodup_iff_count_le_one.mp nodup x)
      · intro k _
        exact outAux k
      · intro k _
        exact ⟨outLocations k, by simp [outAux, everyFnLocationSome]⟩

end Flapjack.Compiler.Backend.ClosToBvl
