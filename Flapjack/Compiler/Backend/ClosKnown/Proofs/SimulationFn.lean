module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.Simulation

@[expose] public section


/-! Closure-creation case of the known-function semantic simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Fn
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Closure-creation case of the original optimizer simulation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0Fn {C F : Type} (name : Basis.Pure.MlString.MlString)
    (loc : Option Nat) (selected : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp)
    (env1full : List ClosSem.Value) (s0 : State (Spt ValApprox × C) F) :
    KnownSimulationAt [.fn name loc selected arity body] env1full s0 := by
  intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
  obtain ⟨run, known, state, inputSyntax, _, _, oracle, _, _, _, _, approxRel, _, globalSafe,
    approxSafe, globals, _, sub1, _, free, envRel, _, stateOracle, envEq, noType⟩ := h
  have syntaxParts : selected = none ∧ everyFnVarsNone [body] := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using inputSyntax
  obtain ⟨selectedEq, bodySyntax⟩ := syntaxParts
  subst selected
  have maxEq : s0.maxApp = t0.maxApp := state.2.2.2.2.2.2.1
  have fv : fvMax (arity + env1.length) [body] := by
    have h := (fvMaxFn env1.length arity name loc none body).1 free
    simpa [Nat.add_comm] using h
  have approxEnvSafe : ∀ a ∈ List.replicate arity ValApprox.other ++ aenv, valApproxSgcFree a := by
    intro a member
    rcases List.mem_append.mp member with replicated | old
    · have same : a = .other := (List.mem_replicate.mp replicated).2
      subst a
      simp [valApproxSgcFree]
    · exact approxSafe a old
  cases hk : knownListTotal c [body] (List.replicate arity .other ++ aenv) g0 with
  | mk bodyEas bodyG =>
    obtain ⟨be, ba, eq⟩ := knownListTotal_single_result c body (List.replicate arity .other ++ aenv) g0 bodyG bodyEas hk
    subst bodyEas
    rw [knownListTotal_fn, hk] at known
    simp [knownSourceHead] at known
    rcases known with ⟨rfl, rfl⟩
    have bodyRel : expRel c (List.replicate arity .other ++ aenv) (nextG s0) body be := by
      refine ⟨g0, bodyG, ba, c.inlineFactor, sub1, approxEnvSafe, globalSafe, ?_⟩
      simpa using hk
    by_cases valid : arity ≤ s0.maxApp ∧ arity ≠ 0
    · simp [evaluate, valid, envEq] at run
      rcases run with ⟨rfl, rfl⟩
      have closureRel : ValueRel c (nextG s0)
          (.closure loc [] (env1 ++ xenv1) arity body) (.closure loc [] (env2 ++ xenv2) arity be) :=
        .closure loc [] [] env1 xenv1 env2 xenv2 arity body be aenv bodySyntax fv
          .nil envRel approxRel bodyRel
      refine ⟨.val [.closure loc [] (env2 ++ xenv2) arity be], t0, ?_, ?_, state, globals, stateOracle, oracle⟩
      · simp [evaluate, ← maxEq, valid]
      · exact .cons closureRel .nil
    · simp [evaluate, valid] at run
      rcases run with ⟨rfl, rfl⟩
      exact False.elim (noType rfl)

end Flapjack.Compiler.Backend.ClosKnown.Simulation.Fn
