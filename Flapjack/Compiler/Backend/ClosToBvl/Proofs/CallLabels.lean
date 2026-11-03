import Flapjack.Compiler.Backend.ClosToBvl.Incremental
import Flapjack.Compiler.Backend.ClosCall.Proofs.LabelDistinct

/-! Auxiliary labels at the incremental direct-call handoff. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open ClosLang ClosProps

/-- The direct-call traversal used by incremental compilation emits distinct
auxiliary labels, including when the retained set of known locations is
nonempty. This is Flapjack proof infrastructure for the incremental handoff. -/
theorem numberedCalls_auxDistinct (fuel start : Nat) (known : NumSet)
    (program : ClosSem.Program) (expressions : List ClosLang.Exp) (state : ClosCall.State)
    (run : ClosCall.callsListBounded fuel
      ((ClosNumber.ignoreTable ClosNumber.compileInc start program).2.1) (known, []) =
        some (expressions, state)) :
    (state.2.map Prod.fst).Nodup := by
  apply ClosCall.callsListBounded_labelsDistinct fuel _ (known, []) state expressions run
  · simpa [ClosNumber.ignoreTable] using
      ClosNumber.compileInc_codeLocations_nodup start program.1
  · simp [ClosCall.LabelsFresh]
  · simp

/-- Annotation preserves the labels emitted by the numbered direct-call
traversal, so the auxiliary input to closure-to-BVL lowering is distinct. -/
theorem numberedCalls_annotatedAuxDistinct (fuel start : Nat) (known : NumSet)
    (program : ClosSem.Program) (expressions : List ClosLang.Exp) (state : ClosCall.State)
    (run : ClosCall.callsListBounded fuel
      ((ClosNumber.ignoreTable ClosNumber.compileInc start program).2.1) (known, []) =
        some (expressions, state)) :
    (((ClosAnnotate.compileInc (expressions, state.2)).2).map Prod.fst).Nodup := by
  have labels := numberedCalls_auxDistinct fuel start known program expressions state run
  simpa [ClosAnnotate.compileInc, ClosAnnotate.compile, List.map_map, Function.comp_def] using labels

/-- A successful full incremental compilation with known-function conversion
disabled passes distinct direct-call auxiliary labels to annotation. -/
theorem compileIncFuel_directCall_auxDistinct (fuel : Nat) (config : Config)
    (program : ClosSem.Program) (output : Config × List (Nat × Nat × Bvl.Exp))
    (enabled : config.doCall = true) (noKnown : config.knownConf = none)
    (run : compileIncFuel? fuel config program = some output) :
    ∃ prepared expressions state,
      prepareIncMtiFuel? fuel config program = some prepared ∧
      ClosCall.callsListBounded fuel
        ((ClosNumber.ignoreTable ClosNumber.compileInc config.nextLoc prepared).2.1)
        (config.callState.1, []) = some (expressions, state) ∧
      (((ClosAnnotate.compileInc (expressions, state.2)).2).map Prod.fst).Nodup := by
  simp only [compileIncFuel?, ClosCall.compileIncFuel?, noKnown, ClosKnown.compileIncFuel, Pure.pure, Bind.bind,
    Option.bind_eq_some_iff, enabled, ↓reduceIte, Option.some.injEq] at run
  obtain ⟨prepared, hp, known, hk, called, ⟨⟨expressions, state⟩, hc, _⟩, _⟩ := run
  subst known
  exact ⟨prepared, expressions, state, hp, hc,
    numberedCalls_annotatedAuxDistinct fuel config.nextLoc config.callState.1 prepared expressions state hc⟩

end Flapjack.Compiler.Backend.ClosToBvl
