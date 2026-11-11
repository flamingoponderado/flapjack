module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.TraversalLabels
public import Flapjack.Compiler.Backend.ClosKnown.Compile
public import Flapjack.Compiler.Backend.ClosFvs.Proofs.Labels
public import Flapjack.Compiler.Backend.ClosTicks.Proofs.Labels
public import Flapjack.Compiler.Backend.ClosLetop.Proofs.Labels

@[expose] public section

/-! Label preservation for the complete known-function pass. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang ClosProps

/-- The enabled optimizer preserves label-freedom and returns safe global approximations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "compile_no_Labels"]
theorem compileNoLabels (c : Config) (xs : List Exp)
    (res : Option Config) (ys : List Exp)
    (h : compileSource (some c) xs = (res, ys) ∧ ∀ e ∈ xs, noLabels e) :
    ∃ c1, res = some c1 ∧ (∀ e ∈ ys, noLabels e) ∧
      globalsApproxNoLabels c1.valApproxSpt := by
  obtain ⟨run, inputSafe⟩ := h
  have fvsSafe : ∀ e ∈ ClosFvs.compileSource xs, noLabels e := by
    exact (ClosFvs.removeSource_noLabels 0 xs).mpr inputSafe
  have emptySafe : globalsApproxNoLabels .ln := by
    simp [globalsApproxNoLabels]
  have traversal := knownNoLabels c (ClosFvs.compileSource xs) [] .ln
    ⟨fvsSafe, by simp, emptySafe⟩
  cases hk : knownListTotal c (ClosFvs.compileSource xs) [] .ln with
  | mk result globals =>
    simp only [hk] at traversal
    have ticksSafe := ClosTicks.removeSource_noLabels (result.map Prod.fst) traversal.1
    have letSafe := (ClosLetop.compileSource_noLabels _).mpr ticksSafe
    simp only [compileSource, hk, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨_, rfl, letSafe, traversal.2.2⟩

end Flapjack.Compiler.Backend.ClosKnown
