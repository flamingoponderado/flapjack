module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.TraversalArity
public import Flapjack.Compiler.Backend.ClosKnown.Compile
public import Flapjack.Compiler.Backend.ClosFvs.Proofs.Arity
public import Flapjack.Compiler.Backend.ClosTicks.Proofs.Arity
public import Flapjack.Compiler.Backend.ClosLetop.Proofs.Arity

@[expose] public section

/-! Application-arity preservation for the complete known-function pass. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang ClosProps

/-- The enabled optimizer preserves the bound and returns safe global approximations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "compile_obeys_max_app"]
theorem compileObeysMaxApp (limit : Nat) (c : Config) (xs : List Exp)
    (res : Option Config) (ys : List Exp)
    (h : compileSource (some c) xs = (res, ys) ∧ ∀ e ∈ xs, obeysMaxApp limit e) :
    ∃ c1, res = some c1 ∧ (∀ e ∈ ys, obeysMaxApp limit e) ∧
      globalsApproxObeysMaxApp limit c1.valApproxSpt := by
  obtain ⟨run, inputSafe⟩ := h
  have fvsSafe : ∀ e ∈ ClosFvs.compileSource xs, obeysMaxApp limit e := by
    exact (ClosFvs.removeSource_obeysMaxApp limit 0 xs).mpr inputSafe
  have emptySafe : globalsApproxObeysMaxApp limit .ln := by
    simp [globalsApproxObeysMaxApp]
  have traversal := knownObeysMaxApp limit c (ClosFvs.compileSource xs) [] .ln
    ⟨fvsSafe, by simp, emptySafe⟩
  cases hk : knownListTotal c (ClosFvs.compileSource xs) [] .ln with
  | mk result globals =>
    simp only [hk] at traversal
    have ticksSafe := ClosTicks.removeSource_obeysMaxApp limit (result.map Prod.fst) traversal.1
    have letSafe := (ClosLetop.compileSource_obeysMaxApp limit _).mpr ticksSafe
    simp only [compileSource, hk, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨_, rfl, letSafe, traversal.2.2⟩

end Flapjack.Compiler.Backend.ClosKnown
