import Flapjack.Compiler.Backend.SourceToFlat.Proofs.CompileDecGlobals
import Flapjack.Compiler.Backend.SourceToFlat.Eliminate
import Flapjack.Compiler.Backend.FlatElim.Proofs.GlobalInvariants
import Flapjack.Compiler.Backend.FlatPattern.Proofs.GlobalSafety

/-! Global-initialization safety through the complete source-to-flat pass. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.Compiler.Backend.FlatProps

/-- Elimination and pattern compilation preserve global-initialization safety. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "compile_flat_esgc_free"]
theorem compileFlat_esgcFree (cfg : FlatPattern.Config) (ds ds' : List FlatLang.Exp)
    (h : compileFlatTotal cfg ds = ds' ∧ ∀ e ∈ ds, esgcFree e) :
    ∀ e ∈ ds', esgcFree e := by
  rw [← h.1]
  unfold compileFlatTotal
  apply FlatPattern.compileDecs_esgcFree
  exact FlatElim.removeFlatProg_esgcFree ds h.2

/-- The complete source-to-flat pass emits safe declarations. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "compile_esgc_free"]
theorem compile_esgcFree (c : Config) (p : List Dec) :
    ∀ e ∈ (compileTotal c p).2, esgcFree e := by
  generalize hp : compileProg c p = result
  obtain ⟨next, code⟩ := result
  have safe := compileProg_esgcFree c p next code hp
  have out := compileFlat_esgcFree next.patternCfg code (compileFlatTotal next.patternCfg code) ⟨rfl, safe⟩
  simpa [compileTotal, hp] using out

/-- Incremental source-to-flat compilation emits safe declarations. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "inc_compile_esgc_free"]
theorem incCompile_esgcFree (envId : Nat × Nat) (c : Config) (p : List Dec) :
    ∀ e ∈ (incCompile envId c p).2, esgcFree e := by
  generalize hp : incCompileProg envId c p = result
  obtain ⟨next, code⟩ := result
  have safe := incCompileProg_esgcFree envId c p
  simp only [hp] at safe
  have out := FlatPattern.compileDecs_esgcFree next.patternCfg code safe
  simpa [incCompile, hp] using out

end Flapjack.Compiler.Backend.SourceToFlat
