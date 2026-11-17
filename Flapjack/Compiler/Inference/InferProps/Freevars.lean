module

public import Flapjack.TypeSystemHOL.Environments

@[expose] public section

/-! Free-variable bounds used by inference completeness. -/
namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.TypeSystemHOL Flapjack.Basis.Pure.MlString

mutual
/-- Adding permitted type-variable names preserves a free-variable check. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "check_freevars_more"]
theorem checkFreevarsMore (bound : Nat) (names : List MlString) (t : SemanticT) :
    checkFreevars bound names t = true → ∀ names',
      (∀ name ∈ names, name ∈ names') → checkFreevars bound names' t = true := by
  intro checked names' included
  cases t with
  | var name =>
    have member : name ∈ names := by simpa [checkFreevars] using checked
    simpa [checkFreevars] using included name member
  | varDb n => simpa [checkFreevars] using checked
  | app ts id =>
    have all : checkFreevarsList bound names ts = true := by simpa [checkFreevars] using checked
    simpa [checkFreevars] using checkFreevarsListMore bound names ts all names' included
termination_by sizeOf t

/-- List recursion for the source type induction. -/
private theorem checkFreevarsListMore (bound : Nat) (names : List MlString) (ts : List SemanticT) :
    checkFreevarsList bound names ts = true → ∀ names',
      (∀ name ∈ names, name ∈ names') → checkFreevarsList bound names' ts = true := by
  intro checked names' included
  cases ts with
  | nil => simp [checkFreevarsList]
  | cons t ts =>
    simp only [checkFreevarsList, Bool.and_eq_true] at checked ⊢
    exact ⟨checkFreevarsMore bound names t checked.1 names' included,
      checkFreevarsListMore bound names ts checked.2 names' included⟩
termination_by sizeOf ts
end
end Flapjack.Compiler.Inference.InferProps
