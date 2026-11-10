import Flapjack.Compiler.Backend.ClosAnnotate.Original
import Flapjack.FiniteMap.AlistExact.Lookup

/-! Original closure-annotation compiler list properties. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang

/-- Reversing the compiled list is compiling the reversed list. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "REVERSE_compile"]
theorem reverse_compileSource {α : Type} (program : List (α × Nat × Exp)) :
    (compileSource program).reverse = compileSource program.reverse := by
  simp [compileSource]

/-- Lookup after compilation maps the corresponding source lookup result. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "ALOOKUP_compile"]
theorem alookup_compileSource {α : Type} (program : List (α × Nat × Exp)) :
    Flapjack.holALookup (compileSource program) =
      Option.map (fun (args, exp) =>
        (args, @Flapjack.holHd Exp ⟨.var .none 0⟩ (annotateSource args [exp]))) ∘
        Flapjack.holALookup program := by
  classical
  funext key
  induction program with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨entryKey, args, exp⟩ := entry
    simp only [Function.comp_apply, compileSource] at ih
    by_cases equal : key = entryKey <;>
      simp [compileSource, Flapjack.holALookup, equal, ih]

/-- Compilation distributes over list append. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "compile_append"]
theorem compileSource_append {α : Type} (left right : List (α × Nat × Exp)) :
    compileSource (left ++ right) = compileSource left ++ compileSource right := by
  simp [compileSource]

end Flapjack.Compiler.Backend.ClosAnnotate
