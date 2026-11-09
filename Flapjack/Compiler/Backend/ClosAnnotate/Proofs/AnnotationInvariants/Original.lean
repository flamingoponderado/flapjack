import Flapjack.Compiler.Backend.ClosAnnotate.Original
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.AnnotationInvariants

/-! Source-shaped closure annotation invariants. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang ClosProps

/-- Annotating a singleton yields the singleton containing its head. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "HD_annotate_SING"]
theorem hdAnnotate_sing (arity : Nat) (expression : Exp) :
    [@Flapjack.holHd Exp ⟨.var .none 0⟩ (annotateSource arity [expression])] =
      annotateSource arity [expression] := by
  rw [(annotateSource_sing_eq arity expression []).1]
  rfl

/-- Annotation preserves existing function-code locations in every program body. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "every_Fn_SOME_ann"]
theorem everyFnSome_ann {α : Type} (program : List (α × Nat × Exp)) :
    everyFnLocationSome (program.map (fun entry => entry.2.2)) →
      everyFnLocationSome ((compileSource program).map (fun entry => entry.2.2)) := by
  rw [compileSource_eq_compile]
  induction program with
  | nil => simp [compile, everyFnLocationSome]
  | cons entry rest ih =>
    obtain ⟨name, arity, body⟩ := entry
    simp only [compile, List.map_cons, everyFnLocationSome] at *
    intro locations
    exact ⟨annotateSing_locations arity body locations.1, ih locations.2⟩

end Flapjack.Compiler.Backend.ClosAnnotate
