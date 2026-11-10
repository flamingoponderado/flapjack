module

public import Flapjack.Compiler.Backend.ClosAnnotate.Original
public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.AnnotationInvariants

@[expose] public section

/-! Source-shaped closure annotation invariants. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang ClosProps

/-- Shifting supplies the free-variable annotation of each function. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "every_Fn_vs_SOME_shift"]
theorem everyFnVarsSome_shift (expressions : List Exp) (m l : Nat) (index : Spt Nat) :
    everyFnVarsSome (shiftSource expressions m l index) := by
  rw [shiftSource_eq_shiftList]
  exact shiftList_varsSome expressions m l index

/-- Annotation supplies the free-variable annotation of each function. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "every_Fn_vs_SOME_annotate"]
theorem everyFnVarsSome_annotate (arity : Nat) (expressions : List Exp) :
    everyFnVarsSome (annotateSource arity expressions) := by
  unfold annotateSource
  exact everyFnVarsSome_shift _ 0 arity .ln

/-- Shifting preserves precisely the function-location invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "every_Fn_SOME_shift"]
theorem everyFnSome_shift (expressions : List Exp) (m l : Nat) (index : Spt Nat) :
    everyFnLocationSome (shiftSource expressions m l index) ↔ everyFnLocationSome expressions := by
  rw [shiftSource_eq_shiftList]
  exact shiftList_locations expressions m l index

/-- The padding constant contains no unlocated functions. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "every_Fn_SOME_const_0"]
theorem everyFnSome_const0 (trace : BackendCommon.Tra) :
    everyFnLocationSome [const0 trace] := by
  simp [const0, everyFnLocationSome, fnLocationSomeExp]

/-- Free-variable rewriting preserves function locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "every_Fn_SOME_alt_free"]
theorem everyFnSome_altFree (expressions : List Exp) :
    everyFnLocationSome expressions → everyFnLocationSome (altFreeSource expressions).1 := by
  rw [altFreeSource_sing_eq.2.1]
  exact altFreeList_locations expressions

/-- Annotation preserves function locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "every_Fn_SOME_annotate"]
theorem everyFnSome_annotate (expressions : List Exp) (arity : Nat) :
    everyFnLocationSome expressions → everyFnLocationSome (annotateSource arity expressions) := by
  intro locations
  unfold annotateSource
  exact (everyFnSome_shift _ 0 arity .ln).2 (everyFnSome_altFree expressions locations)

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
    have annotated := everyFnSome_annotate [body] arity (by simpa [everyFnLocationSome] using locations.1)
    rw [(annotateSource_sing_eq arity body []).1] at annotated
    exact ⟨by simpa [everyFnLocationSome] using annotated, ih locations.2⟩

end Flapjack.Compiler.Backend.ClosAnnotate
