import Flapjack.Compiler.Backend.FlatToClos.Proofs.NoMti
import Flapjack.Compiler.Backend.Semantics.ClosProps.NoMtiSyntactic

/-! Closure syntax properties established by flat-to-closure compilation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.ClosProps

private theorem compile_noMti (m : List (Option MlString)) (xs : List FlatLang.Exp) :
    ∀ e ∈ compile m xs, noMti e := by
  induction xs with
  | nil => simp [compile, compileExps]
  | cons x xs ih =>
    simp only [compile, compileExps] at ih ⊢
    intro e member
    rcases List.mem_cons.mp member with rfl | member
    · exact compileExp_noMti m x
    · exact ih e member

/-- Compiled expressions have the three original closure syntax properties. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "compile_syntactic_props"]
theorem compile_syntacticProps (maxApp : Nat) (positive : 0 < maxApp)
    (m : List (Option MlString)) (xs : List FlatLang.Exp) :
    ¬ containsAppSome maxApp (compile m xs) ∧
      (∀ e ∈ compile m xs, noMti e) ∧ everyFnVarsNone (compile m xs) := by
  have safe := compile_noMti m xs
  have properties := noMtiList_syntactic maxApp positive (compile m xs) safe
  exact ⟨properties.2, safe, properties.1⟩

/-- Compiled declarations have the original closure syntax properties. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "compile_decs_syntactic_props"]
theorem compileDecs_syntacticProps (maxApp : Nat) (ds : List FlatLang.Exp) :
    (∀ e ∈ compileDecs ds, noMti e) ∧ everyFnVarsNone (compileDecs ds) ∧
      (0 < maxApp → ¬ containsAppSome maxApp (compileDecs ds)) := by
  have safe := compileDecs_noMti ds
  have properties := noMtiList_syntactic 1 (by decide) (compileDecs ds) safe
  exact ⟨safe, properties.1, fun positive => (noMtiList_syntactic maxApp positive _ safe).2⟩

/-- Program compilation, including the interpreter, has the syntax properties. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "compile_prog_syntactic_props"]
theorem compileProg_syntacticProps (maxApp : Nat) (ds : List FlatLang.Exp) :
    (∀ e ∈ compileProg ds, noMti e) ∧ everyFnVarsNone (compileProg ds) ∧
      (0 < maxApp → ¬ containsAppSome maxApp (compileProg ds)) := by
  have safe : ∀ e ∈ compileProg ds, noMti e := by
    have compiled := compileDecs_noMti ds
    simpa [compileProg, ClosInterp.attachInterpreter, compileInit_noMti] using compiled
  have properties := noMtiList_syntactic 1 (by decide) (compileProg ds) safe
  exact ⟨safe, properties.1, fun positive => (noMtiList_syntactic maxApp positive _ safe).2⟩

/-- Incremental compilation has the original closure syntax properties. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "FST_inc_compile_syntactic_props"]
theorem incCompileDecs_syntacticProps {α β γ : Type} (maxApp : Nat) (ds : List FlatLang.Exp) :
    (∀ e ∈ (incCompileDecs (α := α) ds).1, noMti e) ∧
      everyFnVarsNone (incCompileDecs (α := β) ds).1 ∧
      (0 < maxApp → ¬ containsAppSome maxApp (incCompileDecs (α := γ) ds).1) := by
  have safeAll : ∀ {X : Type}, ∀ e ∈ (incCompileDecs (α := X) ds).1, noMti e := by
    intro X e member
    apply ClosInterp.insertInterp_noMti e _ member
    intro x sourceMember
    rcases List.mem_append.mp sourceMember with original | unit
    · exact compileDecs_noMti ds x original
    · exact compileDecs_noMti [.con .none none []] x unit
  have safe := safeAll (X := α)
  have safeBeta := safeAll (X := β)
  have safeGamma := safeAll (X := γ)
  have properties := noMtiList_syntactic 1 (by decide) _ safeBeta
  exact ⟨safe, properties.1, fun positive => (noMtiList_syntactic maxApp positive _ safeGamma).2⟩

end Flapjack.Compiler.Backend.FlatToClos
