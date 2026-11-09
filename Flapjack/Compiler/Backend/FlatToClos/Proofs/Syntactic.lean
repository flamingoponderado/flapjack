import Flapjack.Compiler.Backend.FlatToClos.Proofs.NoMti
import Flapjack.Compiler.Backend.Semantics.ClosProps.NoMtiSyntactic

/-! Closure syntax properties established by flat-to-closure compilation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.ClosProps

private theorem destConstant_noApp (maxApp : Nat) (e : ClosLang.Exp) (c : ClosLang.Const)
    (decoded : destConstant e = some c) : ¬ containsAppSomeExp maxApp e := by
  cases e <;> simp [destConstant] at decoded
  case op t op args =>
    cases args with
    | cons a rest => cases op <;> simp at decoded
    | nil =>
      cases op <;> try simp at decoded
      case intOp op => cases op <;> try simp at decoded <;> simp [containsAppSomeExp, containsAppSome]
      case blockOp op => cases op <;> try simp at decoded <;> simp [containsAppSomeExp, containsAppSome]

private theorem destConstants_noApp (maxApp : Nat) (xs : List ClosLang.Exp) (cs : List ClosLang.Const)
    (decoded : destConstants xs = some cs) : ¬ containsAppSome maxApp xs := by
  induction xs generalizing cs with
  | nil => simp [containsAppSome]
  | cons x xs ih =>
    cases first : destConstant x with
    | none => simp [destConstants, first] at decoded
    | some c =>
      cases rest : destConstants xs with
      | none => simp [destConstants, first, rest] at decoded
      | some cs' =>
        simpa [containsAppSome] using
          And.intro (destConstant_noApp maxApp x c first) (ih cs' rest)

/-- The smart constructor preserves the application predicate. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "contains_App_SOME_SmartCons"]
theorem containsAppSome_smartCons (maxApp : Nat) (t : BackendCommon.Tra) (tag : Nat)
    (xs : List ClosLang.Exp) :
    containsAppSome maxApp [smartCons t tag xs] ↔ containsAppSome maxApp xs := by
  cases xs with
  | nil => simp [smartCons, containsAppSome, containsAppSomeExp]
  | cons x xs =>
    cases decoded : destConstants (x :: xs) with
    | none => simp [smartCons, decoded, containsAppSome, containsAppSomeExp]
    | some constants =>
      have absent := destConstants_noApp maxApp (x :: xs) constants decoded
      simp [smartCons, decoded, containsAppSome, containsAppSomeExp] at absent ⊢
      exact absent

/-- The smart constructor preserves the function-annotation predicate. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "every_Fn_vs_NONE_SmartCons"]
theorem everyFnVarsNone_smartCons (t : BackendCommon.Tra) (tag : Nat) (xs : List ClosLang.Exp) :
    everyFnVarsNone [smartCons t tag xs] ↔ everyFnVarsNone xs := by
  cases xs with
  | nil => simp [smartCons, everyFnVarsNone, fnVarsNoneExp]
  | cons x xs =>
    cases decoded : destConstants (x :: xs) with
    | none => simp [smartCons, decoded, everyFnVarsNone, fnVarsNoneExp]
    | some constants =>
      have safe : ∀ e ∈ x :: xs, noMti e := by
        apply (noMti_smartCons t tag (x :: xs)).1
        simp [smartCons, decoded, noMti, noMtiList]
      have annotations := (noMtiList_syntactic 1 (by decide) _ safe).1
      simp [smartCons, decoded, everyFnVarsNone, fnVarsNoneExp, annotations]

/-- Initializer functions carry no variable annotations. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "every_Fn_vs_NONE_compile_init"]
theorem everyFnVarsNone_compileInit (b : Bool) :
    everyFnVarsNone [ClosInterp.compileInit b] := by
  have safe : ∀ e ∈ [ClosInterp.compileInit b], noMti e := by
    simpa using compileInit_noMti b
  exact (noMtiList_syntactic 1 (by decide) _ safe).1

/-- Initializer code contains no application exceeding a positive limit. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "contains_App_SOME_compile_init" 2549]
theorem containsAppSome_compileInit (maxApp : Nat) (b : Bool) :
    1 ≤ maxApp → (containsAppSome maxApp [ClosInterp.compileInit b] ↔ False) := by
  intro positive
  have safe : ∀ e ∈ [ClosInterp.compileInit b], noMti e := by
    simpa using compileInit_noMti b
  have absent := (noMtiList_syntactic maxApp positive _ safe).2
  exact ⟨fun present => (absent present).elim, False.elim⟩

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
