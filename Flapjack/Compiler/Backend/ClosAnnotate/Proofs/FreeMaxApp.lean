import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.MaxApp
import Flapjack.Compiler.Backend.ClosAnnotate.Free.OriginalEquivalence
import Flapjack.Compiler.Backend.ClosAnnotate.Original

/-! Preservation of application bounds by free-variable annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang ClosProps

mutual
/-- Structural singleton case for the source free-variable bound proof. -/
theorem altFreeSing_obeysMaxApp (bound : Nat) (expression : Exp)
    (safe : obeysMaxApp bound expression) : obeysMaxApp bound (altFreeSing expression).1 := by
  cases expression with
  | var trace n => simp [altFreeSing, obeysMaxApp]
  | ifThenElse trace a b c =>
    simp only [obeysMaxApp] at safe
    simpa [altFreeSing, obeysMaxApp] using
      And.intro (altFreeSing_obeysMaxApp bound a safe.1)
        (And.intro (altFreeSing_obeysMaxApp bound b safe.2.1) (altFreeSing_obeysMaxApp bound c safe.2.2))
  | «let» trace args body =>
    simp only [obeysMaxApp] at safe
    have argsOk := altFreeList_obeysMaxApp bound args safe.1
    have bodyOk := altFreeSing_obeysMaxApp bound body safe.2
    have replicated : ∀ n, obeysMaxAppList bound (List.replicate n (const0 trace)) := by
      intro n
      induction n with
      | zero => simp [obeysMaxAppList]
      | succ n ih =>
        simp only [List.replicate_succ, obeysMaxAppList]
        exact ⟨by simp [const0, obeysMaxApp, obeysMaxAppList], ih⟩
    simp only [altFreeSing]
    split
    · simpa [obeysMaxApp] using And.intro (replicated args.length) bodyOk
    · simpa [obeysMaxApp] using And.intro argsOk bodyOk
  | raise trace body =>
    simpa [altFreeSing, obeysMaxApp] using altFreeSing_obeysMaxApp bound body (by simpa [obeysMaxApp] using safe)
  | tick trace body =>
    simpa [altFreeSing, obeysMaxApp] using altFreeSing_obeysMaxApp bound body (by simpa [obeysMaxApp] using safe)
  | handle trace a b =>
    simp only [obeysMaxApp] at safe
    simpa [altFreeSing, obeysMaxApp] using
      And.intro (altFreeSing_obeysMaxApp bound a safe.1) (altFreeSing_obeysMaxApp bound b safe.2)
  | op trace op args =>
    simpa [altFreeSing, obeysMaxApp] using altFreeList_obeysMaxApp bound args (by simpa [obeysMaxApp] using safe)
  | call trace ticks dest args =>
    simpa [altFreeSing, obeysMaxApp] using altFreeList_obeysMaxApp bound args (by simpa [obeysMaxApp] using safe)
  | app trace loc fn args =>
    simp only [obeysMaxApp] at safe
    simpa [altFreeSing, obeysMaxApp, altFreeList_length] using
      And.intro safe.1 (And.intro (altFreeSing_obeysMaxApp bound fn safe.2.1)
        (altFreeList_obeysMaxApp bound args safe.2.2))
  | fn name loc vars arity body =>
    simpa [altFreeSing, obeysMaxApp] using altFreeSing_obeysMaxApp bound body (by simpa [obeysMaxApp] using safe)
  | letrec names loc vars functions body =>
    simp only [obeysMaxApp] at safe
    simpa [altFreeSing, obeysMaxApp] using And.intro
      (altFreeFuns_obeysMaxApp bound functions functions.length safe.1)
      (altFreeSing_obeysMaxApp bound body safe.2)
termination_by sizeOf expression

/-- Structural list case for the source free-variable bound proof. -/
theorem altFreeList_obeysMaxApp (bound : Nat) (expressions : List Exp)
    (safe : obeysMaxAppList bound expressions) : obeysMaxAppList bound (altFreeList expressions).1 := by
  cases expressions with
  | nil => simp [altFreeList, obeysMaxAppList]
  | cons first rest =>
    simp only [obeysMaxAppList] at safe
    simpa [altFreeList, obeysMaxAppList] using
      And.intro (altFreeSing_obeysMaxApp bound first safe.1) (altFreeList_obeysMaxApp bound rest safe.2)
termination_by sizeOf expressions

/-- Structural recursive-group case for the source free-variable bound proof. -/
theorem altFreeFuns_obeysMaxApp (bound : Nat) (functions : List (Nat × Exp)) (count : Nat)
    (safe : obeysMaxAppFuns bound functions) :
    obeysMaxAppFuns bound ((altFreeFuns count functions).map Prod.fst) := by
  cases functions with
  | nil => simp [altFreeFuns, obeysMaxAppFuns]
  | cons first rest =>
    cases first with
    | mk arity body =>
      simp only [obeysMaxAppFuns] at safe
      simpa [altFreeFuns, obeysMaxAppFuns] using
        And.intro (altFreeSing_obeysMaxApp bound body safe.1) (altFreeFuns_obeysMaxApp bound rest count safe.2)
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega
end

/-- Original free-variable discovery preserves the application-arity bound.
The three unused parameters retain the independent types inferred by HOL. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "alt_free_obeys_max_app"]
theorem altFreeSource_obeysMaxApp {α β γ : Type} (bound : Nat) (expressions : List Exp)
    (_m : α) (_l : β) (_i : γ)
    (safe : ∀ expression ∈ expressions, obeysMaxApp bound expression) :
    ∀ expression ∈ (altFreeSource expressions).1, obeysMaxApp bound expression := by
  rw [altFreeSource_sing_eq.2.1]
  exact (obeysMaxAppList_iff _ _).1
    (altFreeList_obeysMaxApp bound expressions ((obeysMaxAppList_iff _ _).2 safe))

/-- Original annotation preserves the application-arity bound. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "annotate_obeys_max_app"]
theorem annotateSource_obeysMaxApp (bound arity : Nat) (expressions : List Exp)
    (safe : ∀ expression ∈ expressions, obeysMaxApp bound expression) :
    ∀ expression ∈ annotateSource arity expressions, obeysMaxApp bound expression := by
  unfold annotateSource
  exact shiftSource_obeysMaxApp bound _ 0 arity .ln
    (altFreeSource_obeysMaxApp bound expressions (0 : Nat) (0 : Nat) (0 : Nat) safe)

/-- Original program annotation preserves the application-arity bound. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "obeys_max_app_ann"]
theorem compileSource_obeysMaxApp {α : Type} (bound : Nat) (program : List (α × Nat × Exp))
    (safe : ∀ expression ∈ program.map (fun entry => entry.2.2), obeysMaxApp bound expression) :
    ∀ expression ∈ (compileSource program).map (fun entry => entry.2.2), obeysMaxApp bound expression := by
  intro expression member
  simp only [compileSource, List.map_map, Function.comp_def] at member
  obtain ⟨⟨name, arity, body⟩, sourceMember, rfl⟩ := List.mem_map.mp member
  have bodySafe : obeysMaxApp bound body := safe body (List.mem_map.mpr ⟨(name, arity, body), sourceMember, rfl⟩)
  have annotated := annotateSource_obeysMaxApp bound arity [body] (by simpa using bodySafe)
  rw [(annotateSource_sing_eq arity body []).1] at annotated
  rw [(annotateSource_sing_eq arity body []).1]
  simpa [Flapjack.holHd] using annotated (annotateSing arity body) (by simp)

end Flapjack.Compiler.Backend.ClosAnnotate
