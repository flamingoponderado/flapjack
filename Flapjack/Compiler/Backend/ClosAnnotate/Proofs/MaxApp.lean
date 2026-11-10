import Flapjack.Compiler.Backend.ClosAnnotate.Shift.OriginalEquivalence
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.CodeLocations
import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic.LabelsAndArity

/-! Preservation of the source application-arity bound by closure shifting. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang ClosProps

/-- A singleton shift satisfies EVERY exactly when its head does. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "EVERY_shift_sing"]
theorem every_shiftSing (f : Exp → Prop) (expression : Exp) (m l : Nat) (i : Spt Nat) :
    (∀ e ∈ shiftSource [expression] m l i, f e) ↔
      f (@Flapjack.holHd Exp ⟨.var .none 0⟩ (shiftSource [expression] m l i)) := by
  rw [shiftSource_sing_eq.1]
  simp [Flapjack.holHd]

mutual
/-- Structural helper for the singleton shift case of arity preservation. -/
theorem shiftSing_obeysMaxApp (bound : Nat) (expression : Exp) (m l : Nat) (i : Spt Nat)
    (safe : obeysMaxApp bound expression) : obeysMaxApp bound (shiftSing expression m l i) := by
  cases expression with
  | var trace n => simp [shiftSing, obeysMaxApp]
  | ifThenElse trace a b c =>
    simp only [shiftSing, obeysMaxApp] at safe ⊢
    exact ⟨shiftSing_obeysMaxApp bound a m l i safe.1,
      shiftSing_obeysMaxApp bound b m l i safe.2.1,
      shiftSing_obeysMaxApp bound c m l i safe.2.2⟩
  | «let» trace args body =>
    simp only [shiftSing, obeysMaxApp] at safe ⊢
    exact ⟨shiftList_obeysMaxApp bound args m l i safe.1,
      shiftSing_obeysMaxApp bound body m (l + args.length) i safe.2⟩
  | raise trace body =>
    simpa [shiftSing, obeysMaxApp] using shiftSing_obeysMaxApp bound body m l i (by simpa [obeysMaxApp] using safe)
  | tick trace body =>
    simpa [shiftSing, obeysMaxApp] using shiftSing_obeysMaxApp bound body m l i (by simpa [obeysMaxApp] using safe)
  | handle trace a b =>
    simp only [shiftSing, obeysMaxApp] at safe ⊢
    exact ⟨shiftSing_obeysMaxApp bound a m l i safe.1,
      shiftSing_obeysMaxApp bound b m (l + 1) i safe.2⟩
  | op trace op args =>
    simpa [shiftSing, obeysMaxApp] using shiftList_obeysMaxApp bound args m l i (by simpa [obeysMaxApp] using safe)
  | call trace ticks dest args =>
    simpa [shiftSing, obeysMaxApp] using shiftList_obeysMaxApp bound args m l i (by simpa [obeysMaxApp] using safe)
  | app trace loc fn args =>
    simp only [shiftSing, obeysMaxApp, shiftList_length] at safe ⊢
    exact ⟨safe.1, shiftSing_obeysMaxApp bound fn m l i safe.2.1,
      shiftList_obeysMaxApp bound args m l i safe.2.2⟩
  | fn name loc vars arity body =>
    simp only [obeysMaxApp] at safe
    simpa [shiftSing, obeysMaxApp] using shiftSing_obeysMaxApp bound body (m + l) arity
      (shiftedEnv 0 ((vars.getD []).filter (· < m + l))) safe
  | letrec names loc vars fs body =>
    simp only [obeysMaxApp] at safe
    simpa [shiftSing, obeysMaxApp] using And.intro
      (shiftFuns_obeysMaxApp bound fs fs.length (m + l)
        (shiftedEnv 0 ((vars.getD []).filter (· < m + l))) safe.1)
      (shiftSing_obeysMaxApp bound body m (l + fs.length) i safe.2)
termination_by sizeOf expression

/-- Structural helper for shifted expression lists. -/
theorem shiftList_obeysMaxApp (bound : Nat) (expressions : List Exp) (m l : Nat) (i : Spt Nat)
    (safe : obeysMaxAppList bound expressions) : obeysMaxAppList bound (shiftList expressions m l i) := by
  cases expressions with
  | nil => simp [shiftList, obeysMaxAppList]
  | cons head tail =>
    simp only [obeysMaxAppList] at safe
    simp only [shiftList, obeysMaxAppList]
    exact ⟨shiftSing_obeysMaxApp bound head m l i safe.1,
      shiftList_obeysMaxApp bound tail m l i safe.2⟩
termination_by sizeOf expressions

/-- Structural helper for shifted recursive function groups. -/
theorem shiftFuns_obeysMaxApp (bound : Nat) (functions : List (Nat × Exp)) (count m : Nat) (i : Spt Nat)
    (safe : obeysMaxAppFuns bound functions) : obeysMaxAppFuns bound (shiftFuns count m i functions) := by
  cases functions with
  | nil => simp [shiftFuns, obeysMaxAppFuns]
  | cons entry tail =>
    cases entry with
    | mk arity body =>
      simp only [obeysMaxAppFuns] at safe
      simp only [shiftFuns, obeysMaxAppFuns]
      exact ⟨shiftSing_obeysMaxApp bound body m (arity + count) i safe.1,
        shiftFuns_obeysMaxApp bound tail count m i safe.2⟩
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega
end

/-- Shifting preserves the application-arity bound for all expressions. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "shift_obeys_max_app"]
theorem shiftSource_obeysMaxApp (bound : Nat) (expressions : List Exp) (m l : Nat) (i : Spt Nat)
    (safe : ∀ expression ∈ expressions, obeysMaxApp bound expression) :
    ∀ expression ∈ shiftSource expressions m l i, obeysMaxApp bound expression := by
  rw [shiftSource_eq_shiftList]
  exact (obeysMaxAppList_iff _ _).1
    (shiftList_obeysMaxApp bound expressions m l i ((obeysMaxAppList_iff _ _).2 safe))

end Flapjack.Compiler.Backend.ClosAnnotate
