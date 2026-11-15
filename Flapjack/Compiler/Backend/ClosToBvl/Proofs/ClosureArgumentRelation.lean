module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ClosureArguments
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Call
public import Mathlib.Data.List.Forall2

@[expose] public section

/-! Relations on arguments left by closure application. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Full closure application preserves the relation on remaining arguments. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "list_rel_app"]
theorem listRelApp {α : Type} (maxApp : Nat) (R : ClosSem.Value → α → Prop)
    (args : List ClosSem.Value) (targetArgs : List α) (remaining : List ClosSem.Value)
    (body : ClosLang.Exp) (env : List ClosSem.Value) (func : ClosSem.Value) (remArgs : Nat)
    (premises : ClosSem.destClosure maxApp none func args = some (.fullApp body env remaining) ∧
      numRemainingArgs func = some remArgs ∧ List.Forall₂ R args targetArgs) :
    List.Forall₂ R remaining (targetArgs.take (targetArgs.length - remArgs)) := by
  rcases premises with ⟨found, rem, rel⟩
  have remainingEq : remaining = args.take (args.length - remArgs) := by
    cases func <;> simp only [ClosSem.destClosure, numRemainingArgs] at found rem <;> try contradiction
    case closure location supplied captured arity expression =>
      simp only [Option.some.injEq] at rem
      subst remArgs
      split at found
      · split at found
        · simp at found
        · simp only [Option.some.injEq, ClosSem.AppKind.fullApp.injEq] at found
          rcases found with ⟨_, _, rfl⟩
          simp [List.reverse_drop]
      · simp at found
    case recclosure location supplied captured functions index =>
      split at found
      · simp at found
      · rename_i arity expression selected
        split at found
        · split at found
          · simp at found
          · simp only [Option.some.injEq, ClosSem.AppKind.fullApp.injEq] at found
            rcases found with ⟨_, _, rfl⟩
            have idx : index < functions.length := List.getElem?_eq_some_iff.mp selected |>.1
            have entry := Flapjack.holEl_eq_getElem index functions idx
            have get := List.getElem?_eq_getElem idx
            rw [selected] at get
            simp only [Option.some.injEq] at get
            rw [entry, ← get] at rem
            simp only [Option.some.injEq] at rem
            subst remArgs
            simp [List.reverse_drop]
        · simp at found
  subst remaining
  have sameLength := rel.length_eq
  simpa [sameLength] using List.forall₂_take (args.length - remArgs) rel

/-- Dropping the same argument prefix preserves the pointwise value relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "cl_rel_run_lemma3"]
theorem clRelRunLemma3 {α β : Type} (R : α → β → Prop) (args : List α)
    (args' : List β) (n : Nat) (related : List.Forall₂ R args args') :
    List.Forall₂ R (args.drop (args'.length - n)) (args'.drop (args'.length - n)) :=
  List.forall₂_drop (args'.length - n) related

end Flapjack.Compiler.Backend.ClosToBvl
