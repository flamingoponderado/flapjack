import Flapjack.Compiler.Backend.ClosInterp.Optimise
import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic

/-! Application invariants of interpreter insertion. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open ClosLang ClosProps

/-- Local successful-optimization case of the HOL proof, without a separate HOL declaration. -/
private theorem optInterp_noAppSome (maxApp : Nat) (positive : 1 ≤ maxApp)
    (e e' : Exp) (run : optInterp e = some e') : ¬ containsAppSomeExp maxApp e' := by
  unfold optInterp at run
  split at run
  · simp only [Option.some.injEq] at run
    subst e'
    simp [containsAppSomeExp, containsAppSome, Nat.not_lt.mpr positive]
  · simp at run

/-- Local fallback case of the HOL proof, without a separate HOL declaration. -/
private theorem optInterp1_noAppSome (maxApp : Nat) (positive : 1 ≤ maxApp)
    (e : Exp) (safe : ¬ containsAppSomeExp maxApp e) : ¬ containsAppSomeExp maxApp (optInterp1 e) := by
  cases result : optInterp e with
  | none => simpa [optInterp1, result] using safe
  | some e' => simpa [optInterp1, result] using optInterp_noAppSome maxApp positive e e' result

/-- Local mapped-list case of the HOL proof, without a separate HOL declaration. -/
private theorem mappedOpt_noAppSome (maxApp : Nat) (positive : 1 ≤ maxApp)
    (es : List Exp) (safe : ¬ containsAppSome maxApp es) : ¬ containsAppSome maxApp (es.map optInterp1) := by
  induction es with
  | nil => simp [containsAppSome]
  | cons e es ih =>
    simp only [List.map_cons, containsAppSome, not_or] at safe ⊢
    exact ⟨optInterp1_noAppSome maxApp positive e safe.1, ih safe.2⟩

/-- Local singleton case of the HOL proof, without a separate HOL declaration. -/
private theorem insertInterp1_noAppSome (maxApp : Nat) (positive : 1 ≤ maxApp)
    (e : Exp) (safe : ¬ containsAppSomeExp maxApp e) : ¬ containsAppSomeExp maxApp (insertInterp1 e) := by
  cases result : optInterp e with
  | some e' => simpa [insertInterp1, result] using optInterp_noAppSome maxApp positive e e' result
  | none =>
    cases e <;> simp [insertInterp1, result, containsAppSomeExp] at safe ⊢ <;> try assumption
    case «let» t es body => exact ⟨safe.1, mappedOpt_noAppSome maxApp positive es safe.2⟩

/-- Interpreter insertion preserves the source application invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_interpProofScript.sml" "contains_App_SOME_insert_interp"]
theorem containsAppSome_insertInterp (maxApp : Nat) (xs : List Exp)
    (safe : ¬ containsAppSome maxApp xs ∧ 1 ≤ maxApp) :
    ¬ containsAppSome maxApp (insertInterp xs) := by
  obtain ⟨safe, positive⟩ := safe
  induction xs with
  | nil => simp [insertInterp, containsAppSome]
  | cons e es ih =>
    simp only [containsAppSome, not_or] at safe
    simp only [insertInterp, List.map_cons, containsAppSome, not_or]
    exact ⟨insertInterp1_noAppSome maxApp positive e safe.1, by simpa [insertInterp] using ih safe.2⟩

end Flapjack.Compiler.Backend.ClosInterp
