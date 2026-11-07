import Flapjack.Compiler.Backend.ClosMti.Proofs.Syntactic

/-! Application-arity preservation for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open ClosLang ClosProps
/-- Flapjack infrastructure: the stronger syntactic exclusion implies the
source arity predicate. -/
private theorem noBadApp_obeys (maxApp : Nat) (e : Exp) :
    ¬ containsAppSomeExp maxApp e → obeysMaxApp maxApp e := by
  induction e using containsAppSomeExp.induct
      (motive2 := fun fs => ¬ containsAppSomeFuns maxApp fs → obeysMaxAppFuns maxApp fs)
      (motive3 := fun es => ¬ containsAppSome maxApp es → obeysMaxAppList maxApp es)
  all_goals simp_all [containsAppSomeExp, containsAppSome, containsAppSomeFuns,
    obeysMaxApp, obeysMaxAppList, obeysMaxAppFuns]
/-- Lift the arity implication to expression lists. -/
private theorem noBadApps_obeys (maxApp : Nat) (es : List Exp)
    (valid : ¬ containsAppSome maxApp es) : ∀ e ∈ es, obeysMaxApp maxApp e := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [containsAppSome, not_or] at valid
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨noBadApp_obeys maxApp e valid.1, ih valid.2⟩

/-- Multi-argument introduction respects the configured application bound. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "intro_multi_obeys_max_app"]
theorem intro_multi_obeys_max_app (maxApp : Nat) (es : List Exp)
    (premises : maxApp ≠ 0 ∧ ∀ e ∈ es, noMti e) :
    ∀ e ∈ introList maxApp es, obeysMaxApp maxApp e := by
  have positive : 0 < maxApp := Nat.pos_of_ne_zero premises.1
  have noBad : ¬ containsAppSome maxApp es := (noMtiList_syntactic maxApp positive es premises.2).2
  have noBadTransformed : ¬ containsAppSome maxApp (introList maxApp es) := by
    intro bad
    exact noBad ((introList_containsAppSome maxApp es).mp bad)
  exact noBadApps_obeys maxApp (introList maxApp es) noBadTransformed
end Flapjack.Compiler.Backend.ClosMti
