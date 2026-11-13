module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.MtiLocations
public import Flapjack.Compiler.Backend.ClosMti.Proofs.TotalView

@[expose] public section

/-! Location annotations through multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosProps ClosLang

/-- Flapjack infrastructure: the single-expression case of the mutual list proof. -/
private theorem introExpLocation (m : Nat) (e : ClosLang.Exp) :
    fnLocationSomeExp (ClosMti.introExp m e) ↔ fnLocationSomeExp e := by
  have listIH (xs : List ClosLang.Exp) (bound : listBudget xs < expBudget e) :
      everyFnLocationSome (ClosMti.introList m xs) ↔ everyFnLocationSome xs := by
    induction xs with
    | nil => simp [ClosMti.introList, everyFnLocationSome]
    | cons head tail ih =>
      have headBound : expBudget head < expBudget e := by simp only [listBudget] at bound; omega
      have tailBound : listBudget tail < expBudget e := by simp only [listBudget] at bound; omega
      simp only [ClosMti.introList_cons, everyFnLocationSome,
        introExpLocation m head, ih tailBound]
  cases e with
  | var t n => simp [ClosMti.introExp_var, fnLocationSomeExp]
  | ifThenElse t a b c =>
    simp [ClosMti.introExp_if, fnLocationSomeExp, introExpLocation m a,
      introExpLocation m b, introExpLocation m c]
  | «let» t xs body =>
    have hxs := listIH xs (by simp [expBudget]; omega)
    simp [ClosMti.introExp_let, fnLocationSomeExp, hxs, introExpLocation m body]
  | raise t body => simp [ClosMti.introExp_raise, fnLocationSomeExp, introExpLocation m body]
  | tick t body => simp [ClosMti.introExp_tick, fnLocationSomeExp, introExpLocation m body]
  | handle t body handler =>
    simp [ClosMti.introExp_handle, fnLocationSomeExp, introExpLocation m body, introExpLocation m handler]
  | call t ticks dest args =>
    have hargs := listIH args (by simp [expBudget])
    simp [ClosMti.introExp_call, fnLocationSomeExp, hargs]
  | op t op args =>
    have hargs := listIH args (by simp [expBudget])
    simp [ClosMti.introExp_op, fnLocationSomeExp, hargs]
  | app t loc body args =>
    cases loc with
    | some loc =>
      have hargs := listIH args (by simp [expBudget]; omega)
      simp [ClosMti.introExp_app_some, fnLocationSomeExp, hargs, introExpLocation m body]
    | none =>
      cases found : ClosMti.collectApps m args body with
      | mk collected head =>
        have bounds := ClosMti.collectApps_budget m args body
        rw [found] at bounds
        change listBudget collected + expBudget head ≤ listBudget args + expBudget body at bounds
        have hargs := listIH collected (by simp [expBudget]; omega)
        have hhead := introExpLocation m head
        have collector := collectApps_everyFnLocationSome m args body collected head found
        simp only [everyFnLocationSome] at collector
        simpa [ClosMti.introExp_app_none, found, fnLocationSomeExp, hargs, hhead,
          and_assoc, and_left_comm, and_comm] using collector
  | fn name loc vs arity body =>
    cases loc with
    | some loc =>
      simp [ClosMti.introExp_fn_location, fnLocationSomeExp, introExpLocation m body]
    | none =>
      cases vs with
      | some vs => simp [ClosMti.introExp_fn_vars, fnLocationSomeExp]
      | none =>
        cases found : ClosMti.collectArgs m arity body with
        | mk count rest => simp [ClosMti.introExp_fn_none, found, fnLocationSomeExp]
  | letrec names loc vs fns body =>
    cases loc with
    | some loc =>
      simp [ClosMti.introExp_letrec_location, fnLocationSomeExp, introExpLocation m body]
    | none =>
      cases vs with
      | some vs => simp [ClosMti.introExp_letrec_vars, fnLocationSomeExp]
      | none => simp [ClosMti.introExp_letrec_none, fnLocationSomeExp]
termination_by expBudget e
decreasing_by
  all_goals simp_all [expBudget]
  all_goals omega

/-- Multi-argument introduction preserves and reflects function locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "every_Fn_SOME_intro_multi"]
theorem introMulti_everyFnLocationSome (m : Nat) (es : List ClosLang.Exp) :
    everyFnLocationSome (ClosMti.introList m es) ↔ everyFnLocationSome es := by
  induction es with
  | nil => simp [ClosMti.introList, everyFnLocationSome]
  | cons e es ih =>
    simp [ClosMti.introList_cons, everyFnLocationSome, introExpLocation, ih]
end Flapjack.Compiler.Backend.ClosToBvl
