module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.MtiFreeVars
public import Flapjack.Compiler.Backend.ClosMti.Proofs.TotalView

@[expose] public section

/-! Free-variable preservation by multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosProps ClosLang

/-- Flapjack infrastructure: singleton preservation for the list-relation proof. -/
private theorem introExpFree (m : Nat) (e : ClosLang.Exp) (v : Nat) :
    freeVarExp v (ClosMti.introExp m e) ↔ freeVarExp v e := by
  have listIH (xs : List ClosLang.Exp) (bound : listBudget xs < expBudget e) (z : Nat) :
      freeVars z (ClosMti.introList m xs) ↔ freeVars z xs := by
    induction xs with
    | nil => simp [ClosMti.introList, freeVars]
    | cons head tail ih =>
      have headBound : expBudget head < expBudget e := by simp only [listBudget] at bound; omega
      have tailBound : listBudget tail < expBudget e := by simp only [listBudget] at bound; omega
      simp only [ClosMti.introList_cons, freeVars, introExpFree m head z, ih tailBound]
  cases e with
  | var t n => simp [ClosMti.introExp_var, freeVarExp]
  | ifThenElse t a b c =>
    simp [ClosMti.introExp_if, freeVarExp, introExpFree m a v,
      introExpFree m b v, introExpFree m c v]
  | «let» t xs body =>
    have hxs := listIH xs (by simp [expBudget]; omega) v
    simp [ClosMti.introExp_let, freeVarExp, hxs, ClosMti.introList_length, introExpFree m body]
  | raise t body => simp [ClosMti.introExp_raise, freeVarExp, introExpFree m body v]
  | tick t body => simp [ClosMti.introExp_tick, freeVarExp, introExpFree m body v]
  | handle t body handler =>
    simp [ClosMti.introExp_handle, freeVarExp, introExpFree m body, introExpFree m handler]
  | call t ticks dest args =>
    have hargs := listIH args (by simp [expBudget]) v
    simp [ClosMti.introExp_call, freeVarExp, hargs]
  | op t op args =>
    have hargs := listIH args (by simp [expBudget]) v
    simp [ClosMti.introExp_op, freeVarExp, hargs]
  | app t loc body args =>
    cases loc with
    | some loc =>
      have hargs := listIH args (by simp [expBudget]; omega) v
      simp [ClosMti.introExp_app_some, freeVarExp, hargs, introExpFree m body v]
    | none =>
      cases found : ClosMti.collectApps m args body with
      | mk collected head =>
        have bounds := ClosMti.collectApps_budget m args body
        rw [found] at bounds
        change listBudget collected + expBudget head ≤ listBudget args + expBudget body at bounds
        have hargs := listIH collected (by simp [expBudget]; omega) v
        have hhead := introExpFree m head v
        have collector := collectApps_freeVars m args body v
        rw [found] at collector
        simpa [ClosMti.introExp_app_none, found, freeVar, freeVars, freeVarExp,
          hargs, hhead, or_assoc, or_left_comm, or_comm] using collector
  | fn name loc vs arity body =>
    cases loc with
    | some loc =>
      simp [ClosMti.introExp_fn_location, freeVarExp, introExpFree m body]
    | none =>
      cases vs with
      | some vs => simp [ClosMti.introExp_fn_vars, freeVarExp, introExpFree m body]
      | none =>
        cases found : ClosMti.collectArgs m arity body with
        | mk count head =>
          have bounds := ClosMti.collectArgs_budget m arity body
          rw [found] at bounds
          change expBudget head ≤ expBudget body at bounds
          have hh := introExpFree m head (v + count)
          have collector := collectArgs_freeVar m arity body count head v found
          simpa [ClosMti.introExp_fn_none, found, freeVar, freeVars, freeVarExp,
            hh, Nat.add_comm] using collector
  | letrec names loc vs fns body =>
    cases loc with
    | some loc =>
      simp [ClosMti.introExp_letrec_location, freeVarExp, introExpFree m body]
    | none =>
      cases vs with
      | some vs => simp [ClosMti.introExp_letrec_vars, freeVarExp, introExpFree m body]
      | none =>
        have funsIH (fs : List (Nat × ClosLang.Exp))
            (bound : funsBudget fs < expBudget (.letrec names none none fns body))
            (count index : Nat) :
            freeVarFuns index count (fs.map (ClosMti.introFun m)) ↔
              freeVarFuns index count fs := by
          induction fs with
          | nil => simp [freeVarFuns]
          | cons first rest ih =>
            obtain ⟨arity, functionBody⟩ := first
            have headBound : expBudget functionBody < expBudget (.letrec names none none fns body) := by
              simp only [funsBudget] at bound; omega
            have tailBound : funsBudget rest < expBudget (.letrec names none none fns body) := by
              simp only [funsBudget] at bound; omega
            cases found : ClosMti.collectArgs m arity functionBody with
            | mk newArity head =>
              have hb := ClosMti.collectArgs_budget m arity functionBody
              rw [found] at hb
              change expBudget head ≤ expBudget functionBody at hb
              have headIH := introExpFree m head (index + newArity + count)
              have collector := collectArgs_freeVar m arity functionBody newArity head (index + count) found
              simp only [freeVar, freeVars, or_false] at collector
              have result : freeVarExp (index + newArity + count) (ClosMti.introExp m head) ↔
                  freeVarExp (index + arity + count) functionBody := by
                rw [headIH]
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using collector
              simp [ClosMti.introFun, found, freeVarFuns, result, ih tailBound]
        have funcs := funsIH fns (by simp [expBudget]; omega) fns.length v
        simp [ClosMti.introExp_letrec_none, freeVarExp, funcs, introExpFree m body]

termination_by expBudget e
decreasing_by
  all_goals simp_all [expBudget]
  all_goals omega

/-- Multi-argument introduction preserves every free-variable predicate pointwise. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "intro_multi_fv1"]
theorem introMulti_freeVar (m : Nat) (es : List ClosLang.Exp) :
    List.Forall₂ (fun e1 e2 => ∀ v, freeVar v e1 ↔ freeVar v e2)
      (ClosMti.introList m es) es := by
  induction es with
  | nil => simp [ClosMti.introList]
  | cons e es ih =>
    simp only [ClosMti.introList_cons, List.forall₂_cons]
    refine ⟨?_, ih⟩
    intro v
    simpa [freeVar, freeVars] using introExpFree m e v
end Flapjack.Compiler.Backend.ClosToBvl
