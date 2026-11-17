module

public import Flapjack.TypeSysProps.Abbrev
public import Flapjack.TypeSystemHOL.Patterns

@[expose] public section

/-! Free-variable bounds for declarative pattern typing. -/
namespace Flapjack.TypeSysProps
open Flapjack Flapjack.TypeSystemHOL Flapjack.Basis.Pure.MlString Flapjack.AstHOL

/-- Pattern and pattern-list typing contain only permitted free variables. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "type_p_freevars"]
theorem typePFreevars :
    (∀ tvs env p t bindings, TypeP tvs env p t bindings →
      checkFreevars tvs [] t = true ∧ (bindings.map Prod.snd).all (checkFreevars tvs []) = true) ∧
    (∀ tvs env ps ts bindings, TypePs tvs env ps ts bindings →
      ts.all (checkFreevars tvs []) = true ∧ (bindings.map Prod.snd).all (checkFreevars tvs []) = true) := by
  constructor <;> intro tvs env p t bindings typed
  all_goals
    first
    | refine TypeP.rec (motive_1 := fun p t bindings _ =>
          checkFreevars tvs [] t = true ∧ (bindings.map Prod.snd).all (checkFreevars tvs []) = true)
        (motive_2 := fun ps ts bindings _ =>
          ts.all (checkFreevars tvs []) = true ∧ (bindings.map Prod.snd).all (checkFreevars tvs []) = true)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
    | refine TypePs.rec (motive_1 := fun p t bindings _ =>
          checkFreevars tvs [] t = true ∧ (bindings.map Prod.snd).all (checkFreevars tvs []) = true)
        (motive_2 := fun ps ts bindings _ =>
          ts.all (checkFreevars tvs []) = true ∧ (bindings.map Prod.snd).all (checkFreevars tvs []) = true)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
    all_goals try simp_all [checkFreevars, checkFreevarsListEqAll, Ttup, Tref,
      Tint, Tchar, Tstring, Tword8, Tword64, List.all_append]
    all_goals intros; constructor <;> assumption

end Flapjack.TypeSysProps
