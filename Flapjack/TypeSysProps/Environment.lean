module

public import Flapjack.TypeSoundInvariants
public import Flapjack.TypeSystemHOL.Declarations
public import Flapjack.NamespaceProps

@[expose] public section

/-! Well-formed declarative environments are closed under extension. -/
namespace Flapjack.TypeSysProps
open Flapjack.NamespaceHOL Flapjack.TypeSystemHOL Flapjack.TypeSoundInvariants
  Flapjack.Basis.Pure.MlString Flapjack.AstHOL

/-- Binding names does not change the number of local type variables. This is
a local unfolding of the HOL definitions used in the function-list proof. -/
private theorem numTvsBind (bindings : List (MlString × SemanticT)) (env : TenvValExp) :
    numTvs (bindVarList 0 bindings env) = numTvs env := by
  induction bindings with
  | nil => simp [bindVarList]
  | cons entry rest ih =>
    rcases entry with ⟨name, ty⟩
    simp [bindVarList, numTvs, ih]

/-- Well-typed function bindings preserve the local value-environment
invariant when they are added at de Bruijn level zero. The unused polymorphic
binder is present in the HOL theorem and is retained here. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tenv_val_exp_ok_bvl_funs"]
theorem tenvValExpOkBvlFuns {α : Type} (funs : List (MlString × MlString × Flapjack.AstHOL.Exp))
    (output : List (MlString × SemanticT)) (env : TypeEnv)
    (bindings : List (MlString × SemanticT)) (_tenvVal : α) (localEnv : TenvValExp) :
    TypeFuns env (bindVarList 0 bindings localEnv) funs output ∧ tenvValExpOk localEnv →
      tenvValExpOk (bindVarList 0 output localEnv) := by
  intro ⟨typed, ok⟩
  induction funs generalizing output with
  | nil =>
    cases typed
    simpa [bindVarList] using ok
  | cons first rest ih =>
    cases typed with
    | cons envE name arg body funs binds t1 t2 free typed tail unique =>
      simp only [bindVarList, tenvValExpOk, numTvsBind, Nat.zero_add]
      refine ⟨?_, ih _ tail⟩
      simpa [numTvsBind] using free

@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "extend_dec_tenv_ok"]
theorem extendDecTenvOk (tenv tenv' : TypeEnv)
    (h : tenvOk tenv ∧ tenvOk tenv') : tenvOk (extendDecTenv tenv tenv') := by
  refine ⟨?_, ?_, ?_⟩
  · exact nsAll_nsAppend _ _ _ ⟨h.1.1, h.2.1⟩
  · exact nsAll_nsAppend _ _ _ ⟨h.1.2.1, h.2.2.1⟩
  · exact nsAll_nsAppend _ _ _ ⟨h.1.2.2, h.2.2.2⟩

end Flapjack.TypeSysProps
