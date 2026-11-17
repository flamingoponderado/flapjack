module

public import Flapjack.TypeSoundInvariants
public import Flapjack.TypeSystemHOL.Declarations
public import Flapjack.NamespaceProps
public import Flapjack.TypeSysProps.Freevars

@[expose] public section

/-! Well-formed declarative environments are closed under extension. -/
namespace Flapjack.TypeSysProps
open Flapjack.NamespaceHOL Flapjack.TypeSystemHOL Flapjack.TypeSoundInvariants
  Flapjack.Basis.Pure.MlString Flapjack.AstHOL

/-- Binding names does not change the number of local type variables. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "num_tvs_bind_var_list"]
theorem numTvsBindVarList (tvs : Nat) (bindings : List (MlString × SemanticT)) (env : TenvValExp) :
    numTvs (bindVarList tvs bindings env) = numTvs env := by
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
      simp only [bindVarList, tenvValExpOk, numTvsBindVarList, Nat.zero_add]
      refine ⟨?_, ih _ tail⟩
      simpa [numTvsBindVarList] using free

/-- Adding well-formed monomorphic bindings preserves the local environment
invariant. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tenv_val_exp_ok_bvl"]
theorem tenvValExpOkBvl (localEnv : TenvValExp) (bindings : List (MlString × SemanticT)) :
    tenvValExpOk localEnv ∧ (bindings.map Prod.snd).all (checkFreevars (numTvs localEnv) []) = true →
      tenvValExpOk (bindVarList 0 bindings localEnv) := by
  intro ⟨ok, checks⟩
  induction bindings with
  | nil => simpa [bindVarList] using ok
  | cons entry rest ih =>
    rcases entry with ⟨name, ty⟩
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at checks
    simp only [bindVarList, tenvValExpOk, numTvsBindVarList, Nat.zero_add]
    exact ⟨checks.1, ih checks.2⟩

/-- Instantiating a value found in a well-formed local environment preserves
the free-variable bound. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tveLookup_freevars_subst"]
theorem tveLookupFreevarsSubst (localEnv : TenvValExp) (args : List SemanticT) (name : MlString)
    (t : SemanticT) (inc : Nat) :
    args.all (checkFreevars (inc + numTvs localEnv) []) = true ∧
    tveLookup name inc localEnv = some (args.length, t) ∧ tenvValExpOk localEnv →
      checkFreevars (inc + numTvs localEnv) [] (deBruijnSubst 0 args t) = true := by
  induction localEnv generalizing inc t with
  | empty => simp [tveLookup]
  | bindTvar tvs rest ih =>
    intro ⟨all, found, ok⟩
    simp only [numTvs, tveLookup, tenvValExpOk] at all found ok ⊢
    simpa [Nat.add_assoc] using ih t (inc + tvs) ⟨by simpa [Nat.add_assoc] using all, found, ok⟩
  | bindName boundName tvs ty rest ih =>
    intro ⟨all, found, ok⟩
    simp only [numTvs, tveLookup, tenvValExpOk] at all found ok ⊢
    by_cases same : boundName = name
    · simp [same] at found
      obtain ⟨rfl, rfl⟩ := found
      apply checkFreevarsSubstInc _ [] ty ok.1 (numTvs rest) args inc
      exact ⟨rfl, all⟩
    · simp [same] at found
      exact ih t inc ⟨all, found, ok.2⟩

@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "extend_dec_tenv_ok"]
theorem extendDecTenvOk (tenv tenv' : TypeEnv)
    (h : tenvOk tenv ∧ tenvOk tenv') : tenvOk (extendDecTenv tenv tenv') := by
  refine ⟨?_, ?_, ?_⟩
  · exact nsAll_nsAppend _ _ _ ⟨h.1.1, h.2.1⟩
  · exact nsAll_nsAppend _ _ _ ⟨h.1.2.1, h.2.2.1⟩
  · exact nsAll_nsAppend _ _ _ ⟨h.1.2.2, h.2.2.2⟩

end Flapjack.TypeSysProps
