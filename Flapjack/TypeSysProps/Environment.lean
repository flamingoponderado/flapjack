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

/-- Appending an empty-namespace extension of a local environment is the same
as extending the target namespace directly. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "add_tenvE_nsAppend"]
theorem addTenvE_nsAppend {M : Type} (localEnv : TenvValExp)
    (env : Namespace M MlString (Nat × SemanticT)) :
    nsAppend (addTenvE localEnv nsEmpty) env = addTenvE localEnv env := by
  have appendBind : ∀ {M : Type} (name : MlString) (value : Nat × SemanticT)
      (rest other : Namespace M MlString (Nat × SemanticT)),
      nsAppend (nsBind name value rest) other = nsBind name value (nsAppend rest other) := by
    intro M name value rest other
    cases rest with
    | bind vs ms =>
      cases other with
      | bind vs' ms' => simp [nsBind, nsAppend]
  induction localEnv with
  | empty =>
    cases env with
    | bind vs ms => simp [addTenvE, nsAppend, nsEmpty]
  | bindTvar _ rest ih =>
    simp only [addTenvE]
    exact ih
  | bindName name tvs t rest ih =>
    simp only [addTenvE]
    rw [appendBind name (tvs, t), ih]

/-- The empty declaration list types exactly the empty type-id set and the
empty environment. -/
@[simp, hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "type_ds_empty"]
theorem typeDsEmpty (extra : Bool) (tenv : TypeEnv) (ids : TypeIds) (r : TypeEnv) :
    TypeDs extra tenv [] ids r ↔ ids = (fun _ => False) ∧ r = ⟨nsEmpty, nsEmpty, nsEmpty⟩ := by
  constructor
  · intro typed
    cases typed
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact TypeDs.nil extra tenv

/-- Extending a declaration environment is associative. -/
@[simp, hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "extend_dec_tenv_assoc"]
theorem extendDecTenv_assoc (tenv1 tenv2 tenv3 : TypeEnv) :
    extendDecTenv tenv1 (extendDecTenv tenv2 tenv3) =
      extendDecTenv (extendDecTenv tenv1 tenv2) tenv3 := by
  simp [extendDecTenv, nsAppend_assoc]

/-- Appending two abbreviation environments preserves well-formedness. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tenv_abbrev_ok_merge"]
theorem tenvAbbrevOk_merge {M N : Type} (env1 env2 : Namespace M N (List MlString × SemanticT)) :
    tenvAbbrevOk env1 ∧ tenvAbbrevOk env2 → tenvAbbrevOk (nsAppend env1 env2) := by
  intro h
  exact nsAll_nsAppend _ _ _ h

/-- Appending two constructor environments preserves well-formedness. -/
@[simp, hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tenv_ctor_ok_merge"]
theorem tenvCtorOk_merge {M N Tag : Type}
    (env1 env2 : Namespace M N (List MlString × List SemanticT × Tag)) :
    tenvCtorOk env1 ∧ tenvCtorOk env2 → tenvCtorOk (nsAppend env1 env2) := by
  intro h
  exact nsAll_nsAppend _ _ _ h

/-- A short lookup found by the local environment survives adding local
bindings, provided its type satisfies the local bound. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "nsLookup_add_tenvE1"]
theorem nsLookup_addTenvE1 {M : Type} [DecidableEq M] (localEnv : TenvValExp)
    (env : Namespace M MlString (Nat × SemanticT)) (n : MlString) (tvs tvs2 : Nat)
    (t : SemanticT) :
    checkFreevars tvs2 [] t = true ∧ tveLookup n tvs localEnv = some (tvs2, t) →
      nsLookup (addTenvE localEnv env) (.short n) = some (tvs2, t) := by
  intro h
  induction localEnv generalizing tvs with
  | empty => cases h.2
  | bindTvar bound rest ih =>
    simp only [tveLookup] at h
    simp only [addTenvE]
    exact ih _ h
  | bindName name bound ty rest ih =>
    by_cases same : name = n
    · rw [← same] at h ⊢
      simp only [tveLookup] at h
      obtain ⟨rfl, rfl⟩ := Option.some.inj h.2
      simp only [addTenvE]
      rw [nsLookup_nsBind.1 name (tvs2, ty) (addTenvE rest env)]
      rw [nil_deBruijnInc tvs2 tvs ty (Or.inr h.1)]
    · simp only [tveLookup] at h
      have restFound := ih _ ⟨h.1, by simpa [same] using h.2⟩
      have different : (Ident.short n : Ident M MlString) ≠ Ident.short name := by
        intro h
        exact same (by simpa using h.symm)
      simp only [addTenvE]
      rw [nsLookup_nsBind.2 (Ident.short n) name (bound, ty) (addTenvE rest env) different]
      exact restFound

/-- A short lookup missed by the local environment survives adding local
bindings. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "nsLookup_add_tenvE2"]
theorem nsLookup_addTenvE2 {M : Type} [DecidableEq M] (localEnv : TenvValExp)
    (env : Namespace M MlString (Nat × SemanticT)) (n : MlString) (tvs tvs2 : Nat)
    (t : SemanticT) :
    tveLookup n tvs localEnv = none ∧ nsLookup env (.short n) = some (tvs2, t) →
      nsLookup (addTenvE localEnv env) (.short n) = some (tvs2, t) := by
  intro h
  induction localEnv generalizing tvs with
  | empty => exact h.2
  | bindTvar bound rest ih =>
    simp only [tveLookup] at h
    simp only [addTenvE]
    exact ih _ h
  | bindName name bound ty rest ih =>
    by_cases same : name = n
    · rw [← same] at h ⊢
      simp only [tveLookup] at h
      simp at h
    · simp only [tveLookup] at h
      have restFound := ih _ ⟨by simpa [same] using h.1, h.2⟩
      have different : (Ident.short n : Ident M MlString) ≠ Ident.short name := by
        intro h
        exact same (by simpa using h.symm)
      simp only [addTenvE]
      rw [nsLookup_nsBind.2 (Ident.short n) name (bound, ty) (addTenvE rest env) different]
      exact restFound

/-- A qualified lookup found in the environment survives adding local bindings. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "nsLookup_add_tenvE3"]
theorem nsLookup_addTenvE3 {M : Type} [DecidableEq M] (localEnv : TenvValExp)
    (env : Namespace M MlString (Nat × SemanticT)) (n : Ident M MlString) (t : SemanticT)
    (tvs2 : Nat) (mn : M) :
    nsLookup env (.long mn n) = some (tvs2, t) →
      nsLookup (addTenvE localEnv env) (.long mn n) = some (tvs2, t) := by
  intro found
  induction localEnv with
  | empty => exact found
  | bindTvar bound rest ih =>
    simp only [addTenvE]
    exact ih
  | bindName name bound ty rest ih =>
    have different : (Ident.long mn n : Ident M MlString) ≠ Ident.short name := by
      intro h
      cases h
    simp only [addTenvE]
    rw [nsLookup_nsBind.2 (Ident.long mn n) name (bound, ty) (addTenvE rest env) different]
    exact ih

end Flapjack.TypeSysProps
