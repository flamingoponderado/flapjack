module

public import Flapjack.Compiler.Backend.ClosFvs.Source
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic
public import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.FreeVars
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Globals
public import Flapjack.Compiler.Backend.ClosFvs.Proofs.Production

@[expose] public section

/-! Syntactic invariants of closure free-variable cleanup. -/
namespace Flapjack.Compiler.Backend.ClosFvs
open ClosLang ClosProps

mutual

/-- Free-variable cleanup preserves absent capture annotations on an
expression. This helper has no standalone HOL declaration. -/
theorem removeSing_varsNone (expression : Exp) (bound : Nat) :
    fnVarsNoneExp (removeSing bound expression) ↔ fnVarsNoneExp expression := by
  cases expression with
  | var trace n => simp [removeSing, fnVarsNoneExp]; split <;> simp [fnVarsNoneExp, everyFnVarsNone]
  | ifThenElse trace condition yes no =>
    simp [removeSing, fnVarsNoneExp, removeSing_varsNone condition, removeSing_varsNone yes, removeSing_varsNone no]
  | «let» trace bindings body =>
    simp [removeSing, fnVarsNoneExp, removeList_varsNone bindings, removeSing_varsNone body]
  | raise trace body => simp [removeSing, fnVarsNoneExp, removeSing_varsNone body]
  | handle trace body handler =>
    simp [removeSing, fnVarsNoneExp, removeSing_varsNone body, removeSing_varsNone handler]
  | tick trace body => simp [removeSing, fnVarsNoneExp, removeSing_varsNone body]
  | call trace ticks location args => simp [removeSing, fnVarsNoneExp, removeList_varsNone args]
  | app trace location function args =>
    simp [removeSing, fnVarsNoneExp, removeSing_varsNone function, removeList_varsNone args]
  | fn name location vars arity body => simp [removeSing, fnVarsNoneExp, removeSing_varsNone body]
  | letrec names location vars functions body =>
    simp [removeSing, fnVarsNoneExp, removeFuns_varsNone functions, removeSing_varsNone body]
  | op trace op args => simp [removeSing, fnVarsNoneExp, removeList_varsNone args]
termination_by sizeOf expression

/-- Cleanup preserves absent capture annotations in an expression list. -/
theorem removeList_varsNone (expressions : List Exp) (bound : Nat) :
    everyFnVarsNone (removeList bound expressions) ↔ everyFnVarsNone expressions := by
  cases expressions with
  | nil => simp [removeList, everyFnVarsNone]
  | cons first rest =>
    simp [removeList, everyFnVarsNone, removeSing_varsNone first, removeList_varsNone rest]
termination_by sizeOf expressions

/-- The same invariant for recursive function bundles. This helper has no
standalone HOL declaration. -/
theorem removeFuns_varsNone (functions : List (Nat × Exp)) (count captured : Nat) :
    fnVarsNoneFuns (removeFuns count captured functions) ↔ fnVarsNoneFuns functions := by
  cases functions with
  | nil => simp [removeFuns, fnVarsNoneFuns]
  | cons first rest =>
    cases first with
    | mk arity body =>
      simp [removeFuns, fnVarsNoneFuns, removeSing_varsNone body, removeFuns_varsNone rest]
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega

end

mutual

/-- Free-variable cleanup preserves present function locations on an
expression. This helper has no standalone HOL declaration. -/
theorem removeSing_locations (expression : Exp) (bound : Nat) :
    fnLocationSomeExp (removeSing bound expression) ↔ fnLocationSomeExp expression := by
  cases expression with
  | var trace n => simp [removeSing, fnLocationSomeExp]; split <;> simp [fnLocationSomeExp, everyFnLocationSome]
  | ifThenElse trace condition yes no =>
    simp [removeSing, fnLocationSomeExp, removeSing_locations condition, removeSing_locations yes, removeSing_locations no]
  | «let» trace bindings body =>
    simp [removeSing, fnLocationSomeExp, removeList_locations bindings, removeSing_locations body]
  | raise trace body => simp [removeSing, fnLocationSomeExp, removeSing_locations body]
  | handle trace body handler =>
    simp [removeSing, fnLocationSomeExp, removeSing_locations body, removeSing_locations handler]
  | tick trace body => simp [removeSing, fnLocationSomeExp, removeSing_locations body]
  | call trace ticks location args => simp [removeSing, fnLocationSomeExp, removeList_locations args]
  | app trace location function args =>
    simp [removeSing, fnLocationSomeExp, removeSing_locations function, removeList_locations args]
  | fn name location vars arity body => simp [removeSing, fnLocationSomeExp, removeSing_locations body]
  | letrec names location vars functions body =>
    simp [removeSing, fnLocationSomeExp, removeFuns_locations functions, removeSing_locations body]
  | op trace op args => simp [removeSing, fnLocationSomeExp, removeList_locations args]
termination_by sizeOf expression

/-- Cleanup preserves present function locations in an expression list. -/
theorem removeList_locations (expressions : List Exp) (bound : Nat) :
    everyFnLocationSome (removeList bound expressions) ↔ everyFnLocationSome expressions := by
  cases expressions with
  | nil => simp [removeList, everyFnLocationSome]
  | cons first rest =>
    simp [removeList, everyFnLocationSome, removeSing_locations first, removeList_locations rest]
termination_by sizeOf expressions

/-- The same invariant for recursive function bundles. This helper has no
standalone HOL declaration. -/
theorem removeFuns_locations (functions : List (Nat × Exp)) (count captured : Nat) :
    fnLocationSomeFuns (removeFuns count captured functions) ↔ fnLocationSomeFuns functions := by
  cases functions with
  | nil => simp [removeFuns, fnLocationSomeFuns]
  | cons first rest =>
    cases first with
    | mk arity body =>
      simp [removeFuns, fnLocationSomeFuns, removeSing_locations body, removeFuns_locations rest]
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega

end

mutual

/-- Cleanup preserves the global-write bag of an expression. This helper has
no standalone HOL declaration. -/
theorem removeSing_globals (expression : Exp) (bound : Nat) :
    setGlobals (removeSing bound expression) = setGlobals expression := by
  cases expression with
  | var trace index =>
    by_cases inside : index < bound <;>
      simp [removeSing, inside, setGlobals, opGlobalBag, elistGlobals,
        FlatProps.unionGlobalBag_eq_empty]
  | ifThenElse trace condition yes no =>
    simp [removeSing, setGlobals, removeSing_globals condition, removeSing_globals yes, removeSing_globals no]
  | «let» trace bindings body =>
    simp [removeSing, setGlobals, removeList_globals bindings, removeSing_globals body]
  | raise trace body => simp [removeSing, setGlobals, removeSing_globals body]
  | handle trace body handler => simp [removeSing, setGlobals, removeSing_globals body, removeSing_globals handler]
  | tick trace body => simp [removeSing, setGlobals, removeSing_globals body]
  | call trace ticks location args => simp [removeSing, setGlobals, removeList_globals args]
  | app trace location function args =>
    simp [removeSing, setGlobals, removeSing_globals function, removeList_globals args]
  | fn name location vars arity body => simp [removeSing, setGlobals, removeSing_globals body]
  | letrec names location vars functions body =>
    simp [removeSing, setGlobals, removeFuns_globals functions, removeSing_globals body]
  | op trace op args => simp [removeSing, setGlobals, removeList_globals args]
termination_by sizeOf expression

/-- Cleanup preserves the combined global-write bag of an expression list. -/
theorem removeList_globals (expressions : List Exp) (bound : Nat) :
    elistGlobals (removeList bound expressions) = elistGlobals expressions := by
  cases expressions with
  | nil => simp [removeList, elistGlobals]
  | cons first rest => simp [removeList, elistGlobals, removeSing_globals first, removeList_globals rest]
termination_by sizeOf expressions

/-- Cleanup preserves the global-write bag of recursive bodies. This helper
has no standalone HOL declaration. -/
theorem removeFuns_globals (functions : List (Nat × Exp)) (count captured : Nat) :
    funGlobals (removeFuns count captured functions) = funGlobals functions := by
  cases functions with
  | nil => simp [removeFuns, funGlobals]
  | cons first rest =>
    cases first with
    | mk arity body => simp [removeFuns, funGlobals, removeSing_globals body, removeFuns_globals rest]
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega

end

/-- Cleanup preserves each expression's global-write bag, in order. -/
theorem removeList_setGlobals (expressions : List Exp) (bound : Nat) :
    (removeList bound expressions).map setGlobals = expressions.map setGlobals := by
  induction expressions with
  | nil => rfl
  | cons first rest ih => simp [removeList, removeSing_globals, ih]

mutual

/-- Cleanup preserves global-write safety of an expression. This helper has
no standalone HOL declaration. -/
theorem removeSing_esgcFree (expression : Exp) (bound : Nat) :
    esgcFree (removeSing bound expression) ↔ esgcFree expression := by
  cases expression with
  | var trace index =>
    by_cases inside : index < bound <;> simp [removeSing, inside, esgcFree, esgcFreeList]
  | ifThenElse trace condition yes no =>
    simp [removeSing, esgcFree, removeSing_esgcFree condition, removeSing_esgcFree yes, removeSing_esgcFree no]
  | «let» trace bindings body =>
    simp [removeSing, esgcFree, removeList_esgcFree bindings, removeSing_esgcFree body]
  | raise trace body => simp [removeSing, esgcFree, removeSing_esgcFree body]
  | handle trace body handler => simp [removeSing, esgcFree, removeSing_esgcFree body, removeSing_esgcFree handler]
  | tick trace body => simp [removeSing, esgcFree, removeSing_esgcFree body]
  | call trace ticks location args => simp [removeSing, esgcFree, removeList_esgcFree args]
  | app trace location function args =>
    simp [removeSing, esgcFree, removeSing_esgcFree function, removeList_esgcFree args]
  | fn name location vars arity body => simp [removeSing, esgcFree, removeSing_globals body]
  | letrec names location vars functions body =>
    simp [removeSing, esgcFree, removeFuns_globals functions, removeSing_esgcFree body]
  | op trace op args => simp [removeSing, esgcFree, removeList_esgcFree args]
termination_by sizeOf expression

/-- Cleanup preserves global-write safety over expression lists. -/
theorem removeList_esgcFree (expressions : List Exp) (bound : Nat) :
    esgcFreeList (removeList bound expressions) ↔ esgcFreeList expressions := by
  cases expressions with
  | nil => simp [removeList, esgcFreeList]
  | cons first rest => simp [removeList, esgcFreeList, removeSing_esgcFree first, removeList_esgcFree rest]
termination_by sizeOf expressions

end

mutual

/-- Cleanup bounds the free variables of an expression with absent capture
annotations. This helper has no standalone HOL declaration. -/
theorem removeSing_fvMax (expression : Exp) (bound : Nat) (safe : fnVarsNoneExp expression) :
    ClosKnown.fvMax bound [removeSing bound expression] := by
  cases expression with
  | var trace index =>
    by_cases inside : index < bound
    · simp [removeSing, ClosKnown.fvMaxVar, inside]
    · simp [removeSing, inside, ClosKnown.fvMax, freeVars, freeVarExp]
  | ifThenElse trace condition yes no =>
    simp only [fnVarsNoneExp] at safe
    simp only [removeSing, ClosKnown.fvMax, freeVars, freeVarExp, or_false, or_imp, forall_and]
    simpa [ClosKnown.fvMax, freeVars] using
      And.intro (removeSing_fvMax condition bound safe.1)
        (And.intro (removeSing_fvMax yes bound safe.2.1) (removeSing_fvMax no bound safe.2.2))
  | «let» trace bindings body =>
    simp only [fnVarsNoneExp] at safe
    rw [removeSing, ClosKnown.fvMaxLet]
    exact ⟨removeList_fvMax bindings bound safe.2, removeSing_fvMax body _ safe.1⟩
  | raise trace body =>
    simpa [removeSing, ClosKnown.fvMax, freeVars, freeVarExp] using
      removeSing_fvMax body bound (by simpa [fnVarsNoneExp] using safe)
  | tick trace body =>
    simpa [removeSing, ClosKnown.fvMax, freeVars, freeVarExp] using
      removeSing_fvMax body bound (by simpa [fnVarsNoneExp] using safe)
  | handle trace body handler =>
    simp only [fnVarsNoneExp] at safe
    rw [removeSing, ClosKnown.fvMaxHandle]
    exact ⟨removeSing_fvMax body bound safe.1, removeSing_fvMax handler _ safe.2⟩
  | call trace ticks location args =>
    simpa [removeSing, ClosKnown.fvMax, freeVars, freeVarExp] using
      removeList_fvMax args bound (by simpa [fnVarsNoneExp] using safe)
  | op trace op args =>
    simpa [removeSing, ClosKnown.fvMax, freeVars, freeVarExp] using
      removeList_fvMax args bound (by simpa [fnVarsNoneExp] using safe)
  | app trace location function args =>
    simp only [fnVarsNoneExp] at safe
    simp only [removeSing, ClosKnown.fvMax, freeVars, freeVarExp, or_false, or_imp, forall_and]
    simpa [ClosKnown.fvMax, freeVars] using
      And.intro (removeSing_fvMax function bound safe.1) (removeList_fvMax args bound safe.2)
  | fn name location vars arity body =>
    simp only [fnVarsNoneExp] at safe
    have varsEq := safe.1
    subst vars
    rw [removeSing, ClosKnown.fvMaxFn]
    simpa [Nat.add_comm] using removeSing_fvMax body (arity + bound) safe.2
  | letrec names location vars functions body =>
    simp only [fnVarsNoneExp] at safe
    have varsEq := safe.1
    subst vars
    rw [removeSing, ClosKnown.fvMaxLetrec]
    constructor
    · simpa [removeFuns_length] using removeFuns_fvMax functions functions.length bound safe.2.1
    · simpa [removeFuns_length, Nat.add_comm] using removeSing_fvMax body (functions.length + bound) safe.2.2
termination_by sizeOf expression

/-- Cleanup bounds all free variables in a list of safely annotated
expressions. -/
theorem removeList_fvMax (expressions : List Exp) (bound : Nat) (safe : everyFnVarsNone expressions) :
    ClosKnown.fvMax bound (removeList bound expressions) := by
  cases expressions with
  | nil => simp [removeList, ClosKnown.fvMax, freeVars]
  | cons first rest =>
    simp only [everyFnVarsNone] at safe
    rw [removeList, ClosKnown.fvMaxCons]
    exact ⟨removeSing_fvMax first bound safe.1, removeList_fvMax rest bound safe.2⟩
termination_by sizeOf expressions

/-- Cleanup bounds all bodies in a recursive function bundle. This helper has
no standalone HOL declaration. -/
theorem removeFuns_fvMax (functions : List (Nat × Exp)) (count captured : Nat)
    (safe : fnVarsNoneFuns functions) :
    ∀ p ∈ removeFuns count captured functions, ClosKnown.fvMax (captured + p.1 + count) [p.2] := by
  cases functions with
  | nil => simp [removeFuns]
  | cons first rest =>
    cases first with
    | mk arity body =>
      simp only [fnVarsNoneFuns] at safe
      simp only [removeFuns, List.mem_cons, forall_eq_or_imp]
      constructor
      · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          removeSing_fvMax body (arity + count + captured) safe.1
      · exact removeFuns_fvMax rest count captured safe.2
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega

end

/-- The singleton removal result satisfies EVERY exactly when its head does. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "EVERY_remove_fvs_sing"]
theorem every_removeSource_sing (f : Exp → Prop) (n : Nat) (y : Exp) :
    (∀ e ∈ removeSource n [y], f e) ↔
      f (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource n [y])) := by
  simp [removeSource_eq_list, removeList, Flapjack.holHd]

/-- The original list-shaped removal satisfies the HOL invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "remove_fvs_every_Fn_vs_NONE"]
theorem removeSource_varsNone (bound : Nat) (expressions : List Exp) :
    everyFnVarsNone (removeSource bound expressions) ↔ everyFnVarsNone expressions := by
  simpa using removeList_varsNone expressions bound

/-- The original list-shaped removal satisfies the HOL invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "remove_fvs_every_Fn_SOME"]
theorem removeSource_locations (bound : Nat) (expressions : List Exp) :
    everyFnLocationSome (removeSource bound expressions) ↔ everyFnLocationSome expressions := by
  simpa using removeList_locations expressions bound

/-- The original list-shaped removal satisfies the HOL invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "remove_fvs_elist_globals"]
theorem removeSource_globals (bound : Nat) (expressions : List Exp) :
    elistGlobals (removeSource bound expressions) = elistGlobals expressions := by
  simpa using removeList_globals expressions bound

/-- The original list-shaped removal satisfies the HOL invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "remove_fvs_set_globals"]
theorem removeSource_setGlobals (bound : Nat) (expressions : List Exp) :
    (removeSource bound expressions).map setGlobals = expressions.map setGlobals := by
  simpa using removeList_setGlobals expressions bound

/-- Removing free variables from a singleton preserves its head's globals. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "set_globals_HD_remove_fvs_SING"]
theorem setGlobals_head_removeSource_sing (bound : Nat) (expression : Exp) :
    setGlobals (@Flapjack.holHd Exp ⟨.var .none 0⟩ (removeSource bound [expression])) =
      setGlobals expression := by
  have h := removeSource_setGlobals bound [expression]
  simpa [removeSource_eq_list, removeList, Flapjack.holHd] using h

/-- The original list-shaped removal satisfies the HOL invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "remove_fvs_esgc_free"]
theorem removeSource_esgcFree (bound : Nat) (expressions : List Exp) :
    (∀ e ∈ removeSource bound expressions, esgcFree e) ↔ ∀ e ∈ expressions, esgcFree e := by
  simpa [esgcFreeList_iff] using removeList_esgcFree expressions bound

/-- The original list-shaped removal satisfies the HOL invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "fv_max_remove_fvs"]
theorem removeSource_fvMax (bound : Nat) (expressions : List Exp) (safe : everyFnVarsNone expressions) :
    ∀ v, freeVars v (removeSource bound expressions) → v < bound := by
  simpa [ClosKnown.fvMax] using removeList_fvMax expressions bound safe

end Flapjack.Compiler.Backend.ClosFvs
