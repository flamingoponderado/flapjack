module

public import Flapjack.Compiler.Backend.ClosNumber.Proofs.VarsNone
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Globals

@[expose] public section

/-! Global-write and closure-safety preservation by source numbering. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open Flapjack ClosLang ClosProps
open Flapjack.Compiler.Backend.FlatProps (emptyGlobalBag unionGlobalBag)

mutual
private theorem renumber_globals (expression : Exp) (start : Nat) :
    setGlobals (renumber start expression).2 = setGlobals expression := by
  cases expression with
  | var trace n => simp [renumber, setGlobals]
  | ifThenElse trace condition yes no =>
    simp [renumber, setGlobals, renumber_globals condition, renumber_globals yes, renumber_globals no]
  | «let» trace bindings body =>
    simp [renumber, setGlobals, renumberList_globals bindings, renumber_globals body]
  | raise trace body => simp [renumber, setGlobals, renumber_globals body]
  | handle trace body handler => simp [renumber, setGlobals, renumber_globals body, renumber_globals handler]
  | tick trace body => simp [renumber, setGlobals, renumber_globals body]
  | call trace ticks location args =>
    simp [renumber, setGlobals, opGlobalBag, emptyGlobalBag, unionGlobalBag, renumberList_globals args]
    funext key
    simp [bagUnion, emptyBag]
  | app trace location function args => simp [renumber, setGlobals, renumber_globals function, renumberList_globals args]
  | fn name location vars arity body => simp [renumber, setGlobals, renumber_globals body]
  | letrec names location vars functions body =>
    simp [renumber, setGlobals, renumberFuns_globals functions, renumber_globals body]
  | op trace op args => simp [renumber, setGlobals, renumberList_globals args]
termination_by sizeOf expression

private theorem renumberList_globals (expressions : List Exp) (start : Nat) :
    elistGlobals (renumberList start expressions).2 = elistGlobals expressions := by
  cases expressions with
  | nil => simp [renumberList, elistGlobals]
  | cons first rest => simp [renumberList, elistGlobals, renumber_globals first, renumberList_globals rest]
termination_by sizeOf expressions

private theorem renumberFuns_globals (functions : List (Nat × Exp)) (start : Nat) :
    funGlobals (renumberFuns start functions).2 = funGlobals functions := by
  cases functions with
  | nil => simp [renumberFuns, funGlobals]
  | cons first rest =>
    cases first with
    | mk arity body => simp [renumberFuns, funGlobals, renumber_globals body, renumberFuns_globals rest]
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega
end

/-- Numbering preserves the global-write bags of lists and expressions. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "renumber_code_locs_elist_globals"]
theorem renumberCodeLocs_elistGlobals :
    (∀ loc es n es', renumberList loc es = (n, es') → elistGlobals es' = elistGlobals es) ∧
    (∀ loc e n e', renumber loc e = (n, e') → setGlobals e' = setGlobals e) := by
  constructor
  · intro loc es n es' run
    have h := renumberList_globals es loc
    simpa [run] using h
  · intro loc e n e' run
    have h := renumber_globals e loc
    simpa [run] using h

mutual
private theorem renumber_esgcFree (expression : Exp) (start : Nat) :
    esgcFree (renumber start expression).2 ↔ esgcFree expression := by
  cases expression with
  | var trace n => simp [renumber, esgcFree]
  | ifThenElse trace condition yes no =>
    simp [renumber, esgcFree, renumber_esgcFree condition, renumber_esgcFree yes, renumber_esgcFree no]
  | «let» trace bindings body =>
    simp [renumber, esgcFree, renumberList_esgcFree bindings, renumber_esgcFree body]
  | raise trace body => simp [renumber, esgcFree, renumber_esgcFree body]
  | handle trace body handler => simp [renumber, esgcFree, renumber_esgcFree body, renumber_esgcFree handler]
  | tick trace body => simp [renumber, esgcFree, renumber_esgcFree body]
  | call trace ticks location args => simp [renumber, esgcFree, renumberList_esgcFree args]
  | app trace location function args => simp [renumber, esgcFree, renumber_esgcFree function, renumberList_esgcFree args]
  | fn name location vars arity body => simp [renumber, esgcFree, renumber_globals body]
  | letrec names location vars functions body =>
    simp [renumber, esgcFree, renumberFuns_globals functions, renumber_esgcFree body]
  | op trace op args => simp [renumber, esgcFree, renumberList_esgcFree args]
termination_by sizeOf expression

private theorem renumberList_esgcFree (expressions : List Exp) (start : Nat) :
    esgcFreeList (renumberList start expressions).2 ↔ esgcFreeList expressions := by
  cases expressions with
  | nil => simp [renumberList, esgcFreeList]
  | cons first rest => simp [renumberList, esgcFreeList, renumber_esgcFree first, renumberList_esgcFree rest]
termination_by sizeOf expressions
decreasing_by all_goals subst_vars; simp_wf <;> omega
end

/-- Numbering preserves global-write closure safety for lists and expressions. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "renumber_code_locs_esgc_free"]
theorem renumberCodeLocs_esgcFree :
    (∀ loc es n es', renumberList loc es = (n, es') ∧ (∀ e ∈ es, esgcFree e) →
      ∀ e ∈ es', esgcFree e) ∧
    (∀ loc e n e', renumber loc e = (n, e') ∧ esgcFree e → esgcFree e') := by
  constructor
  · intro loc es n es' ⟨run, input⟩
    have h := renumberList_esgcFree es loc
    rw [run] at h
    exact esgcFreeList_iff es' |>.mp (h.mpr (esgcFreeList_iff es |>.mpr input))
  · intro loc e n e' ⟨run, input⟩
    have h := renumber_esgcFree e loc
    rw [run] at h
    exact h.mpr input

end Flapjack.Compiler.Backend.ClosNumber
