module

public import Flapjack.Compiler.Backend.ClosAnnotate.Shift
public import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations

@[expose] public section

/-! Annotation invariants of closure-variable shifting. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang ClosProps

mutual

/-- Flapjack helper: shifting an expression fills every closure-variable
annotation, regardless of the annotations in the input expression. -/
theorem shiftSing_varsSome (expression : Exp) (m l : Nat) (index : Spt Nat) :
    fnVarsSomeExp (shiftSing expression m l index) := by
  cases expression with
  | var trace n => simp [shiftSing, fnVarsSomeExp]
  | ifThenElse trace condition yes no =>
    simp [shiftSing, fnVarsSomeExp, shiftSing_varsSome condition, shiftSing_varsSome yes, shiftSing_varsSome no]
  | «let» trace bindings body =>
    simp [shiftSing, fnVarsSomeExp, shiftList_varsSome bindings, shiftSing_varsSome body]
  | raise trace body => simp [shiftSing, fnVarsSomeExp, shiftSing_varsSome body]
  | handle trace body handler =>
    simp [shiftSing, fnVarsSomeExp, shiftSing_varsSome body, shiftSing_varsSome handler]
  | tick trace body => simp [shiftSing, fnVarsSomeExp, shiftSing_varsSome body]
  | call trace ticks location args => simp [shiftSing, fnVarsSomeExp, shiftList_varsSome args]
  | app trace location function args =>
    simp [shiftSing, fnVarsSomeExp, shiftSing_varsSome function, shiftList_varsSome args]
  | fn name location vars arity body => simp [shiftSing, fnVarsSomeExp, shiftSing_varsSome body]
  | letrec names location vars functions body =>
    simp [shiftSing, fnVarsSomeExp, shiftFuns_varsSome functions, shiftSing_varsSome body]
  | op trace op args => simp [shiftSing, fnVarsSomeExp, shiftList_varsSome args]
termination_by sizeOf expression

/-- Flapjack helper: all expressions in a shifted list have variable
annotations. -/
theorem shiftList_varsSome (expressions : List Exp) (m l : Nat) (index : Spt Nat) :
    everyFnVarsSome (shiftList expressions m l index) := by
  cases expressions with
  | nil => simp [shiftList, everyFnVarsSome]
  | cons first rest =>
    simp [shiftList, everyFnVarsSome, shiftSing_varsSome first, shiftList_varsSome rest]
termination_by sizeOf expressions

/-- Flapjack helper for the recursive-function list shifted by a letrec. -/
theorem shiftFuns_varsSome (functions : List (Nat × Exp)) (count m : Nat) (index : Spt Nat) :
    fnVarsSomeFuns (shiftFuns count m index functions) := by
  cases functions with
  | nil => simp [shiftFuns, fnVarsSomeFuns]
  | cons first rest =>
    obtain ⟨arity, body⟩ := first
    simp [shiftFuns, fnVarsSomeFuns, shiftSing_varsSome body, shiftFuns_varsSome rest]
termination_by sizeOf functions

end

mutual

/-- Free-variable discovery preserves existing location annotations. The
unused pure-let branch may erase bindings, so this is a forward implication. -/
theorem altFreeSing_locations (expression : Exp) :
    fnLocationSomeExp expression → fnLocationSomeExp (altFreeSing expression).1 := by
  intro locations
  cases expression with
  | var trace n => simp [altFreeSing, fnLocationSomeExp]
  | ifThenElse trace condition yes no =>
    simp only [fnLocationSomeExp] at locations
    simpa [altFreeSing, fnLocationSomeExp] using
      And.intro (altFreeSing_locations condition locations.1)
        (And.intro (altFreeSing_locations yes locations.2.1) (altFreeSing_locations no locations.2.2))
  | «let» trace bindings body =>
    simp only [fnLocationSomeExp] at locations
    have bodyOk := altFreeSing_locations body locations.1
    have bindingsOk := altFreeList_locations bindings locations.2
    have replicated : ∀ n, everyFnLocationSome (List.replicate n (const0 trace)) := by
      intro n
      induction n with
      | zero => simp [everyFnLocationSome]
      | succ n ih =>
        simp only [List.replicate_succ, everyFnLocationSome]
        exact ⟨by simp [const0, fnLocationSomeExp, everyFnLocationSome], ih⟩
    simp only [altFreeSing]
    split
    · simpa [fnLocationSomeExp] using And.intro bodyOk (replicated bindings.length)
    · simpa [fnLocationSomeExp] using And.intro bodyOk bindingsOk
  | raise trace body =>
    have h : fnLocationSomeExp body := by simpa [fnLocationSomeExp] using locations
    simpa [altFreeSing, fnLocationSomeExp] using altFreeSing_locations body h
  | handle trace body handler =>
    simp only [fnLocationSomeExp] at locations
    simpa [altFreeSing, fnLocationSomeExp] using
      And.intro (altFreeSing_locations body locations.1) (altFreeSing_locations handler locations.2)
  | tick trace body =>
    have h : fnLocationSomeExp body := by simpa [fnLocationSomeExp] using locations
    simpa [altFreeSing, fnLocationSomeExp] using altFreeSing_locations body h
  | call trace ticks location args =>
    have h : everyFnLocationSome args := by simpa [fnLocationSomeExp] using locations
    simpa [altFreeSing, fnLocationSomeExp] using altFreeList_locations args h
  | app trace location function args =>
    simp only [fnLocationSomeExp] at locations
    simpa [altFreeSing, fnLocationSomeExp] using
      And.intro (altFreeSing_locations function locations.1) (altFreeList_locations args locations.2)
  | fn name location vars arity body =>
    simp only [fnLocationSomeExp] at locations
    simpa [altFreeSing, fnLocationSomeExp] using And.intro locations.1 (altFreeSing_locations body locations.2)
  | letrec names location vars functions body =>
    simp only [fnLocationSomeExp] at locations
    have functionOk := altFreeFuns_locations functions functions.length locations.2.1
    have bodyOk := altFreeSing_locations body locations.2.2
    simpa [altFreeSing, fnLocationSomeExp] using And.intro locations.1 (And.intro functionOk bodyOk)
  | op trace op args =>
    have h : everyFnLocationSome args := by simpa [fnLocationSomeExp] using locations
    simpa [altFreeSing, fnLocationSomeExp] using altFreeList_locations args h
termination_by sizeOf expression

/-- Free-variable discovery preserves locations in expression lists. -/
theorem altFreeList_locations (expressions : List Exp) :
    everyFnLocationSome expressions → everyFnLocationSome (altFreeList expressions).1 := by
  intro locations
  cases expressions with
  | nil => simp [altFreeList, everyFnLocationSome]
  | cons first rest =>
    simp only [everyFnLocationSome] at locations
    simpa [altFreeList, everyFnLocationSome] using
      And.intro (altFreeSing_locations first locations.1) (altFreeList_locations rest locations.2)
termination_by sizeOf expressions

/-- Free-variable discovery preserves locations in recursive function bodies. -/
theorem altFreeFuns_locations (functions : List (Nat × Exp)) (count : Nat) :
    fnLocationSomeFuns functions → fnLocationSomeFuns ((altFreeFuns count functions).map Prod.fst) := by
  intro locations
  cases functions with
  | nil => simp [altFreeFuns, fnLocationSomeFuns]
  | cons first rest =>
    cases first with
    | mk arity body =>
      simp only [fnLocationSomeFuns] at locations
      simpa [altFreeFuns, fnLocationSomeFuns] using
        And.intro (altFreeSing_locations body locations.1) (altFreeFuns_locations rest count locations.2)
termination_by sizeOf functions
decreasing_by all_goals subst_vars; simp_wf <;> omega

end

mutual

/-- Flapjack helper: variable shifting preserves the presence of every
function-code location in an expression. -/
theorem shiftSing_locations (expression : Exp) (m l : Nat) (index : Spt Nat) :
    fnLocationSomeExp (shiftSing expression m l index) ↔ fnLocationSomeExp expression := by
  cases expression with
  | var trace n => simp [shiftSing, fnLocationSomeExp]
  | ifThenElse trace condition yes no =>
    simp [shiftSing, fnLocationSomeExp, shiftSing_locations condition, shiftSing_locations yes, shiftSing_locations no]
  | «let» trace bindings body =>
    simp [shiftSing, fnLocationSomeExp, shiftList_locations bindings, shiftSing_locations body]
  | raise trace body => simp [shiftSing, fnLocationSomeExp, shiftSing_locations body]
  | handle trace body handler =>
    simp [shiftSing, fnLocationSomeExp, shiftSing_locations body, shiftSing_locations handler]
  | tick trace body => simp [shiftSing, fnLocationSomeExp, shiftSing_locations body]
  | call trace ticks location args => simp [shiftSing, fnLocationSomeExp, shiftList_locations args]
  | app trace location function args =>
    simp [shiftSing, fnLocationSomeExp, shiftSing_locations function, shiftList_locations args]
  | fn name location vars arity body => simp [shiftSing, fnLocationSomeExp, shiftSing_locations body]
  | letrec names location vars functions body =>
    simp [shiftSing, fnLocationSomeExp, shiftFuns_locations functions, shiftSing_locations body]
  | op trace op args => simp [shiftSing, fnLocationSomeExp, shiftList_locations args]
termination_by sizeOf expression

/-- Flapjack helper: shifting a list preserves its location predicate. -/
theorem shiftList_locations (expressions : List Exp) (m l : Nat) (index : Spt Nat) :
    everyFnLocationSome (shiftList expressions m l index) ↔ everyFnLocationSome expressions := by
  cases expressions with
  | nil => simp [shiftList, everyFnLocationSome]
  | cons first rest =>
    simp [shiftList, everyFnLocationSome, shiftSing_locations first, shiftList_locations rest]
termination_by sizeOf expressions

/-- Flapjack helper for recursive-function location annotations. -/
theorem shiftFuns_locations (functions : List (Nat × Exp)) (count m : Nat) (index : Spt Nat) :
    fnLocationSomeFuns (shiftFuns count m index functions) ↔ fnLocationSomeFuns functions := by
  cases functions with
  | nil => simp [shiftFuns, fnLocationSomeFuns]
  | cons first rest =>
    obtain ⟨arity, body⟩ := first
    simp [shiftFuns, fnLocationSomeFuns, shiftSing_locations body, shiftFuns_locations rest]
termination_by sizeOf functions

end

/-- Every expression produced by the executable list annotation has its
closure-variable annotations filled. -/
theorem annotateList_varsSome (arity : Nat) (expressions : List Exp) :
    everyFnVarsSome (annotateList arity expressions) :=
  shiftList_varsSome _ _ _ _

/-- Every function body produced by the executable program annotation has its
closure-variable annotations filled. -/
theorem compile_varsSome (program : List (Nat × Nat × Exp)) :
    ∀ name arity body, (name, arity, body) ∈ compile program → everyFnVarsSome [body] := by
  intro name arity body member
  obtain ⟨⟨n, args, exp⟩, sourceMember, equal⟩ := List.mem_map.mp member
  simp only [Prod.mk.injEq] at equal
  obtain ⟨rfl, rfl, rfl⟩ := equal
  simpa [compile, annotateSing, everyFnVarsSome] using shiftSing_varsSome (altFreeSing exp).1 0 args .ln

/-- Incremental annotation fills variable annotations in the main expression
list and in every auxiliary function body. -/
theorem compileInc_varsSome (program : List Exp × List (Nat × Nat × Exp)) :
    everyFnVarsSome (compileInc program).1 ∧
      ∀ entry ∈ (compileInc program).2, everyFnVarsSome [entry.2.2] := by
  constructor
  · exact annotateList_varsSome 0 program.1
  · intro ⟨name, arity, body⟩ member
    exact compile_varsSome program.2 name arity body member

/-- Annotating an expression preserves its existing function locations. -/
theorem annotateSing_locations (arity : Nat) (expression : Exp)
    (locations : fnLocationSomeExp expression) : fnLocationSomeExp (annotateSing arity expression) := by
  apply (shiftSing_locations (altFreeSing expression).1 0 arity .ln).2
  exact altFreeSing_locations expression locations

/-- Annotating a list preserves its existing function locations. -/
theorem annotateList_locations (arity : Nat) (expressions : List Exp)
    (locations : everyFnLocationSome expressions) : everyFnLocationSome (annotateList arity expressions) := by
  apply (shiftList_locations (altFreeList expressions).1 0 arity .ln).2
  exact altFreeList_locations expressions locations

/-- Program annotation preserves function locations in every compiled body. -/
theorem compile_locations (program : List (Nat × Nat × Exp))
    (locations : ∀ name arity body, (name, arity, body) ∈ program → everyFnLocationSome [body]) :
    ∀ name arity body, (name, arity, body) ∈ compile program → everyFnLocationSome [body] := by
  intro name arity body member
  obtain ⟨⟨n, args, exp⟩, sourceMember, equal⟩ := List.mem_map.mp member
  simp only [Prod.mk.injEq] at equal
  obtain ⟨rfl, rfl, rfl⟩ := equal
  have sourceLocations : fnLocationSomeExp exp := by
    simpa [everyFnLocationSome] using locations n args exp sourceMember
  simpa [everyFnLocationSome] using annotateSing_locations args exp sourceLocations

/-- Incremental annotation preserves all source function locations. -/
theorem compileInc_locations (program : List Exp × List (Nat × Nat × Exp))
    (mainLocations : everyFnLocationSome program.1)
    (auxLocations : ∀ entry ∈ program.2, everyFnLocationSome [entry.2.2]) :
    everyFnLocationSome (compileInc program).1 ∧
      ∀ entry ∈ (compileInc program).2, everyFnLocationSome [entry.2.2] := by
  constructor
  · exact annotateList_locations 0 program.1 mainLocations
  · intro ⟨name, arity, body⟩ member
    apply compile_locations program.2 ?_ name arity body member
    intro n a e sourceMember
    exact auxLocations (n, a, e) sourceMember

end Flapjack.Compiler.Backend.ClosAnnotate
