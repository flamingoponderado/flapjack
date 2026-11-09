module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.State
public import Flapjack.Misc.LookupVars

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Closure application and code lookup for the closure evaluator. -/
namespace Flapjack.Compiler.Backend.ClosSem

private def maptoBroadlookup {α β : Type} (f : HolFiniteMapExact α β) : α → Option β := f.lookup
private def mapofBroad {α β : Type} (lookup : α → Option β)
    (support : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact α β :=
  ⟨lookup, support⟩

/-- The source code map has the canonical lookup/support roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_findCode_code {κ β : Type}
    (code : HolFiniteMapExact κ (Nat × β)) :
    mapofBroad (maptoBroadlookup code) code.finiteSupport = code := by
  cases code
  rfl

/-- A direct call accepts a code entry only at its declared arity. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "find_code_def"
  (fmap_as_finite_support_parameters := [code])]
def findCode {κ α β : Type} (location : κ) (args : List α)
    (code : HolFiniteMapExact κ (Nat × β)) : Option (List α × β) := do
  let (arity, body) ← code.lookup location
  if args.length = arity then some (args, body) else none

/-- Check the optional direct-call location and application arity. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "check_loc_def"]
noncomputable def checkLoc {α : Type} (maxApp : Nat) (requested location : Option α)
    (parameters arguments supplied : Nat) : Bool := by
  classical
  exact match requested with
    | none => decide (arguments ≤ maxApp)
    | some address => decide (parameters = arguments ∧ supplied = 0 ∧ some address = location)

/-- Result of examining a closure application. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "app_kind"]
inductive AppKind where
  | partialApp : Value → AppKind
  | fullApp : ClosLang.Exp → List Value → List Value → AppKind

/-- Split argument lists exactly as the closure evaluator does, allowing
partial and over-application and constructing all recursive closures. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "dest_closure_def"]
noncomputable def destClosure (maxApp : Nat) (requested : Option Nat) (function : Value)
    (args : List Value) : Option AppKind :=
  match function with
  | .closure location supplied env arity body =>
    if checkLoc maxApp requested location arity args.length supplied.length && supplied.length < arity then
      if args.length + supplied.length < arity then
        some (.partialApp (.closure location (args ++ supplied) env arity body))
      else
        let needed := arity - supplied.length
        some (.fullApp body (args.reverse.take needed |>.reverse |>.append (supplied ++ env))
          (args.reverse.drop needed |>.reverse))
    else none
  | .recclosure location supplied env functions index =>
    match functions[index]? with
    | none => none
    | some (arity, body) =>
      let codeLocation := location.map (fun loc => 2 * index + loc)
      if checkLoc maxApp requested codeLocation arity args.length supplied.length && supplied.length < arity then
        if args.length + supplied.length < arity then
          some (.partialApp (.recclosure location (args ++ supplied) env functions index))
        else
          let needed := arity - supplied.length
          let recursive := (List.range functions.length).map (fun i => Value.recclosure location [] env functions i)
          some (.fullApp body (args.reverse.take needed |>.reverse |>.append (supplied ++ recursive ++ env))
            (args.reverse.drop needed |>.reverse))
      else none
  | _ => none

/-- The ordinary closure clause in the source's full-before-partial form. -/
theorem destClosure_closure_source (maxApp : Nat) (requested location : Option Nat)
    (supplied env args : List Value) (arity : Nat) (body : ClosLang.Exp) :
    destClosure maxApp requested (.closure location supplied env arity body) args =
      if checkLoc maxApp requested location arity args.length supplied.length = true ∧ supplied.length < arity then
        if ¬ (args.length + supplied.length < arity) then
          some (.fullApp body (args.reverse.take (arity - supplied.length) |>.reverse |>.append (supplied ++ env))
            (args.reverse.drop (arity - supplied.length) |>.reverse))
        else some (.partialApp (.closure location (args ++ supplied) env arity body))
      else none := by
  by_cases valid : checkLoc maxApp requested location arity args.length supplied.length = true ∧ supplied.length < arity <;>
    by_cases partialCase : args.length + supplied.length < arity <;> simp [destClosure, valid, partialCase]

/-- The recursive closure clause uses HOL `EL` only under its original
index bound and keeps the same application and captured-environment order. -/
theorem destClosure_recclosure_source (maxApp : Nat) (requested location : Option Nat)
    (supplied env args : List Value) (functions : List (Nat × ClosLang.Exp)) (index : Nat) :
    destClosure maxApp requested (.recclosure location supplied env functions index) args =
      let entry := @Flapjack.holEl (Nat × ClosLang.Exp) ⟨(0, .var .none 0)⟩ index functions
      let arity := entry.1
      let body := entry.2
      if functions.length ≤ index ∨
          checkLoc maxApp requested (location.map (fun loc => 2 * index + loc)) arity args.length supplied.length = false ∨
          ¬ (supplied.length < arity) then none
      else
        let recursive := (List.range functions.length).map (fun i => Value.recclosure location [] env functions i)
        if ¬ (args.length + supplied.length < arity) then
          some (.fullApp body (args.reverse.take (arity - supplied.length) |>.reverse |>.append (supplied ++ recursive ++ env))
            (args.reverse.drop (arity - supplied.length) |>.reverse))
        else some (.partialApp (.recclosure location (args ++ supplied) env functions index)) := by
  letI : Nonempty (Nat × ClosLang.Exp) := ⟨(0, .var .none 0)⟩
  by_cases bound : index < functions.length
  · have get := List.getElem?_eq_getElem (l := functions) bound
    rw [Flapjack.holEl_eq_getElem index functions bound]
    cases entry : functions[index]'bound with
    | mk arity body =>
      by_cases check : checkLoc maxApp requested (location.map (fun loc => 2 * index + loc))
          arity args.length supplied.length = true <;>
        by_cases enough : supplied.length < arity <;>
        by_cases partialCase : args.length + supplied.length < arity <;>
        simp [destClosure, get, entry, Nat.not_le_of_gt bound, check, enough, partialCase]
  · have outside : functions.length ≤ index := Nat.le_of_not_gt bound
    simp [destClosure, outside]

/-- A full application consumes at least one argument. This ensures that
repeated application of an over-applied result can be well founded. -/
theorem destClosure_full_remaining_lt (maxApp : Nat) (requested : Option Nat)
    (function : Value) (args env rest : List Value) (body : ClosLang.Exp)
    (result : destClosure maxApp requested function args = some (.fullApp body env rest)) :
    rest.length < args.length := by
  cases function <;> simp only [destClosure] at result <;> try contradiction
  case closure location supplied captured arity expression =>
    split at result
    · rename_i valid
      split at result
      · simp at result
      · simp only [Option.some.injEq, AppKind.fullApp.injEq] at result
        rcases result with ⟨_, _, rfl⟩
        simp only [List.length_reverse, List.length_drop]
        have suppliedBound : supplied.length < arity := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
          exact valid.2
        omega
    · simp at result
  case recclosure location supplied captured functions index =>
    split at result
    · simp at result
    · rename_i arity expression found
      split at result
      · rename_i valid
        split at result
        · simp at result
        · simp only [Option.some.injEq, AppKind.fullApp.injEq] at result
          rcases result with ⟨_, _, rfl⟩
          simp only [List.length_reverse, List.length_drop]
          have suppliedBound : supplied.length < arity := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
            exact valid.2
          omega
      · simp at result

/-- A full application consumes an argument; the source's unused `so_far`
parameter remains independently polymorphic. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "dest_closure_length"]
theorem destClosure_length {α : Type} (maxApp : Nat) (requested : Option Nat)
    (function : Value) (args : List Value) (body : ClosLang.Exp) (env rest : List Value) (_soFar : α)
    (result : destClosure maxApp requested function args = some (.fullApp body env rest)) :
    rest.length < args.length :=
  destClosure_full_remaining_lt maxApp requested function args env rest body result

/-- Restrict an environment when requested by the closure optimizer. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "clos_env_def"]
def closEnv {α : Type} (restrict : Bool) (names : List Nat) (env : List α) : Option (List α) :=
  if restrict then lookupVars names env else some env

/-- Construct the recursive closure bundle over the selected environment. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "build_recc_def"]
def buildRecc (restrict : Bool) (location : Option Nat) (env : List Value)
    (names : List Nat) (functions : List (Nat × ClosLang.Exp)) : Option (List Value) := do
  let captured ← closEnv restrict names env
  pure ((List.range functions.length).map (fun i => .recclosure location [] captured functions i))

end Flapjack.Compiler.Backend.ClosSem
