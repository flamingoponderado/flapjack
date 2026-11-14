module

public import Flapjack.Compiler.Backend.ClosNumber.Proofs.ValueRelation
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Call
public import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationInvariants

@[expose] public section

/-! Closure application prerequisites for numbering correctness. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open Flapjack.Compiler.Backend.ClosSem

/-- Each numbered list entry comes from numbering its corresponding source
expression at some intermediate state. -/
theorem renumberList_getElem (expressions : List ClosLang.Exp) (start index : Nat)
    (body : ClosLang.Exp) (found : expressions[index]? = some body) :
    ∃ location, (renumberList start expressions).2[index]? = some (renumber location body).2 := by
  induction expressions generalizing start index with
  | nil => simp at found
  | cons first rest ih =>
    cases index with
    | zero =>
      simp at found
      subst body
      exact ⟨start, by simp [renumberList]⟩
    | succ index =>
      have tailFound : rest[index]? = some body := by simpa using found
      obtain ⟨location, result⟩ := ih (renumber start first).1 index tailFound
      exact ⟨location, by simpa [renumberList] using result⟩

/-- Numbering a recursive function bundle preserves the arity at every
present index and numbers that function's body at an intermediate location. -/
theorem renumberedBundle_getElem (functions : List (Nat × ClosLang.Exp)) (start index arity : Nat)
    (body : ClosLang.Exp) (found : functions[index]? = some (arity, body)) :
    ∃ location, ((functions.map Prod.fst).zip (renumberList start (functions.map Prod.snd)).2)[index]? =
      some (arity, (renumber location body).2) := by
  have sourceBody : (functions.map Prod.snd)[index]? = some body := by simp [List.getElem?_map, found]
  have sourceArity : (functions.map Prod.fst)[index]? = some arity := by simp [List.getElem?_map, found]
  obtain ⟨location, result⟩ := renumberList_getElem (functions.map Prod.snd) start index body sourceBody
  refine ⟨location, ?_⟩
  exact List.getElem?_zip_eq_some.mpr ⟨sourceArity, result⟩

/-- The recursive-bundle traversal has the same bodies and arities as the
    representation used by the numbered closure relation. -/
theorem renumberFuns_eq_bundle (functions : List (Nat × ClosLang.Exp)) (start : Nat) :
    (renumberFuns start functions).2 =
      (functions.map Prod.fst).zip (renumberList start (functions.map Prod.snd)).2 := by
  induction functions generalizing start with
  | nil => rfl
  | cons f rest ih =>
    obtain ⟨arity, body⟩ := f
    simp [renumberFuns, renumberList, ih]

/-- The recursive-function traversal threads exactly the same next location
as numbering the list of bodies. This is supporting infrastructure for the
source traversal, with no separate HOL declaration. -/
theorem renumberFuns_next_eq (functions : List (Nat × ClosLang.Exp)) (start : Nat) :
    (renumberFuns start functions).1 = (renumberList start (functions.map Prod.snd)).1 := by
  induction functions generalizing start with
  | nil => rfl
  | cons function rest ih =>
    obtain ⟨arity, body⟩ := function
    simpa [renumberFuns, renumberList] using ih (renumber start body).1

/-- The function-bundle traversal agrees in both returned components with
numbering bodies and reattaching their original arities. This helper has no
separate HOL declaration. -/
theorem renumberFuns_eq_numberedBodies (functions : List (Nat × ClosLang.Exp)) (start : Nat) :
    renumberFuns start functions =
      ((renumberList start (functions.map Prod.snd)).1,
        (functions.map Prod.fst).zip (renumberList start (functions.map Prod.snd)).2) := by
  apply Prod.ext
  · exact renumberFuns_next_eq functions start
  · exact renumberFuns_eq_bundle functions start

/-- The executed recursive-binding clause in the source's map-and-zip shape.
This supporting equation has no separate HOL declaration. -/
theorem renumber_letrec_source (names : List Flapjack.AstHOL.VarN) (location : Option Nat)
    (selected : Option (List Nat)) (functions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (start : Nat) :
    renumber start (.letrec names location selected functions body) =
      let (next, bodies) := renumberList start (functions.map Prod.snd)
      let (finish, nextBody) := renumber (next + 2 * bodies.length) body
      (finish, .letrec names (some next) selected ((functions.map Prod.fst).zip bodies) nextBody) := by
  simp [renumber, renumberFuns_eq_numberedBodies, renumberList_length]

/-- Recursive-bundle numbering preserves the arity validation test. -/
theorem renumberFuns_all_arities (functions : List (Nat × ClosLang.Exp)) (start maxApp : Nat) :
    ((renumberFuns start functions).2.all (fun (arity, _) => arity ≤ maxApp && arity != 0)) =
      functions.all (fun (arity, _) => arity ≤ maxApp && arity != 0) := by
  induction functions generalizing start with
  | nil => rfl
  | cons f rest ih =>
    obtain ⟨arity, body⟩ := f
    simp [renumberFuns, ih]

/-- A body selected from an application-safe function bundle is itself
application-safe. -/
theorem selectedBody_noAppSome (maxApp index arity : Nat) (functions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (found : functions[index]? = some (arity, body))
    (safe : ¬ ClosProps.containsAppSome maxApp (functions.map Prod.snd)) :
    ¬ ClosProps.containsAppSome maxApp [body] := by
  have member : body ∈ functions.map Prod.snd := by
    apply List.mem_map.mpr
    exact ⟨(arity, body), List.mem_of_getElem? found, rfl⟩
  have contained : ∀ (xs : List ClosLang.Exp), body ∈ xs →
      ClosProps.containsAppSomeExp maxApp body → ClosProps.containsAppSome maxApp xs := by
    intro xs
    induction xs with
    | nil => simp
    | cons first rest ih =>
      intro h hb
      simp only [List.mem_cons] at h
      simp only [ClosProps.containsAppSome]
      rcases h with rfl | h
      · exact Or.inl hb
      · exact Or.inr (ih h hb)
  intro forbidden
  apply safe
  apply contained _ member
  simpa [ClosProps.containsAppSome] using forbidden

/-- The bundles installed into environments for a full recursive application
are pointwise related, with exactly the original number of closures. -/
theorem numberedRecclosures_related (maxApp start : Nat) (location nextLocation : Option Nat)
    (env nextEnv : List Value) (functions : List (Nat × ClosLang.Exp))
    (envRel : List.Forall₂ (ValueRel maxApp) env nextEnv)
    (safe : ¬ ClosProps.containsAppSome maxApp (functions.map Prod.snd)) :
    List.Forall₂ (ValueRel maxApp)
      ((List.range functions.length).map (fun i => Value.recclosure location [] env functions i))
      ((List.range ((functions.map Prod.fst).zip (renumberList start (functions.map Prod.snd)).2).length).map
        (fun i => Value.recclosure nextLocation [] nextEnv
          ((functions.map Prod.fst).zip (renumberList start (functions.map Prod.snd)).2) i)) := by
  have lengths : ((functions.map Prod.fst).zip (renumberList start (functions.map Prod.snd)).2).length =
      functions.length := by simp [renumberList_length]
  rw [lengths]
  generalize indices : List.range functions.length = xs
  clear indices
  induction xs with
  | nil => exact .nil
  | cons index rest ih =>
    apply List.Forall₂.cons
    · exact .recclosure location nextLocation [] [] env nextEnv functions _ index start envRel .nil safe rfl
    · exact ih

/-- For ordinary closures, a rejected indirect application is also rejected
after numbering: the location annotations are not observed by an indirect
application and related argument lists have equal lengths. -/
theorem destClosure_numbered_none (maxApp arity start : Nat) (location nextLocation : Option Nat)
    (supplied nextSupplied env nextEnv args nextArgs : List Value) (body : ClosLang.Exp)
    (suppliedRel : List.Forall₂ (ValueRel maxApp) supplied nextSupplied)
    (argsRel : List.Forall₂ (ValueRel maxApp) args nextArgs)
    (rejected : destClosure maxApp none (.closure location supplied env arity body) args = none) :
    destClosure maxApp none (.closure nextLocation nextSupplied nextEnv arity (renumber start body).2) nextArgs = none := by
  have fail : ¬ (args.length ≤ maxApp ∧ supplied.length < arity) := by
    intro ⟨argsBound, suppliedBound⟩
    by_cases hpart : args.length + supplied.length < arity <;>
      simp [destClosure, checkLoc, argsBound, suppliedBound, hpart] at rejected
  simp [destClosure, checkLoc, ← argsRel.length_eq, ← suppliedRel.length_eq, fail]

/-- A successful partial application of an ordinary closure remains partial
after numbering, and its newly supplied arguments remain related. -/
theorem destClosure_numbered_partial (maxApp arity start : Nat) (location nextLocation : Option Nat)
    (supplied nextSupplied env nextEnv args nextArgs : List Value) (body : ClosLang.Exp) (result : Value)
    (suppliedRel : List.Forall₂ (ValueRel maxApp) supplied nextSupplied)
    (envRel : List.Forall₂ (ValueRel maxApp) env nextEnv)
    (argsRel : List.Forall₂ (ValueRel maxApp) args nextArgs)
    (safe : ¬ ClosProps.containsAppSome maxApp [body])
    (run : destClosure maxApp none (.closure location supplied env arity body) args = some (.partialApp result)) :
    ∃ nextResult,
      destClosure maxApp none (.closure nextLocation nextSupplied nextEnv arity (renumber start body).2) nextArgs =
        some (.partialApp nextResult) ∧ ValueRel maxApp result nextResult := by
  by_cases valid : args.length ≤ maxApp ∧ supplied.length < arity
  · by_cases hpart : args.length + supplied.length < arity
    · have resultEq : result = .closure location (args ++ supplied) env arity body := by
        simpa [destClosure, checkLoc, valid.1, valid.2, hpart] using run.symm
      subst result
      refine ⟨.closure nextLocation (nextArgs ++ nextSupplied) nextEnv arity (renumber start body).2, ?_, ?_⟩
      · simp [destClosure, checkLoc, ← argsRel.length_eq, ← suppliedRel.length_eq, valid.1, valid.2, hpart]
      · exact .closure location nextLocation (args ++ supplied) (nextArgs ++ nextSupplied) env nextEnv
          arity start body _ envRel (List.rel_append argsRel suppliedRel) safe rfl
    · simp [destClosure, checkLoc, valid.1, valid.2, hpart] at run
  · simp [destClosure, checkLoc, valid] at run

/-- Full indirect application of an ordinary closure selects the numbered
body and related argument environments, including the over-application tail. -/
theorem destClosure_numbered_full (maxApp arity start : Nat) (location nextLocation : Option Nat)
    (supplied nextSupplied env nextEnv args nextArgs : List Value) (body resultBody : ClosLang.Exp)
    (resultEnv remaining : List Value)
    (suppliedRel : List.Forall₂ (ValueRel maxApp) supplied nextSupplied)
    (envRel : List.Forall₂ (ValueRel maxApp) env nextEnv)
    (argsRel : List.Forall₂ (ValueRel maxApp) args nextArgs)
    (safe : ¬ ClosProps.containsAppSome maxApp [body])
    (run : destClosure maxApp none (.closure location supplied env arity body) args =
      some (.fullApp resultBody resultEnv remaining)) :
    ∃ nextResultEnv nextRemaining,
      destClosure maxApp none (.closure nextLocation nextSupplied nextEnv arity (renumber start body).2) nextArgs =
        some (.fullApp (renumber start resultBody).2 nextResultEnv nextRemaining) ∧
      List.Forall₂ (ValueRel maxApp) resultEnv nextResultEnv ∧
      List.Forall₂ (ValueRel maxApp) remaining nextRemaining ∧
      ¬ ClosProps.containsAppSome maxApp [resultBody] := by
  by_cases valid : args.length ≤ maxApp ∧ supplied.length < arity
  · by_cases hpart : args.length + supplied.length < arity
    · simp [destClosure, checkLoc, valid.1, valid.2, hpart] at run
    · simp [destClosure, checkLoc, valid.1, valid.2, hpart] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      let needed := arity - supplied.length
      refine ⟨(nextArgs.reverse.take needed).reverse ++ (nextSupplied ++ nextEnv),
        (nextArgs.reverse.drop needed).reverse, ?_, ?_, ?_, ?_⟩
      · simp [destClosure, checkLoc, ← argsRel.length_eq, ← suppliedRel.length_eq, valid.1, valid.2, hpart, needed]
      · have relatedPrefix := List.rel_reverse (List.forall₂_take needed (List.rel_reverse argsRel))
        exact List.rel_append relatedPrefix (List.rel_append suppliedRel envRel)
      · exact List.rel_reverse (List.forall₂_drop needed (List.rel_reverse argsRel))
      · exact safe
  · simp [destClosure, checkLoc, valid] at run

/-- Partial indirect application of a recursive closure preserves both its
numbered function bundle and accumulated related arguments. -/
theorem destRecclosure_numbered_partial (maxApp start index : Nat) (location nextLocation : Option Nat)
    (supplied nextSupplied env nextEnv args nextArgs : List Value)
    (functions : List (Nat × ClosLang.Exp)) (result : Value)
    (suppliedRel : List.Forall₂ (ValueRel maxApp) supplied nextSupplied)
    (envRel : List.Forall₂ (ValueRel maxApp) env nextEnv)
    (argsRel : List.Forall₂ (ValueRel maxApp) args nextArgs)
    (safe : ¬ ClosProps.containsAppSome maxApp (functions.map Prod.snd))
    (run : destClosure maxApp none (.recclosure location supplied env functions index) args =
      some (.partialApp result)) :
    ∃ nextResult,
      destClosure maxApp none (.recclosure nextLocation nextSupplied nextEnv
        ((functions.map Prod.fst).zip (renumberList start (functions.map Prod.snd)).2) index) nextArgs =
        some (.partialApp nextResult) ∧ ValueRel maxApp result nextResult := by
  cases found : functions[index]? with
  | none => simp [destClosure, found] at run
  | some entry =>
    obtain ⟨arity, body⟩ := entry
    obtain ⟨location', nextFound⟩ := renumberedBundle_getElem functions start index arity body found
    by_cases valid : args.length ≤ maxApp ∧ supplied.length < arity
    · by_cases hpart : args.length + supplied.length < arity
      · have resultEq : result = .recclosure location (args ++ supplied) env functions index := by
          simpa [destClosure, found, checkLoc, valid.1, valid.2, hpart] using run.symm
        subst result
        refine ⟨.recclosure nextLocation (nextArgs ++ nextSupplied) nextEnv
          ((functions.map Prod.fst).zip (renumberList start (functions.map Prod.snd)).2) index, ?_, ?_⟩
        · simp [destClosure, nextFound, checkLoc, ← argsRel.length_eq, ← suppliedRel.length_eq,
            valid.1, valid.2, hpart]
        · exact .recclosure location nextLocation (args ++ supplied) (nextArgs ++ nextSupplied) env nextEnv
            functions _ index start envRel (List.rel_append argsRel suppliedRel) safe rfl
      · simp [destClosure, found, checkLoc, valid.1, valid.2, hpart] at run
    · simp [destClosure, found, checkLoc, valid] at run

/-- Rejected indirect recursive-closure applications remain rejected after
numbering, including an out-of-range function index. -/
theorem destRecclosure_numbered_none (maxApp start index : Nat) (location nextLocation : Option Nat)
    (supplied nextSupplied env nextEnv args nextArgs : List Value)
    (functions : List (Nat × ClosLang.Exp))
    (suppliedRel : List.Forall₂ (ValueRel maxApp) supplied nextSupplied)
    (argsRel : List.Forall₂ (ValueRel maxApp) args nextArgs)
    (rejected : destClosure maxApp none (.recclosure location supplied env functions index) args = none) :
    destClosure maxApp none (.recclosure nextLocation nextSupplied nextEnv
      ((functions.map Prod.fst).zip (renumberList start (functions.map Prod.snd)).2) index) nextArgs = none := by
  cases found : functions[index]? with
  | none =>
    have targetNone : ((functions.map Prod.fst).zip (renumberList start (functions.map Prod.snd)).2)[index]? = none := by
      cases h : ((functions.map Prod.fst).zip (renumberList start (functions.map Prod.snd)).2)[index]? with
      | none => rfl
      | some entry =>
        have first := (List.getElem?_zip_eq_some.mp h).1
        simp [List.getElem?_map, found] at first
    simp [destClosure, targetNone]
  | some entry =>
    obtain ⟨arity, body⟩ := entry
    obtain ⟨location', nextFound⟩ := renumberedBundle_getElem functions start index arity body found
    have fail : ¬ (args.length ≤ maxApp ∧ supplied.length < arity) := by
      intro ⟨argsBound, suppliedBound⟩
      by_cases hpart : args.length + supplied.length < arity <;>
        simp [destClosure, found, checkLoc, argsBound, suppliedBound, hpart] at rejected
    simp [destClosure, nextFound, checkLoc, ← argsRel.length_eq, ← suppliedRel.length_eq, fail]

/-- Full indirect application of a recursive closure selects the corresponding
numbered body and constructs related recursive environments and remaining
argument lists. -/
theorem destRecclosure_numbered_full (maxApp start index : Nat) (location nextLocation : Option Nat)
    (supplied nextSupplied env nextEnv args nextArgs : List Value)
    (functions : List (Nat × ClosLang.Exp)) (resultBody : ClosLang.Exp) (resultEnv remaining : List Value)
    (suppliedRel : List.Forall₂ (ValueRel maxApp) supplied nextSupplied)
    (envRel : List.Forall₂ (ValueRel maxApp) env nextEnv)
    (argsRel : List.Forall₂ (ValueRel maxApp) args nextArgs)
    (safe : ¬ ClosProps.containsAppSome maxApp (functions.map Prod.snd))
    (run : destClosure maxApp none (.recclosure location supplied env functions index) args =
      some (.fullApp resultBody resultEnv remaining)) :
    ∃ bodyStart nextResultEnv nextRemaining,
      destClosure maxApp none (.recclosure nextLocation nextSupplied nextEnv
        ((functions.map Prod.fst).zip (renumberList start (functions.map Prod.snd)).2) index) nextArgs =
        some (.fullApp (renumber bodyStart resultBody).2 nextResultEnv nextRemaining) ∧
      List.Forall₂ (ValueRel maxApp) resultEnv nextResultEnv ∧
      List.Forall₂ (ValueRel maxApp) remaining nextRemaining ∧
      ¬ ClosProps.containsAppSome maxApp [resultBody] := by
  cases found : functions[index]? with
  | none => simp [destClosure, found] at run
  | some entry =>
    obtain ⟨arity, body⟩ := entry
    obtain ⟨bodyStart, nextFound⟩ := renumberedBundle_getElem functions start index arity body found
    by_cases valid : args.length ≤ maxApp ∧ supplied.length < arity
    · by_cases hpart : args.length + supplied.length < arity
      · simp [destClosure, found, checkLoc, valid.1, valid.2, hpart] at run
      · simp [destClosure, found, checkLoc, valid.1, valid.2, hpart] at run
        obtain ⟨rfl, rfl, rfl⟩ := run
        let needed := arity - supplied.length
        let bundle := (functions.map Prod.fst).zip (renumberList start (functions.map Prod.snd)).2
        let recursive := (List.range bundle.length).map (fun i => Value.recclosure nextLocation [] nextEnv bundle i)
        refine ⟨bodyStart, (nextArgs.reverse.take needed).reverse ++ (nextSupplied ++ recursive ++ nextEnv),
          (nextArgs.reverse.drop needed).reverse, ?_, ?_, ?_, ?_⟩
        · simp [destClosure, nextFound, checkLoc, ← argsRel.length_eq, ← suppliedRel.length_eq,
            valid.1, valid.2, hpart, needed, recursive, bundle]
        · have relatedPrefix := List.rel_reverse (List.forall₂_take needed (List.rel_reverse argsRel))
          have relatedRec := numberedRecclosures_related maxApp start location nextLocation env nextEnv functions envRel safe
          simpa [recursive, bundle, List.append_assoc] using
            List.rel_append relatedPrefix (List.rel_append suppliedRel (List.rel_append relatedRec envRel))
        · exact List.rel_reverse (List.forall₂_drop needed (List.rel_reverse argsRel))
        · exact selectedBody_noAppSome maxApp index arity functions body found safe
    · simp [destClosure, found, checkLoc, valid] at run

/-- Related closure values reject the same indirect applications. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "dest_closure_v_rel_none"]
theorem destClosure_related_none (maxApp : Nat) (source : Value) (args : List Value)
    (target : Value) (nextArgs : List Value)
    (h : ValueRel maxApp source target ∧ List.Forall₂ (ValueRel maxApp) args nextArgs ∧
      destClosure maxApp none source args = none) :
    destClosure maxApp none target nextArgs = none := by
  obtain ⟨related, argsRel, rejected⟩ := h
  cases related with
  | number _ | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ => rfl
  | closure location nextLocation supplied nextSupplied env nextEnv arity start body nextBody envRel suppliedRel safe bodyEq =>
    subst nextBody
    exact destClosure_numbered_none maxApp arity start location nextLocation supplied nextSupplied env nextEnv args nextArgs
      body suppliedRel argsRel rejected
  | recclosure location nextLocation supplied nextSupplied env nextEnv functions nextFunctions index start envRel suppliedRel safe functionsEq =>
    subst nextFunctions
    exact destRecclosure_numbered_none maxApp start index location nextLocation supplied nextSupplied env nextEnv args nextArgs
      functions suppliedRel argsRel rejected

/-- Related closure values preserve successful partial indirect applications. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "dest_closure_v_rel_partial"]
theorem destClosure_related_partial (maxApp : Nat) (result source : Value) (args : List Value)
    (target : Value) (nextArgs : List Value)
    (h : ValueRel maxApp source target ∧ List.Forall₂ (ValueRel maxApp) args nextArgs ∧
      destClosure maxApp none source args = some (.partialApp result)) :
    ∃ nextResult, destClosure maxApp none target nextArgs = some (.partialApp nextResult) ∧
      ValueRel maxApp result nextResult := by
  obtain ⟨related, argsRel, run⟩ := h
  cases related with
  | number _ | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ => simp [destClosure] at run
  | closure location nextLocation supplied nextSupplied env nextEnv arity start body nextBody envRel suppliedRel safe bodyEq =>
    subst nextBody
    exact destClosure_numbered_partial maxApp arity start location nextLocation supplied nextSupplied env nextEnv args nextArgs
      body result suppliedRel envRel argsRel safe run
  | recclosure location nextLocation supplied nextSupplied env nextEnv functions nextFunctions index start envRel suppliedRel safe functionsEq =>
    subst nextFunctions
    exact destRecclosure_numbered_partial maxApp start index location nextLocation supplied nextSupplied env nextEnv args nextArgs
      functions result suppliedRel envRel argsRel safe run

/-- Related closure values preserve successful full indirect applications,
with a numbered body and related argument and over-application environments. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "dest_closure_v_rel_full"]
theorem destClosure_related_full {α : Type} (maxApp : Nat) (body : ClosLang.Exp)
    (_c : α) (source : Value) (args : List Value) (target : Value) (nextArgs env remaining : List Value)
    (h : ValueRel maxApp source target ∧ List.Forall₂ (ValueRel maxApp) args nextArgs ∧
      destClosure maxApp none source args = some (.fullApp body env remaining)) :
    ∃ nextEnv nextRemaining start,
      destClosure maxApp none target nextArgs = some (.fullApp (renumber start body).2 nextEnv nextRemaining) ∧
      List.Forall₂ (ValueRel maxApp) env nextEnv ∧ List.Forall₂ (ValueRel maxApp) remaining nextRemaining ∧
      ¬ ClosProps.containsAppSome maxApp [body] := by
  obtain ⟨related, argsRel, run⟩ := h
  cases related with
  | number _ | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ => simp [destClosure] at run
  | closure location nextLocation supplied nextSupplied captured nextCaptured arity start original nextBody envRel suppliedRel safe bodyEq =>
    subst nextBody
    obtain ⟨nextEnv, nextRemaining, result⟩ := destClosure_numbered_full maxApp arity start location nextLocation
      supplied nextSupplied captured nextCaptured args nextArgs original body env remaining suppliedRel envRel argsRel safe run
    exact ⟨nextEnv, nextRemaining, start, result⟩
  | recclosure location nextLocation supplied nextSupplied captured nextCaptured functions nextFunctions index start envRel suppliedRel safe functionsEq =>
    subst nextFunctions
    obtain ⟨number, nextEnv, nextRemaining, result⟩ :=
      destRecclosure_numbered_full maxApp start index location nextLocation supplied nextSupplied captured nextCaptured args nextArgs
        functions body env remaining suppliedRel envRel argsRel safe run
    exact ⟨nextEnv, nextRemaining, number, result⟩

end Flapjack.Compiler.Backend.ClosNumber
