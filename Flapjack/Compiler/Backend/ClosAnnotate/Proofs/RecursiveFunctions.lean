import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Function
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.EnvironmentExtension

/-! Shared environment and value relations for recursive closure groups. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.DbVars

/-- The free-variable and shifting traversals produce related recursive
function bodies when their captured environments agree at all live slots. -/
theorem functionsRel_annotate (env captured : List Value) (count m : Nat) (index : Spt Nat)
    (functions : List (Nat × ClosLang.Exp)) (length : env.length = m)
    (safe : ∀ arity body, (arity, body) ∈ functions → everyFnVarsNone [body])
    (live : ∀ arity body, (arity, body) ∈ functions → ∀ n,
      altFv n [body] = true → arity + count ≤ n → EnvOk m 0 index env captured (n - (arity + count))) :
    FunctionsRel env captured count functions
      (shiftFuns count m index ((altFreeFuns count functions).map Prod.fst)) := by
  induction functions with
  | nil => exact .nil _ _ _
  | cons first rest ih =>
    obtain ⟨arity, body⟩ := first
    simp only [altFreeFuns, List.map_cons, shiftFuns]
    apply FunctionsRel.cons env captured count arity m body _ index rest _
    · simp [altFree_singleton, shiftList, Nat.add_comm]
    · exact live arity body (by simp)
    · exact safe arity body (by simp)
    · exact length
    · apply ih
      · intro a b member
        exact safe a b (by simp [member])
      · intro a b member
        exact live a b (by simp [member])

/-- The two recursive closure lists created for a related function group
are pointwise related in the order used by the evaluator. -/
theorem recursiveValues_related (location : Option Nat) (env captured : List Value)
    (functions nextFunctions : List (Nat × ClosLang.Exp))
    (related : FunctionsRel env captured functions.length functions nextFunctions) :
    List.Forall₂ ValueRel
      ((List.range functions.length).map (fun i => .recclosure location [] env functions i))
      ((List.range functions.length).map (fun i => .recclosure location [] captured nextFunctions i)) := by
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro i member
  exact ValueRel.recclosure location [] [] env captured functions nextFunctions i related .nil
    (List.mem_range.mp member)

/-- Adding the recursive closures preserves the environment relation at the
free variables of the enclosing letrec body. -/
theorem envOk_recursive_body (names : List Flapjack.Basis.Pure.MlString.MlString)
    (location : Option Nat) (selected : Option (List Nat)) (functions nextFunctions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (m l : Nat) (index : Spt Nat) (env nextEnv captured : List Value)
    (related : FunctionsRel env captured functions.length functions nextFunctions)
    (vars : ∀ n, altFv n [.letrec names location selected functions body] = true → EnvOk m l index env nextEnv n)
    (n : Nat) (present : altFv n [body] = true) :
    EnvOk m (l + functions.length) index
      (((List.range functions.length).map (fun i => Value.recclosure location [] env functions i)) ++ env)
      (((List.range functions.length).map (fun i => Value.recclosure location [] captured nextFunctions i)) ++ nextEnv) n := by
  have frontRel := recursiveValues_related location env captured functions nextFunctions related
  have extended := envOk_extend m l index _ _ env nextEnv n frontRel (by
    intro lower
    have lower' : functions.length ≤ n := by simpa using lower
    simp only [List.length_map, List.length_range]
    apply vars (n - functions.length)
    rw [altFv_letrec]
    have shifted : n - functions.length + functions.length = n := by omega
    simp [shifted, present])
  simpa using extended

/-- The recursive group's live-variable set can be selected from the target
environment, and the resulting compact environment relates every function
body to its annotated counterpart. -/
theorem recursiveFunctions_capture (names : List Flapjack.Basis.Pure.MlString.MlString)
    (location : Option Nat) (selected : Option (List Nat)) (functions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (m l : Nat) (index : Spt Nat) (env nextEnv : List Value)
    (length : env.length = m + l)
    (safe : ∀ arity exp, (arity, exp) ∈ functions → everyFnVarsNone [exp])
    (vars : ∀ n, altFv n [.letrec names location selected functions body] = true → EnvOk m l index env nextEnv n) :
    let live := varsToList (listMkUnion ((altFreeFuns functions.length functions).map Prod.snd))
    let compact := live.filter (· < m + l)
    ∃ captured,
      lookupVars (compact.map (getVar m l index)) nextEnv = some captured ∧
      FunctionsRel env captured functions.length functions
        (shiftFuns functions.length (m + l) (shiftedEnv 0 compact)
          ((altFreeFuns functions.length functions).map Prod.fst)) := by
  dsimp only
  let live := varsToList (listMkUnion ((altFreeFuns functions.length functions).map Prod.snd))
  have distinct : live.Nodup := sptAllDistinctMapFstToAList _
  have liveVars : ∀ n ∈ live, EnvOk m l index env nextEnv n := by
    intro n member
    have inGroup : functions.any (fun (arity, exp) => altFv (n + arity + functions.length) [exp]) = true := by
      have h := (memVarsToList n _).mp member
      simpa [hasVar_recursiveLive] using h
    apply vars n
    rw [altFv_letrec]
    simp [inGroup]
  have bounds : ∀ n ∈ (live.filter (· < m + l)).map (getVar m l index), n < nextEnv.length := by
    intro n member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    have parts := List.mem_filter.mp originalMember
    have tracked : original < l + m := by simp only [decide_eq_true_eq] at parts; omega
    exact (envOk_getVar m l index env nextEnv original (liveVars original parts.1) tracked).2.1
  obtain ⟨captured, captureRun⟩ := lookupVars_exists _ nextEnv bounds
  refine ⟨captured, captureRun, ?_⟩
  apply functionsRel_annotate env captured functions.length (m + l) _ functions length safe
  intro arity exp member n present above
  have liveMember : n - (arity + functions.length) ∈ live := by
    apply (memVarsToList _ _).mpr
    rw [hasVar_recursiveLive]
    apply List.any_eq_true.mpr
    refine ⟨(arity, exp), member, ?_⟩
    have equal : n - (arity + functions.length) + arity + functions.length = n := by omega
    simpa [equal] using present
  exact envOk_shiftedEnv m l index env nextEnv captured _ live (liveVars _ liveMember)
    liveMember distinct captureRun

/-- Related recursive function lists have the same arities in the same order. -/
theorem functionsRel_arities (env captured : List Value) (count : Nat)
    (functions nextFunctions : List (Nat × ClosLang.Exp))
    (related : FunctionsRel env captured count functions nextFunctions) :
    functions.map Prod.fst = nextFunctions.map Prod.fst := by
  induction functions generalizing nextFunctions with
  | nil => cases related; rfl
  | cons first rest ih =>
    cases related with
    | cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ tail => simp [ih _ tail]

/-- Every function body in a syntactically safe recursive group is safe. -/
theorem recursiveFunction_safe (functions : List (Nat × ClosLang.Exp))
    (safe : fnVarsNoneFuns functions) (arity : Nat) (body : ClosLang.Exp)
    (member : (arity, body) ∈ functions) : everyFnVarsNone [body] := by
  induction functions with
  | nil => simp at member
  | cons first rest ih =>
    obtain ⟨a, e⟩ := first
    simp only [fnVarsNoneFuns] at safe
    simp only [List.mem_cons, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | member
    · simpa [everyFnVarsNone] using safe.1
    · exact ih safe.2 member

/-- Recursive closure creation and execution of its body preserve the
candidate annotation simulation. Its evaluator and carriers await HOL review. -/
theorem evaluate_letrec {C F : Type} (names : List Flapjack.Basis.Pure.MlString.MlString)
    (location : Option Nat) (selected : Option (List Nat)) (functions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (bodyIH : EvalSimulation (C := C) (F := F) [body]) :
    EvalSimulation (C := C) (F := F) [.letrec names location selected functions body] := by
  intro env source nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  have safeParts : selected = none ∧ fnVarsNoneFuns functions ∧ everyFnVarsNone [body] := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using safe
  have selectedNone := safeParts.1
  subst selected
  have funSafe : ∀ arity exp, (arity, exp) ∈ functions → everyFnVarsNone [exp] := by
    intro arity exp member
    exact recursiveFunction_safe functions safeParts.2.1 arity exp member
  let live := varsToList (listMkUnion ((altFreeFuns functions.length functions).map Prod.snd))
  let compact := live.filter (· < m + l)
  let nextFunctions := shiftFuns functions.length (m + l) (shiftedEnv 0 compact)
    ((altFreeFuns functions.length functions).map Prod.fst)
  obtain ⟨captured, captureRun, functionsRel⟩ :=
    recursiveFunctions_capture names location none functions body m l index env nextEnv length funSafe vars
  have nextLength : nextFunctions.length = functions.length := by
    simp [nextFunctions, shiftFuns_length, altFreeFuns_length]
  have arities := functionsRel_arities env captured functions.length functions nextFunctions functionsRel
  have validity : functions.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) =
      nextFunctions.all (fun (arity, _) => arity ≤ target.maxApp && arity != 0) := by
    have maxEq := states.2.2.1
    rw [← maxEq]
    have h := congrArg (fun xs : List Nat => xs.all (fun arity => arity ≤ source.maxApp && arity != 0)) arities
    simpa only [List.all_map, Function.comp_def] using h
  by_cases valid : functions.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true
  · have targetValid : nextFunctions.all (fun (arity, _) => arity ≤ target.maxApp && arity != 0) = true := by
      rw [← validity]; exact valid
    let front := (List.range functions.length).map (fun i => Value.recclosure location [] env functions i)
    let nextFront := (List.range functions.length).map (fun i => Value.recclosure location [] captured nextFunctions i)
    have bodyRun : evaluate [body] (front ++ env) source = (result, sourceNext) := by
      simpa [evaluate, valid, front] using run
    have bodyLength : (front ++ env).length = m + (l + functions.length) := by
      simp [front, length]; omega
    have bodyVars : ∀ n, altFv n [body] = true →
        EnvOk m (l + functions.length) index (front ++ env) (nextFront ++ nextEnv) n := by
      intro n present
      exact envOk_recursive_body names location none functions nextFunctions body m l index env nextEnv captured
        functionsRel vars n present
    obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
      bodyIH (front ++ env) source (nextFront ++ nextEnv) target result sourceNext m (l + functions.length) index
        bodyRun noType bodyLength bodyVars safeParts.2.2 code oracle states
    refine ⟨targetResult, targetNext, ?_, resultRel, nextRel⟩
    rw [altFree_letrec]
    simp only [altFree_singleton, Flapjack.holHd, shiftList, shiftSing, List.length_map, Option.getD_some]
    have funEq : functions.map (fun x =>
        ((x.1, (altFreeSing x.2).1), DbVarSet.shift (x.1 + functions.length) (altFreeSing x.2).2)) =
        altFreeFuns functions.length functions := by
      simpa [altFree_singleton, Flapjack.holHd] using (altFreeFuns_as_map functions.length functions).symm
    rw [funEq]
    change evaluate [.letrec names location (some (compact.map (getVar m l index))) nextFunctions
      (shiftSing (altFreeSing body).1 m (l + functions.length) index)] nextEnv target = _
    change lookupVars (compact.map (getVar m l index)) nextEnv = some captured at captureRun
    simp only [evaluate, targetValid, if_true, captureRun]
    simpa [altFree_singleton, shiftList, nextFront, nextLength] using targetRun
  · simp [evaluate, valid] at run
    exact False.elim (noType run.1.symm)

end Flapjack.Compiler.Backend.ClosAnnotate
