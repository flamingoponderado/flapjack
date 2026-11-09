module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Function
public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.EnvironmentExtension

@[expose] public section

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
    · simp [shiftSource_eq_shiftList, altFreeSource_eq_altFree, altFree_singleton, shiftList, Nat.add_comm]
    · intro n ⟨present, bound⟩
      exact live arity body (by simp) n (by simpa only [altFvSource_eq_altFv] using present) bound
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
  have extended := envOk_extend _ _ _ n m l index env nextEnv ⟨frontRel, rfl, by
    intro lower
    have lower' : functions.length ≤ n := by simpa using lower
    simp only [List.length_map, List.length_range]
    apply vars (n - functions.length)
    rw [altFv_letrec]
    have shifted : n - functions.length + functions.length = n := by omega
    simp [shifted, present]⟩
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
  exact envOk_shiftedEnv m l index env nextEnv _ live captured
    ⟨liveVars _ liveMember, liveMember, distinct, captureRun⟩

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

end Flapjack.Compiler.Backend.ClosAnnotate
