module

public import Flapjack.Compiler.Backend.FlatProps.EvaluateList
public import Mathlib.Data.Set.Disjoint

@[expose] public section
/-! Local-variable evaluation properties for the faithful flat evaluator. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL (Result)
/-- Evaluating local variables follows the successful environment lookups. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_MAP_Var_local"]
theorem evaluate_mapVarLocal {C F : Type} (env : Environment Value)
    (xs : List Flapjack.AstHOL.VarN) (vs : List Value) (state : State C F) (trace : Flapjack.Compiler.Backend.BackendCommon.Tra)
    (lookups : xs.map (fun x => env.v.lookup x) = vs.map some) :
    evaluate env state (xs.map (.varLocal trace)) = (state, .val vs) := by
  induction xs generalizing vs with
  | nil =>
    cases vs <;> simp_all [evaluate_nil_source]
  | cons x xs ih =>
    cases vs with
    | nil => simp at lookups
    | cons v vs =>
      simp only [List.map_cons, List.cons.injEq] at lookups
      rw [List.map_cons, evaluate_cons, evaluate_varLocal_source]
      simp [lookups.1, ih vs lookups.2]
/-- Build local-variable expressions from paired source traces and names. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "bind_locals_list_def"]
def bindLocalsList (traces : List Flapjack.Compiler.Backend.BackendCommon.Tra)
    (names : List Flapjack.AstHOL.VarN) : List FlatLang.Exp :=
  List.zipWith FlatLang.Exp.varLocal traces names

/-- Flapjack proof infrastructure: induction over an unshadowed environment suffix. -/
private theorem evaluateVarsAux {C F : Type} (env : Environment Value) (state : State C F)
    (kvs envPre : List (Flapjack.AstHOL.VarN × Value)) (ts : List Flapjack.Compiler.Backend.BackendCommon.Tra)
    (distinct : (kvs.map Prod.fst).Nodup)
    (disjoint : Disjoint {x | x ∈ kvs.map Prod.fst} {x | x ∈ envPre.map Prod.fst})
    (eqEnv : env.v = envPre ++ kvs) (len : ts.length = kvs.length) :
    evaluate env state (bindLocalsList ts (kvs.map Prod.fst)) = (state, .val (kvs.map Prod.snd)) := by
  induction kvs generalizing envPre ts with
  | nil =>
    cases ts <;> simp_all [bindLocalsList, evaluate_nil_source]
  | cons pair rest ih =>
    obtain ⟨key, value⟩ := pair
    cases ts with
    | nil => simp at len
    | cons trace traces =>
      simp only [List.map_cons, List.nodup_cons] at distinct
      have notPrefix : key ∉ envPre.map Prod.fst := by
        intro member
        exact Set.disjoint_left.mp disjoint (by simp) member
      have headLookup : env.v.lookup key = some value := by
        rw [eqEnv, List.lookup_append]
        have absent : envPre.lookup key = none := by
          cases found : envPre.lookup key with
          | none => rfl
          | some v =>
            have isSome : (envPre.lookup key).isSome := by rw [found]; rfl
            obtain ⟨entry, member, eq⟩ := List.lookup_isSome_iff.mp isSome
            have eqKey : key = entry.1 := by simpa using eq
            exact False.elim (notPrefix (List.mem_map.mpr ⟨entry, member, eqKey.symm⟩))
        simp [absent]
      have restDisjoint : Disjoint {x | x ∈ rest.map Prod.fst}
          {x | x ∈ (envPre ++ [(key, value)]).map Prod.fst} := by
        apply Set.disjoint_left.mpr
        intro x inRest inPrefix
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at inPrefix
        rcases inPrefix with inPrefix | equal
        · exact Set.disjoint_left.mp disjoint (by simp only [Set.mem_ofPred_eq, List.map_cons, List.mem_cons]; exact Or.inr inRest) inPrefix
        · subst x
          exact distinct.1 inRest
      have tailEnv : env.v = (envPre ++ [(key, value)]) ++ rest := by simpa [List.append_assoc] using eqEnv
      have tailLen : traces.length = rest.length := by simpa using len
      have tail := ih (envPre ++ [(key, value)]) traces distinct.2 restDisjoint tailEnv tailLen
      simp only [List.map_cons, bindLocalsList, List.zipWith_cons_cons]
      rw [evaluate_cons, evaluate_varLocal_source]
      simp only [bindLocalsList] at tail
      simp [headLookup, tail]

/-- Evaluate local variables drawn from a distinct, unshadowed environment suffix. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "evaluate_vars"]
theorem evaluate_vars {C F : Type} (env : Environment Value) (state : State C F)
    (kvs env' : List (Flapjack.AstHOL.VarN × Value)) (ks : List Flapjack.AstHOL.VarN)
    (vs : List Value) (ts : List Flapjack.Compiler.Backend.BackendCommon.Tra)
    (conditions : (kvs.map Prod.fst).Nodup ∧
      Disjoint {x | x ∈ kvs.map Prod.fst} {x | x ∈ env'.map Prod.fst} ∧
      env.v = env' ++ kvs ∧ ks = kvs.map Prod.fst ∧ vs = kvs.map Prod.snd ∧
      ts.length = ks.length) :
    evaluate env state (bindLocalsList ts ks) = (state, .val vs) := by
  obtain ⟨distinct, disjoint, eqEnv, rfl, rfl, length⟩ := conditions
  exact evaluateVarsAux env state kvs env' ts distinct disjoint eqEnv (by simpa using length)
end Flapjack.Compiler.Backend.FlatProps
