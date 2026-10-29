import Flapjack.Compiler.Backend.FlatToClos.Proofs.ValueRelation
import Mathlib.Data.List.Forall2

/-! Recursive-environment prerequisites for flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- Building recursive source bindings is an ordered prefix of closures. -/
theorem buildRecEnv_eq_map (funs : List (VarN × VarN × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (initial : List (VarN × FlatSem.Value)) :
    FlatSem.buildRecEnv funs env initial =
      funs.map (fun f => (f.1, FlatSem.Value.recclosure env funs f.1)) ++ initial := by
  unfold FlatSem.buildRecEnv
  have foldMap : ∀ xs : List (VarN × VarN × FlatLang.Exp),
      xs.foldr (fun (f, _, _) acc => (f, FlatSem.Value.recclosure env funs f) :: acc) initial =
        xs.map (fun f => (f.1, FlatSem.Value.recclosure env funs f.1)) ++ initial := by
    intro xs
    induction xs with
    | nil => rfl
    | cons first rest ih =>
      rcases first with ⟨name, arg, body⟩
      simp [ih]
  exact foldMap funs

/-- Each recursive source closure corresponds to the generated closure at
the same index. -/
theorem recClosureList_related (funs : List (VarN × VarN × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (names : List (Option MlString)) (values : List ClosSem.Value)
    (environments : EnvRel env names values) (distinct : (funs.map Prod.fst).Nodup)
    (safe : FlatProps.noMatFuns funs = true) :
    List.Forall₂ ValueRel
      (funs.map (fun f => FlatSem.Value.recclosure env funs f.1))
      ((List.range funs.length).map (fun i => ClosSem.Value.recclosure none [] values
        (compileFuns (funs.map (fun f => some f.1) ++ names) funs) i)) := by
  apply List.forall₂_of_length_eq_of_get
  · simp
  · intro i leftBound rightBound
    have bound : i < funs.length := by simpa using leftBound
    simpa using (ValueRel.recclosure bound environments distinct safe)

/-- Compiling a recursive function group preserves its length. -/
theorem compileFuns_length (names : List (Option MlString)) (funs : List (VarN × VarN × FlatLang.Exp)) :
    (compileFuns names funs).length = funs.length := by
  induction funs with
  | nil => rfl
  | cons first rest ih =>
    rcases first with ⟨name, arg, body⟩
    simp [compileFuns, ih]

/-- Every compiled recursive function has unary arity. -/
theorem compileFuns_unary (names : List (Option MlString)) (funs : List (VarN × VarN × FlatLang.Exp))
    (maxApp : Nat) (positive : 1 ≤ maxApp) :
    (compileFuns names funs).all (fun (arity, _) => arity ≤ maxApp && arity != 0) = true := by
  induction funs with
  | nil => rfl
  | cons first rest ih =>
    rcases first with ⟨name, arg, body⟩
    simp [compileFuns, positive, ih]

/-- Extending both environments with a recursive function group preserves
the proof-side environment relation. -/
theorem envRel_rec (funs : List (VarN × VarN × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (names : List (Option MlString)) (values : List ClosSem.Value)
    (environments : EnvRel env names values) (distinct : (funs.map Prod.fst).Nodup)
    (safe : FlatProps.noMatFuns funs = true) :
    EnvRel { env with v := FlatSem.buildRecEnv funs env env.v }
      (funs.map (fun f => some f.1) ++ names)
      ((List.range (compileFuns (funs.map (fun f => some f.1) ++ names) funs).length).map
        (fun i => ClosSem.Value.recclosure none [] values
          (compileFuns (funs.map (fun f => some f.1) ++ names) funs) i) ++ values) := by
  have prefixRel := recClosureList_related funs env names values environments distinct safe
  have extended := envRel_append
    (entries := funs.map (fun f => (f.1, FlatSem.Value.recclosure env funs f.1)))
    (targets := (List.range funs.length).map (fun i => ClosSem.Value.recclosure none [] values
      (compileFuns (funs.map (fun f => some f.1) ++ names) funs) i))
    environments (by simpa [List.map_map] using prefixRel)
  simpa [buildRecEnv_eq_map, compileFuns_length, List.map_map, Function.comp_def] using extended

end Flapjack.Compiler.Backend.FlatToClos
