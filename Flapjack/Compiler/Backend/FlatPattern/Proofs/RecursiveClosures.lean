import Flapjack.Compiler.Backend.FlatPattern.Proofs.ValueRelationCases

/-! Recursive closure environment and application simulation infrastructure. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.AstHOL Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL (findRecFun)

/-- The original recursive-function body mapping, factored for proofs. -/
def compiledRecFuns (cfg : Config) (funs : List (VarN × VarN × FlatLang.Exp)) : List (VarN × VarN × FlatLang.Exp) :=
  funs.map fun (name, arg, body) => (name, arg, compileDec cfg body)

/-- Compiling recursive bodies leaves function names and argument names
unchanged, and commutes with function lookup. -/
theorem findRecFun_compiled (cfg : Config) (name : VarN) (funs : List (VarN × VarN × FlatLang.Exp)) :
    findRecFun name (compiledRecFuns cfg funs) =
      (findRecFun name funs).map (fun (arg, body) => (arg, compileDec cfg body)) := by
  induction funs with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨fn, arg, body⟩ := head
    change findRecFun name ((fn, arg, compileDec cfg body) :: compiledRecFuns cfg tail) =
      (findRecFun name ((fn, arg, body) :: tail)).map (fun (arg, body) => (arg, compileDec cfg body))
    by_cases same : fn = name
    · subst fn
      simp [findRecFun]
    · simp [findRecFun, same, ih]

/-- A successfully selected recursive body comes from an actual function
entry, so its compiler bound follows from the bundle's bound. -/
theorem findRecFun_member (name arg : VarN) (body : FlatLang.Exp)
    (funs : List (VarN × VarN × FlatLang.Exp))
    (found : findRecFun name funs = some (arg, body)) : (name, arg, body) ∈ funs := by
  induction funs with
  | nil => simp [findRecFun] at found
  | cons head tail ih =>
    obtain ⟨fn, param, expr⟩ := head
    by_cases same : fn = name
    · subst fn
      simp [findRecFun] at found
      obtain ⟨rfl, rfl⟩ := found
      simp
    · simp [findRecFun, same] at found
      exact List.mem_cons_of_mem _ (ih found)

/-- Mapping the bodies does not change the recursive function-name list. -/
theorem compiledRecFuns_names (cfg : Config) (funs : List (VarN × VarN × FlatLang.Exp)) :
    (compiledRecFuns cfg funs).map Prod.fst = funs.map Prod.fst := by
  simp [compiledRecFuns, List.map_map, Function.comp_def]

/-- Recursive environment construction is an ordered binding prefix followed
by the original environment. -/
theorem buildRecEnv_bindings (captured : Environment Value) (funs : List (VarN × VarN × FlatLang.Exp))
    (initial : List (VarN × Value)) :
    FlatSem.buildRecEnv funs captured initial =
      (funs.map fun (name, _, _) => (name, Value.recclosure captured funs name)) ++ initial := by
  have auxiliary : ∀ remaining : List (VarN × VarN × FlatLang.Exp),
      remaining.foldr (fun (name, _, _) tail => (name, Value.recclosure captured funs name) :: tail) initial =
        (remaining.map fun (name, _, _) => (name, Value.recclosure captured funs name)) ++ initial := by
    intro remaining
    induction remaining with
    | nil => rfl
    | cons head tail ih =>
      obtain ⟨name, arg, body⟩ := head
      simp [ih]
  exact auxiliary funs

/-- Recursive environments generated from related captured environments are
related at the same bound. The original global HOL value relation still needs
correspondence review; this is Flapjack proof infrastructure. -/
theorem envRel_buildRec (n : Nat) (left right : Environment Value) (cfg : Config)
    (funs : List (VarN × VarN × FlatLang.Exp)) (envs : EnvRel n left right)
    (bounds : ∀ entry ∈ funs, (compileExp cfg entry.2.2).1 < n) :
    EnvRel n { left with v := FlatSem.buildRecEnv funs left left.v }
      { right with v := FlatSem.buildRecEnv (compiledRecFuns cfg funs) right right.v } := by
  have prefixRel : aLookupRel (fun name => decNameToNum name < n) ValueRel
      (funs.map fun (name, _, _) => (name, Value.recclosure left funs name))
      (funs.map fun (name, _, _) => (name, Value.recclosure right (compiledRecFuns cfg funs) name)) := by
    apply aLookupRel_map_same
    intro entry _
    obtain ⟨name, arg, body⟩ := entry
    constructor
    · rfl
    · intro _
      exact ValueRel.recclosure envs bounds
  apply (envRel_iff_lookup _ _ _).2
  simp only [buildRecEnv_bindings]
  have rightMap : ((compiledRecFuns cfg funs).map fun (name, _, _) =>
      (name, Value.recclosure right (compiledRecFuns cfg funs) name)) =
      (funs.map fun (name, _, _) => (name, Value.recclosure right (compiledRecFuns cfg funs) name)) := by
    simp [compiledRecFuns, List.map_map, Function.comp_def]
  rw [rightMap]
  exact aLookupRel_append _ _ _ _ _ _ prefixRel ((envRel_iff_lookup n left right).1 envs)

/-- Recursive-closure application produces the compiled selected body and
related recursive environments. This is a case of the proof-side simulation;
the HOL value-relation correspondence remains pending. -/
theorem doOpApp_recclosure (leftEnv : Environment Value)
    (funs : List (VarN × VarN × FlatLang.Exp)) (name argName : VarN) (body : FlatLang.Exp)
    (targetClosure arg targetArg : Value)
    (closures : ValueRel (.recclosure leftEnv funs name) targetClosure) (args : ValueRel arg targetArg)
    (distinct : (funs.map Prod.fst).Nodup) (found : findRecFun name funs = some (argName, body)) :
    ∃ i sg body' targetEnv cfg,
      compileExp cfg body = (i, sg, body') ∧
      EnvRel (i + 1) { leftEnv with v := (argName, arg) :: FlatSem.buildRecEnv funs leftEnv leftEnv.v } targetEnv ∧
      FlatSem.doOpApp [targetClosure, targetArg] = some (targetEnv, body') := by
  obtain ⟨n, captured, cfg, envs, bounds, rfl⟩ :=
    (valueRel_recclosure leftEnv funs name targetClosure).1 closures
  have member := findRecFun_member name argName body funs found
  have bodyBound : (compileExp cfg body).1 < n := by simpa using bounds (name, argName, body) member
  have recEnvs := envRel_buildRec n leftEnv captured cfg funs envs bounds
  cases compiled : compileExp cfg body with
  | mk i rest =>
    cases rest with
    | mk sg body' =>
      have smaller : i + 1 ≤ n := by
        have h : i < n := by simpa [compiled] using bodyBound
        exact Nat.succ_le_of_lt h
      have extended := envRel_cons (i + 1)
        { leftEnv with v := FlatSem.buildRecEnv funs leftEnv leftEnv.v }
        { captured with v := FlatSem.buildRecEnv (compiledRecFuns cfg funs) captured captured.v }
        argName arg targetArg (envRel_mono n (i + 1) _ _ recEnvs smaller) args
      refine ⟨i, sg, body',
        { captured with v := (argName, targetArg) :: FlatSem.buildRecEnv (compiledRecFuns cfg funs) captured captured.v },
        cfg, compiled, extended, ?_⟩
      change FlatSem.doOpApp [.recclosure captured (compiledRecFuns cfg funs) name, targetArg] =
        some ({ captured with v := (argName, targetArg) :: FlatSem.buildRecEnv (compiledRecFuns cfg funs) captured captured.v }, body')
      simp [FlatSem.doOpApp, compiledRecFuns_names, distinct, findRecFun_compiled, found, compileDec, compiled]

/-- Function application simulation for arbitrary related input lists. This
is the original result shape over the proof-side value relation; it remains
untagged until that relation's HOL correspondence is reviewed. -/
theorem doOpApp_simulation (source target : List Value) (env : Environment Value) (body : FlatLang.Exp)
    (run : FlatSem.doOpApp source = some (env, body)) (related : List.Forall₂ ValueRel source target) :
    ∃ i sg body' targetEnv cfg,
      compileExp cfg body = (i, sg, body') ∧ EnvRel (i + 1) env targetEnv ∧
      FlatSem.doOpApp target = some (targetEnv, body') := by
  cases source with
  | nil => simp [FlatSem.doOpApp] at run
  | cons funValue rest =>
    cases rest with
    | nil => simp [FlatSem.doOpApp] at run
    | cons arg rest =>
      cases rest with
      | cons extra tail => simp [FlatSem.doOpApp] at run
      | nil =>
        cases related with
        | cons funRel tailRel =>
          cases tailRel with
          | cons argRel endRel =>
            cases endRel with
            | nil =>
              cases funValue with
              | litv _ | conv _ _ | loc _ _ | vectorv _ => simp [FlatSem.doOpApp] at run
              | closure captured name expr =>
                simp [FlatSem.doOpApp] at run
                obtain ⟨rfl, rfl⟩ := run
                exact doOpApp_closure captured name expr _ arg _ funRel argRel
              | recclosure captured funs name =>
                by_cases distinct : (funs.map Prod.fst).Nodup
                · cases found : findRecFun name funs with
                  | none => simp [FlatSem.doOpApp, distinct, found] at run
                  | some entry =>
                    obtain ⟨argName, expr⟩ := entry
                    simp [FlatSem.doOpApp, distinct, found] at run
                    obtain ⟨rfl, rfl⟩ := run
                    exact doOpApp_recclosure captured funs name argName expr _ arg _ funRel argRel distinct found
                · simp [FlatSem.doOpApp, distinct] at run

end Flapjack.Compiler.Backend.FlatPattern
