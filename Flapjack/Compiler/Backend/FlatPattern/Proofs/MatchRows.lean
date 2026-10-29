import Flapjack.Compiler.Backend.FlatPattern.Proofs.PatternRelation

/-! Simulations for ordered match rows. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.AstHOL Flapjack.Compiler.Backend.FlatSem

/-- A successful row match returns a pattern and body from the input rows. -/
theorem pmatchRows_match_mem {C F E : Type} (state : FlatSem.State C F) (value : Value)
    (rows : List (FlatLang.Pat × E)) (env : List (VarN × Value)) (pattern : FlatLang.Pat) (body : E)
    (matched : FlatSem.pmatchRows rows state value = .match (env, pattern, body)) :
    (pattern, body) ∈ rows := by
  induction rows with
  | nil => simp [FlatSem.pmatchRows] at matched
  | cons row rows ih =>
    obtain ⟨p, e⟩ := row
    cases head : FlatSem.pmatch state p value [] with
    | typeError => simp [FlatSem.pmatchRows, head] at matched
    | noMatch =>
      have tail : FlatSem.pmatchRows rows state value = .match (env, pattern, body) := by
        simpa [FlatSem.pmatchRows, head] using matched
      exact List.mem_cons_of_mem _ (ih tail)
    | «match» next =>
      cases tail : FlatSem.pmatchRows rows state value <;>
        simp_all [FlatSem.pmatchRows]

/-- Mapping row bodies preserves the first matching pattern and its related
bindings, provided the source row match does not raise a type error. The
proof-side value and state relations remain subject to HOL source review. -/
theorem pmatchRows_map_related {C F E E' : Type} (cfg : Config) (n : Nat)
    (source target : FlatSem.State C F) (value value' : Value) (f : E → E')
    (states : StateRel cfg source target) (values : ValueRel value value')
    (rows : List (FlatLang.Pat × E)) :
    match FlatSem.pmatchRows rows source value with
    | .typeError => True
    | .noMatch => FlatSem.pmatchRows (rows.map fun (p, e) => (p, f e)) target value' = .noMatch
    | .match (env, p, e) =>
      ∃ env', aLookupRel (fun key => decNameToNum key < n) ValueRel env env' ∧
        FlatSem.pmatchRows (rows.map fun (p, e) => (p, f e)) target value' = .match (env', p, f e) := by
  induction rows with
  | nil => simp [FlatSem.pmatchRows]
  | cons row rows ih =>
    obtain ⟨pattern, expression⟩ := row
    cases sourceHead : FlatSem.pmatch source pattern value [] with
    | typeError => simp [FlatSem.pmatchRows, sourceHead]
    | noMatch =>
      have head := pmatch_related cfg n source target pattern value value' [] [] states values
        (aLookupRel_empty _ _) (by simp [sourceHead])
      cases targetHead : FlatSem.pmatch target pattern value' [] with
      | typeError => simp [sourceHead, targetHead, MatchRel] at head
      | «match» _ => simp [sourceHead, targetHead, MatchRel] at head
      | noMatch => simpa [FlatSem.pmatchRows, sourceHead, targetHead] using ih
    | «match» env =>
      have head := pmatch_related cfg n source target pattern value value' [] [] states values
        (aLookupRel_empty _ _) (by simp [sourceHead])
      cases targetHead : FlatSem.pmatch target pattern value' [] with
      | typeError => simp [sourceHead, targetHead, MatchRel] at head
      | noMatch => simp [sourceHead, targetHead, MatchRel] at head
      | «match» env' =>
        have envs : aLookupRel (fun key => decNameToNum key < n) ValueRel env env' := by
          simpa [sourceHead, targetHead, MatchRel] using head
        cases sourceTail : FlatSem.pmatchRows rows source value with
        | typeError => simp [FlatSem.pmatchRows, sourceHead, sourceTail]
        | noMatch =>
          simp only [sourceTail] at ih
          simp [FlatSem.pmatchRows, sourceHead, sourceTail, targetHead, ih, envs]
        | «match» result =>
          rcases result with ⟨tailEnv, tailPattern, tailExpression⟩
          simp only [sourceTail] at ih
          obtain ⟨tailEnv', _, targetTail⟩ := ih
          simp [FlatSem.pmatchRows, sourceHead, sourceTail, targetHead, targetTail, envs]

/-- Compiling match rows preserves their patterns and transforms each body. -/
theorem compileMatch_rows (cfg : Config) (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    (compileMatch cfg rows).2.2 = rows.map (fun (p, e) => (p, (compileExp cfg e).2.2)) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨pattern, expression⟩ := row
    cases head : compileExp cfg expression with
    | mk i rest =>
      cases rest with
      | mk flag body =>
        cases tail : compileMatch cfg rows with
        | mk k rest =>
          cases rest with
          | mk tailFlag bodies =>
            simpa [compileMatch, head, tail] using ih

/-- Compiled rows select the compiled body of the source row and preserve
related bindings, or agree that no row matches. -/
theorem compileMatch_pmatchRows_related {C F : Type} (cfg stateCfg : Config) (n : Nat)
    (source target : FlatSem.State C F) (value value' : Value)
    (states : StateRel stateCfg source target) (values : ValueRel value value')
    (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    match FlatSem.pmatchRows rows source value with
    | .typeError => True
    | .noMatch => FlatSem.pmatchRows (compileMatch cfg rows).2.2 target value' = .noMatch
    | .match (env, p, e) =>
      ∃ env', aLookupRel (fun key => decNameToNum key < n) ValueRel env env' ∧
        FlatSem.pmatchRows (compileMatch cfg rows).2.2 target value' =
          .match (env', p, (compileExp cfg e).2.2) := by
  rw [compileMatch_rows]
  have h := pmatchRows_map_related stateCfg n source target value value' (fun e => (compileExp cfg e).2.2)
    states values rows
  cases result : FlatSem.pmatchRows rows source value with
  | typeError => trivial
  | noMatch => simpa [result] using h
  | «match» selected =>
    rcases selected with ⟨env, pattern, expression⟩
    simpa [result] using h

/-- A successfully selected source row and its compiled counterpart occur at
the same index and produce related bindings. -/
theorem compileMatch_pmatchRows_index {C F : Type} (cfg stateCfg : Config) (n : Nat)
    (source target : FlatSem.State C F) (value value' : Value)
    (states : StateRel stateCfg source target) (values : ValueRel value value')
    (rows : List (FlatLang.Pat × FlatLang.Exp)) (env : List (VarN × Value))
    (pattern : FlatLang.Pat) (body : FlatLang.Exp)
    (matched : FlatSem.pmatchRows rows source value = .match (env, pattern, body)) :
    ∃ (i : Nat) (env' : List (VarN × Value)), rows[i]? = some (pattern, body) ∧
      (compileMatch cfg rows).2.2[i]? = some (pattern, (compileExp cfg body).2.2) ∧
      aLookupRel (fun key => decNameToNum key < n) ValueRel env env' ∧
      FlatSem.pmatchRows (compileMatch cfg rows).2.2 target value' =
        .match (env', pattern, (compileExp cfg body).2.2) := by
  obtain ⟨i, index⟩ := List.mem_iff_getElem?.1 (pmatchRows_match_mem source value rows env pattern body matched)
  have sim := compileMatch_pmatchRows_related cfg stateCfg n source target value value' states values rows
  simp only [matched] at sim
  obtain ⟨env', envs, targetMatch⟩ := sim
  refine ⟨i, env', index, ?_, envs, targetMatch⟩
  simp [compileMatch_rows, List.getElem?_map, index]

end Flapjack.Compiler.Backend.FlatPattern
