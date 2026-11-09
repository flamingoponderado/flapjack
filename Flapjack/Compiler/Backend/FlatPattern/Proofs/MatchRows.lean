module

public import Flapjack.Compiler.Backend.FlatProps.PatternMatch
public import Flapjack.Compiler.Backend.FlatPattern.Proofs.PatternRelation
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Simulations for ordered match rows. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.AstHOL Flapjack.Compiler.Backend.FlatSem

local instance : Nonempty (FlatLang.Pat × FlatLang.Exp) :=
  ⟨(.pany, .con .none none [])⟩

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

/-- Every row's compiled body and pattern bindings are bounded by the
maximum generated-name measure for the whole match. -/
theorem compileMatch_member_bound (cfg : Config) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (pattern : FlatLang.Pat) (body : FlatLang.Exp) (member : (pattern, body) ∈ rows) :
    (compileExp cfg body).1 ≤ (compileMatch cfg rows).1 ∧
      maxDecName (FlatLang.patBindings pattern) ≤ (compileMatch cfg rows).1 := by
  induction rows with
  | nil => simp at member
  | cons row rows ih =>
    obtain ⟨p, e⟩ := row
    cases head : compileExp cfg e with
    | mk i rest =>
      cases rest with
      | mk flag compiled =>
        cases tail : compileMatch cfg rows with
        | mk k rest =>
          cases rest with
          | mk tailFlag bodies =>
            simp only [List.mem_cons] at member
            rcases member with same | later
            · cases same
              simp only [compileMatch, head, tail]
              omega
            · have bound := ih later
              simp only [tail] at bound
              simp only [compileMatch, head, tail]
              omega

/-- Indexed source rows compile to indexed target rows with their name bounds. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_match_EL"]
theorem compileMatch_index (cfg : Config) (pattern : FlatLang.Pat) (body : FlatLang.Exp)
    (rows compiledRows : List (FlatLang.Pat × FlatLang.Exp)) (k : Nat) (sg : Bool) (i : Nat)
    (premises : compileMatch cfg rows = (k, sg, compiledRows) ∧ i < rows.length ∧
      Flapjack.holEl i rows = (pattern, body)) :
    ∃ bodyBound flag compiledBody,
      compileExp cfg body = (bodyBound, flag, compiledBody) ∧
      Flapjack.holEl i compiledRows = (pattern, compiledBody) ∧
      bodyBound ≤ k ∧ maxDecName (FlatLang.patBindings pattern) ≤ k := by
  obtain ⟨compiled, indexBound, sourceEl⟩ := premises
  have sourceAt : rows[i]? = some (pattern, body) := by
    rw [Flapjack.holEl_eq_getElem i rows indexBound] at sourceEl
    exact List.getElem?_eq_some_iff.mpr ⟨indexBound, sourceEl⟩
  have bound := compileMatch_member_bound cfg rows pattern body (List.mem_of_getElem? sourceAt)
  have rowAt : (compileMatch cfg rows).2.2[i]? = some (pattern, (compileExp cfg body).2.2) := by
    simp [compileMatch_rows, List.getElem?_map, sourceAt]
  have targetBound : i < compiledRows.length := by
    have lengths := congrArg List.length (compileMatch_rows cfg rows)
    simp only [compiled, List.length_map] at lengths
    omega
  rw [compiled] at bound rowAt
  have targetEl : Flapjack.holEl i compiledRows = (pattern, (compileExp cfg body).2.2) := by
    rw [Flapjack.holEl_eq_getElem i compiledRows targetBound]
    exact (List.getElem?_eq_some_iff.mp rowAt).choose_spec
  cases result : compileExp cfg body with
  | mk bodyBound rest =>
    cases rest with
    | mk flag compiledBody =>
      simp only [result] at bound targetEl
      exact ⟨bodyBound, flag, compiledBody, rfl, targetEl, bound.1, bound.2⟩

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

/-- Compiled match rows preserve the source match and its selected row index. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "compile_match_pmatch_rows"]
theorem compileMatch_pmatchRows {C F : Type} (cfg stateCfg : Config)
    (source target : FlatSem.State C F) (value value' : Value) (n : Nat)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) (k : Nat) (sg : Bool)
    (compiledRows : List (FlatLang.Pat × FlatLang.Exp))
    (result : Flapjack.SemanticPrimitivesHOL.MatchResult
      (List (VarN × Value) × FlatLang.Pat × FlatLang.Exp))
    (premises : compileMatch cfg rows = (k, sg, compiledRows) ∧
      StateRel stateCfg source target ∧ ValueRel value value' ∧ k ≤ n ∧
      FlatSem.pmatchRows rows source value = result) :
    match result with
    | .typeError => True
    | .noMatch => FlatSem.pmatchRows compiledRows target value' = .noMatch
    | .match (env, pattern, body) =>
      ∃ i env', i < rows.length ∧ i < compiledRows.length ∧
        (pattern, body) = Flapjack.holEl i rows ∧
        aLookupRel (fun key => decNameToNum key < n) ValueRel env env' ∧
        FlatSem.pmatchRows compiledRows target value' =
          .match (env', Flapjack.holEl i compiledRows) := by
  obtain ⟨compiled, states, values, _, matched⟩ := premises
  have sim := compileMatch_pmatchRows_related cfg stateCfg n source target value value' states values rows
  rw [compiled] at sim
  cases result with
  | typeError => trivial
  | noMatch => simpa [matched] using sim
  | «match» selected =>
    rcases selected with ⟨env, pattern, body⟩
    have membership := (FlatProps.pmatchRows_imp_pmatch rows source value env pattern body matched).2
    obtain ⟨i, sourceAt⟩ := List.mem_iff_getElem?.1 membership
    have indexBound : i < rows.length := (List.getElem?_eq_some_iff.mp sourceAt).choose
    have targetBound : i < compiledRows.length := by
      have lengths := congrArg List.length (compileMatch_rows cfg rows)
      simp only [compiled, List.length_map] at lengths
      omega
    have sourceEl : Flapjack.holEl i rows = (pattern, body) := by
      rw [Flapjack.holEl_eq_getElem i rows indexBound]
      exact (List.getElem?_eq_some_iff.mp sourceAt).choose_spec
    have targetAt : compiledRows[i]? = some (pattern, (compileExp cfg body).2.2) := by
      have mapped := compileMatch_rows cfg rows
      rw [compiled] at mapped
      change compiledRows = _ at mapped
      rw [mapped]
      simp [List.getElem?_map, sourceAt]
    have targetEl : Flapjack.holEl i compiledRows = (pattern, (compileExp cfg body).2.2) := by
      rw [Flapjack.holEl_eq_getElem i compiledRows targetBound]
      exact (List.getElem?_eq_some_iff.mp targetAt).choose_spec
    simp only [matched] at sim
    obtain ⟨env', related, targetMatch⟩ := sim
    exact ⟨i, env', indexBound, targetBound, sourceEl.symm, related, by simpa [targetEl] using targetMatch⟩

/-- The selected compiled row also carries the bounds needed to evaluate
its compiled body under a sufficiently large name bound. -/
theorem compileMatch_pmatchRows_index_bound {C F : Type} (cfg stateCfg : Config) (n : Nat)
    (source target : FlatSem.State C F) (value value' : Value)
    (states : StateRel stateCfg source target) (values : ValueRel value value')
    (rows : List (FlatLang.Pat × FlatLang.Exp)) (env : List (VarN × Value))
    (pattern : FlatLang.Pat) (body : FlatLang.Exp)
    (matched : FlatSem.pmatchRows rows source value = .match (env, pattern, body)) :
    ∃ (i : Nat) (env' : List (VarN × Value)) (bodyBound : Nat) (flag : Bool) (compiledBody : FlatLang.Exp),
      rows[i]? = some (pattern, body) ∧
      compileExp cfg body = (bodyBound, flag, compiledBody) ∧
      (compileMatch cfg rows).2.2[i]? = some (pattern, compiledBody) ∧
      bodyBound ≤ (compileMatch cfg rows).1 ∧
      maxDecName (FlatLang.patBindings pattern) ≤ (compileMatch cfg rows).1 ∧
      aLookupRel (fun key => decNameToNum key < n) ValueRel env env' ∧
      FlatSem.pmatchRows (compileMatch cfg rows).2.2 target value' = .match (env', pattern, compiledBody) := by
  have sim := compileMatch_pmatchRows cfg stateCfg source target value value'
    (max n (compileMatch cfg rows).1) rows (compileMatch cfg rows).1
    (compileMatch cfg rows).2.1 (compileMatch cfg rows).2.2 (.match (env, pattern, body))
    ⟨by cases h : compileMatch cfg rows with | mk a b => cases b; rfl,
      states, values, Nat.le_max_right _ _, matched⟩
  obtain ⟨i, env', indexBound, targetBound, sourceElRev, envsWide, targetMatch⟩ := sim
  have sourceEl := sourceElRev.symm
  have sourceAt : rows[i]? = some (pattern, body) := by
    rw [Flapjack.holEl_eq_getElem i rows indexBound] at sourceEl
    exact List.getElem?_eq_some_iff.mpr ⟨indexBound, sourceEl⟩
  have envs : aLookupRel (fun key => decNameToNum key < n) ValueRel env env' := by
    apply aLookupRel_mono (D := Unit) (E := Unit) _ ValueRel env env' _ ValueRel
    refine ⟨envsWide, ?_, ?_⟩
    · intro key _ _ h; exact Nat.lt_of_lt_of_le h (Nat.le_max_left _ _)
    · intro _ _ _ h; exact h.2
  obtain ⟨bodyBound, flag, compiledBody, compiled, targetEl, bodyLe, patLe⟩ :=
    compileMatch_index cfg pattern body rows (compileMatch cfg rows).2.2 (compileMatch cfg rows).1
      (compileMatch cfg rows).2.1 i ⟨by cases h : compileMatch cfg rows with | mk a b => cases b; rfl, indexBound, sourceEl⟩
  have targetAt : (compileMatch cfg rows).2.2[i]? = some (pattern, compiledBody) := by
    rw [Flapjack.holEl_eq_getElem i _ targetBound] at targetEl
    exact List.getElem?_eq_some_iff.mpr ⟨targetBound, targetEl⟩
  refine ⟨i, env', bodyBound, flag, compiledBody, sourceAt, compiled, targetAt, bodyLe, patLe, envs, ?_⟩
  simpa [targetEl] using targetMatch

end Flapjack.Compiler.Backend.FlatPattern
