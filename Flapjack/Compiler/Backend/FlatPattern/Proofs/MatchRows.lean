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
  have sim :
    match FlatSem.pmatchRows rows source value with
    | .typeError => True
    | .noMatch => FlatSem.pmatchRows (rows.map (fun (p, e) => (p, (compileExp cfg e).2.2))) target value' = .noMatch
    | .match (env, pattern, body) =>
      ∃ i env', i < rows.length ∧ i < (rows.map (fun (p, e) => (p, (compileExp cfg e).2.2))).length ∧
        (pattern, body) = Flapjack.holEl i rows ∧
        aLookupRel (fun key => decNameToNum key < n) ValueRel env env' ∧
        FlatSem.pmatchRows (rows.map (fun (p, e) => (p, (compileExp cfg e).2.2))) target value' =
          .match (env', Flapjack.holEl i (rows.map (fun (p, e) => (p, (compileExp cfg e).2.2)))) := by
    clear compiled matched
    induction rows with
    | nil => simp [FlatSem.pmatchRows]
    | cons row rows ih =>
      obtain ⟨pattern, body⟩ := row
      cases sourceHead : FlatSem.pmatch source pattern value [] with
      | typeError => simp [FlatSem.pmatchRows, sourceHead]
      | noMatch =>
        have head := pmatch_related stateCfg n source target pattern value value' [] [] states values
          (aLookupRel_empty _ _) (by simp [sourceHead])
        cases targetHead : FlatSem.pmatch target pattern value' [] with
        | typeError => simp [sourceHead, targetHead, MatchRel] at head
        | «match» _ => simp [sourceHead, targetHead, MatchRel] at head
        | noMatch =>
          cases sourceTail : FlatSem.pmatchRows rows source value with
          | typeError => simp [FlatSem.pmatchRows, sourceHead, sourceTail]
          | noMatch => simpa [FlatSem.pmatchRows, sourceHead, sourceTail, targetHead] using ih
          | «match» selected =>
            rcases selected with ⟨env, p, e⟩
            simp only [sourceTail] at ih
            simp only [FlatSem.pmatchRows, sourceHead, sourceTail]
            obtain ⟨i, env', bound, bound', atSource, envs, atTarget⟩ := ih
            refine ⟨i+1, env', by simpa using bound, by simpa using bound', ?_, envs, ?_⟩
            · simpa [Flapjack.holEl] using atSource
            · simpa [FlatSem.pmatchRows, sourceHead, targetHead, Flapjack.holEl] using atTarget
      | «match» env =>
        have head := pmatch_related stateCfg n source target pattern value value' [] [] states values
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
            simp only [FlatSem.pmatchRows, sourceHead, sourceTail]
            refine ⟨0, env', by simp, by simp, ?_, envs, ?_⟩
            · simp [Flapjack.holEl, Flapjack.holHd]
            · simp [FlatSem.pmatchRows, targetHead, ih, Flapjack.holEl, Flapjack.holHd]
          | «match» selected =>
            rcases selected with ⟨tailEnv, p, e⟩
            simp only [sourceTail] at ih
            simp only [FlatSem.pmatchRows, sourceHead, sourceTail]
            obtain ⟨i, tailEnv', _, _, _, _, tailTarget⟩ := ih
            refine ⟨0, env', by simp, by simp, ?_, envs, ?_⟩
            · simp [Flapjack.holEl, Flapjack.holHd]
            · simp [FlatSem.pmatchRows, targetHead, tailTarget, Flapjack.holEl, Flapjack.holHd]

  have mapped := compileMatch_rows cfg rows
  rw [compiled] at mapped
  change compiledRows = _ at mapped
  cases result with
  | typeError => trivial
  | noMatch => simpa [matched, ← mapped] using sim
  | «match» selected =>
    rcases selected with ⟨env, pattern, body⟩
    simpa [matched, ← mapped] using sim

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
    apply aLookupRel_mono _ ValueRel env env' _ ValueRel
    refine ⟨envsWide, ?_, ?_⟩
    · intro key h; exact Nat.lt_of_lt_of_le h (Nat.le_max_left _ _)
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
