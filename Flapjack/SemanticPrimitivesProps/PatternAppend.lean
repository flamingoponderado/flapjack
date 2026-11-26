module

public import Flapjack.SemanticPrimitivesHOL.PatternMatch
public import Flapjack.SemanticPrimitivesProps.MatchMap

@[expose] public section

/-! Appending environments in source pattern matching. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL

mutual
/-- Pattern matching only adds bindings in front of the incoming environment. -/
private theorem pmatch_append_bindings (envC : Namespace ModN ConN (Nat × Stamp))
    (store : Store Value) (pattern : Pat) (value : Value) (pre suffix : List (VarN × Value)) :
    pmatch envC store pattern value (pre ++ suffix) =
      mapMatch (fun items => items ++ suffix) (pmatch envC store pattern value pre) := by
  cases pattern with
  | pany => simp [pmatch, mapMatch]
  | pvar name => simp [pmatch, mapMatch]
  | plit lit =>
    cases value with
    | litv actual =>
      simp only [pmatch, mapMatch]
      split
      · simp
      · split
        · simp
        · simp
    | conv stamp values => simp [pmatch, mapMatch]
    | closure env name body => simp [pmatch, mapMatch]
    | recclosure env fns name => simp [pmatch, mapMatch]
    | loc b n => simp [pmatch, mapMatch]
    | vectorv values => simp [pmatch, mapMatch]
    | env env genid => simp [pmatch, mapMatch]
  | pas pattern name =>
    simpa [pmatch] using
      pmatch_append_bindings envC store pattern value ((name, value) :: pre) suffix
  | ptannot pattern t =>
    simpa [pmatch] using pmatch_append_bindings envC store pattern value pre suffix
  | pref pattern =>
    cases value with
    | loc flag index =>
      simp only [pmatch, mapMatch]
      cases found : storeLookup index store with
      | none => simp
      | some entry =>
        cases entry with
        | refv contents =>
          exact pmatch_append_bindings envC store pattern contents pre suffix
        | w8array ws => simp
        | varray vs => simp
        | thunk mode v => simp
    | litv lit => simp [pmatch, mapMatch]
    | conv stamp values => simp [pmatch, mapMatch]
    | closure env name body => simp [pmatch, mapMatch]
    | recclosure env fns name => simp [pmatch, mapMatch]
    | vectorv values => simp [pmatch, mapMatch]
    | env env genid => simp [pmatch, mapMatch]
  | pcon name patterns =>
    cases name with
    | none =>
      cases value with
      | conv stamp values =>
        cases stamp with
        | none =>
          simp only [pmatch, mapMatch]
          split
          · exact pmatchList_append_bindings envC store patterns values pre suffix
          · simp
        | some actual => simp [pmatch, mapMatch]
      | litv lit => simp [pmatch, mapMatch]
      | closure env name body => simp [pmatch, mapMatch]
      | recclosure env fns name => simp [pmatch, mapMatch]
      | loc b n => simp [pmatch, mapMatch]
      | vectorv values => simp [pmatch, mapMatch]
      | env env genid => simp [pmatch, mapMatch]
    | some stamp =>
      cases value with
      | conv actualStamp values =>
        cases actualStamp with
        | none => simp [pmatch, mapMatch]
        | some actual =>
          simp only [pmatch, mapMatch]
          cases lookup : nsLookup envC stamp with
          | none => simp
          | some entry =>
            cases entry with
            | mk arity expected =>
              by_cases fits : (sameType expected actual && (patterns.length == arity)) = true
              · by_cases same : sameCtor expected actual = true
                · by_cases lengthOk : (values.length == arity) = true
                  · simp only [if_pos fits, if_pos same, if_pos lengthOk]
                    exact pmatchList_append_bindings envC store patterns values pre suffix
                  · simp only [if_pos fits, if_pos same, if_neg lengthOk]
                · simp only [if_pos fits, if_neg same]
              · simp only [if_neg fits]
      | litv lit => simp [pmatch, mapMatch]
      | closure env name body => simp [pmatch, mapMatch]
      | recclosure env fns name => simp [pmatch, mapMatch]
      | loc b n => simp [pmatch, mapMatch]
      | vectorv values => simp [pmatch, mapMatch]
      | env env genid => simp [pmatch, mapMatch]
termination_by sizeOf pattern

/-- List matching maps successful bindings and preserves the two failures. -/
private theorem pmatchList_append_bindings (envC : Namespace ModN ConN (Nat × Stamp))
    (store : Store Value) (patterns : List Pat) (values : List Value)
    (pre suffix : List (VarN × Value)) :
    pmatchList envC store patterns values (pre ++ suffix) =
      mapMatch (fun items => items ++ suffix) (pmatchList envC store patterns values pre) := by
  cases patterns with
  | nil =>
    cases values with
    | nil => simp [pmatchList, mapMatch]
    | cons value values => simp [pmatchList, mapMatch]
  | cons pattern patterns =>
    cases values with
    | nil => simp [pmatchList, mapMatch]
    | cons value values =>
      have head := pmatch_append_bindings envC store pattern value pre suffix
      cases result : pmatch envC store pattern value pre with
      | typeError => simp [pmatchList, head, result, mapMatch]
      | «match» bindings =>
        simpa [pmatchList, head, result, mapMatch] using
          pmatchList_append_bindings envC store patterns values bindings suffix
      | noMatch =>
        have tail := pmatchList_append_bindings envC store patterns values pre suffix
        cases tailResult : pmatchList envC store patterns values pre with
        | typeError => simp_all [pmatchList, mapMatch]
        | «match» bindings => simp_all [pmatchList, mapMatch]
        | noMatch => simp_all [pmatchList, mapMatch]
termination_by sizeOf patterns
end

/-- Original `pmatch_append`: a successful match keeps the appended suffix on
    the produced bindings. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "pmatch_append"]
theorem pmatch_append :
    (∀ (cenv : Namespace ModN ConN (Nat × Stamp)) (st : Store Value) (p : Pat) (v : Value)
        (env env' env'' : List (VarN × Value)),
      pmatch cenv st p v env = .match env' →
        pmatch cenv st p v (env ++ env'') = .match (env' ++ env'')) ∧
    (∀ (cenv : Namespace ModN ConN (Nat × Stamp)) (st : Store Value) (ps : List Pat)
        (vs : List Value) (env env' env'' : List (VarN × Value)),
      pmatchList cenv st ps vs env = .match env' →
        pmatchList cenv st ps vs (env ++ env'') = .match (env' ++ env'')) := by
  constructor
  · intro cenv st p v env env' env'' found
    simp only [pmatch_append_bindings, found, mapMatch]
  · intro cenv st ps vs env env' env'' found
    simp only [pmatchList_append_bindings, found, mapMatch]

/-- Original `pmatch_acc`: appending the same suffix to the incoming bindings
    preserves every match outcome, with the suffix added to the result. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "pmatch_acc"]
theorem pmatch_acc :
    (∀ (envc : Namespace ModN ConN (Nat × Stamp)) (store : Store Value) (p : Pat) (v : Value)
        (env env' env2 : List (VarN × Value)),
      (pmatch envc store p v env = .match env' ↔
          pmatch envc store p v (env ++ env2) = .match (env' ++ env2)) ∧
        (pmatch envc store p v env = .noMatch ↔
          pmatch envc store p v (env ++ env2) = .noMatch) ∧
        (pmatch envc store p v env = .typeError ↔
          pmatch envc store p v (env ++ env2) = .typeError)) ∧
    (∀ (envc : Namespace ModN ConN (Nat × Stamp)) (store : Store Value) (ps : List Pat)
        (vs : List Value) (env env' env2 : List (VarN × Value)),
      (pmatchList envc store ps vs env = .match env' ↔
          pmatchList envc store ps vs (env ++ env2) = .match (env' ++ env2)) ∧
        (pmatchList envc store ps vs env = .noMatch ↔
          pmatchList envc store ps vs (env ++ env2) = .noMatch) ∧
        (pmatchList envc store ps vs env = .typeError ↔
          pmatchList envc store ps vs (env ++ env2) = .typeError)) := by
  constructor
  · intro envc store p v env env' env2
    rw [pmatch_append_bindings]
    cases h : pmatch envc store p v env with
    | «match» bindings =>
      simp [mapMatch]
    | noMatch =>
      simp [mapMatch]
    | typeError =>
      simp [mapMatch]
  · intro envc store ps vs env env' env2
    rw [pmatchList_append_bindings]
    cases h : pmatchList envc store ps vs env with
    | «match» bindings =>
      simp [mapMatch]
    | noMatch =>
      simp [mapMatch]
    | typeError =>
      simp [mapMatch]

end Flapjack.SemanticPrimitivesProps
