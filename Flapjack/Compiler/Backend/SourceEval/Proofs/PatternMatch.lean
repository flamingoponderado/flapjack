module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.StateRelation
public import Flapjack.SemanticPrimitivesHOL.PatternMatch
public import Flapjack.Misc.Pair

@[expose] public section

/-! Pattern matching under the source evaluator's recording relation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.AstHOL Flapjack.NamespaceHOL

/-- Flapjack proof abbreviation for HOL's list of product-related bindings. -/
private def bindRel (es : EvalOracleState) (xs ys : List (VarN × Value)) : Prop :=
  List.Forall₂ (Flapjack.holRprod (· = ·) (ValueRel es)) xs ys

/-- Flapjack induction predicate for one pattern; HOL uses `pmatch_ind`. -/
private def singlePred (es : EvalOracleState) (c : Namespace ModN ConN (Nat × Stamp))
    (left right : Store Value) (p : Pat) : Prop :=
  ∀ x y bs bs', ValueRel es x y → bindRel es bs bs' →
    matchResultRel true (bindRel es) (pmatch c left p x bs) (pmatch c right p y bs')

/-- Flapjack induction predicate for pattern lists; HOL uses `pmatch_ind`. -/
private def listPred (es : EvalOracleState) (c : Namespace ModN ConN (Nat × Stamp))
    (left right : Store Value) (ps : List Pat) : Prop :=
  ∀ xs ys bs bs', List.Forall₂ (ValueRel es) xs ys → bindRel es bs bs' →
    matchResultRel true (bindRel es) (pmatchList c left ps xs bs) (pmatchList c right ps ys bs')

/-- Flapjack proof step for the pattern-list induction. -/
private theorem listCons (es : EvalOracleState) (c : Namespace ModN ConN (Nat × Stamp))
    (left right : Store Value) (pat : Pat) (pats : List Pat)
    (headIH : singlePred es c left right pat) (tailIH : listPred es c left right pats) :
    listPred es c left right (pat :: pats) := by
  intro xs ys bs bs' rel bindings
  cases rel with
  | nil => simp [pmatchList, matchResultRel]
  | @cons x y xs ys head tail =>
    have first := headIH x y bs bs' head bindings
    cases p : pmatch c left pat x bs with
    | typeError => simp [pmatchList, p, matchResultRel]
    | noMatch =>
      have q : pmatch c right pat y bs' = .noMatch := by simpa [p, matchResultRel] using first
      have later := tailIH xs ys bs bs' tail bindings
      cases pr : pmatchList c left pats xs bs with
      | typeError => simp [pmatchList, p, q, pr, matchResultRel]
      | noMatch =>
        have qr : pmatchList c right pats ys bs' = .noMatch := by simpa [pr, matchResultRel] using later
        simp [pmatchList, p, q, pr, qr, matchResultRel]
      | «match» rest =>
        obtain ⟨rest', qr, related⟩ := by simpa [pr, matchResultRel] using later
        simp [pmatchList, p, q, pr, qr, matchResultRel]
    | «match» next =>
      obtain ⟨next', q, related⟩ := by simpa [p, matchResultRel] using first
      simpa [pmatchList, p, q] using tailIH xs ys next next' tail related

/-- Flapjack structural induction supplying the single-pattern case. -/
private theorem singleCore (es : EvalOracleState) (c : Namespace ModN ConN (Nat × Stamp))
    (left right : Store Value) (stores : List.Forall₂ (storeValueRel (ValueRel es)) left right)
    (p : Pat) : singlePred es c left right p := by
  apply Pat.rec (motive_1 := singlePred es c left right) (motive_2 := listPred es c left right)
  case pany =>
    intro x y bs bs' rel bindings
    simpa [pmatch, matchResultRel] using bindings
  case pvar =>
    intro name x y bs bs' rel bindings
    simp only [pmatch, matchResultRel]
    exact ⟨_, rfl, .cons ⟨rfl, rel⟩ bindings⟩
  case plit =>
    intro lit x y bs bs' rel bindings
    cases rel with
    | lit actual =>
      by_cases eq : lit = actual
      · simp [pmatch, eq, matchResultRel, bindings]
      · by_cases same : litSameType lit actual = true
        · simp [pmatch, eq, same, matchResultRel]
        · simp [pmatch, eq, same, matchResultRel]
    | _ => simp [pmatch, matchResultRel]
  case pcon =>
    intro name ps ih x y bs bs' rel bindings
    cases rel with
    | @con xs ys stamp values =>
      have lengths : xs.length = ys.length := by
        induction values with
        | nil => rfl
        | cons _ _ ih => simp [ih]
      cases name with
      | none =>
        cases stamp with
        | none =>
          by_cases h : ps.length = xs.length
          · have h' : ps.length = ys.length := h.trans lengths
            simpa [pmatch, h, h', lengths] using ih xs ys bs bs' values bindings
          · have h' : ps.length ≠ ys.length := by simpa [← lengths] using h
            simp [pmatch, h, h', matchResultRel]
        | some _ => simp [pmatch, matchResultRel]
      | some name =>
        cases stamp with
        | none => simp [pmatch, matchResultRel]
        | some stamp =>
          cases found : nsLookup c name with
          | none => simp [pmatch, found, matchResultRel]
          | some pair =>
            obtain ⟨arity, expected⟩ := pair
            by_cases h : sameType expected stamp = true ∧ ps.length = arity
            · by_cases same : sameCtor expected stamp = true
              · by_cases size : xs.length = arity
                · have size' : ys.length = arity := lengths.symm.trans size
                  simpa [pmatch, found, h.1, h.2, same, size, size'] using ih xs ys bs bs' values bindings
                · have size' : ys.length ≠ arity := by simpa [← lengths] using size
                  simp [pmatch, found, h.1, h.2, same, size, size', matchResultRel]
              · simp [pmatch, found, h.1, h.2, same, matchResultRel]
            · simp [pmatch, found, Bool.and_eq_true, h, matchResultRel]
    | _ => simp [pmatch, matchResultRel]
  case pref =>
    intro pat ih x y bs bs' rel bindings
    cases rel with
    | loc flag index =>
      cases found : storeLookup index left with
      | none => simp [pmatch, found, matchResultRel]
      | some entry =>
        cases entry with
        | refv value =>
          obtain ⟨target, targetFound, entries⟩ := storeValueRel_lookup stores index (.refv value) found
          cases target with
          | refv value' =>
            have vals : ValueRel es value value' := by simpa [storeValueRel] using entries
            simpa [pmatch, found, targetFound] using ih value value' bs bs' vals bindings
          | _ => simp [storeValueRel] at entries
        | _ => simp [pmatch, found, matchResultRel]
    | _ => simp [pmatch, matchResultRel]
  case pas =>
    intro pat name ih x y bs bs' rel bindings
    simpa [pmatch] using ih x y ((name, x) :: bs) ((name, y) :: bs') rel (.cons ⟨rfl, rel⟩ bindings)
  case ptannot =>
    intro pat typ ih x y bs bs' rel bindings
    simpa [pmatch] using ih x y bs bs' rel bindings
  case nil =>
    intro xs ys bs bs' rel bindings
    cases rel with
    | nil => simpa [pmatchList, matchResultRel] using bindings
    | cons _ _ => simp [pmatchList, matchResultRel]
  case cons =>
    intro pat pats headIH tailIH
    exact listCons es c left right pat pats headIH tailIH

/-- Flapjack structural induction supplying the pattern-list case. -/
private theorem listCore (es : EvalOracleState) (c : Namespace ModN ConN (Nat × Stamp))
    (left right : Store Value) (stores : List.Forall₂ (storeValueRel (ValueRel es)) left right)
    (ps : List Pat) : listPred es c left right ps := by
  induction ps with
  | nil =>
    intro xs ys bs bs' rel bindings
    cases rel with
    | nil => simpa [pmatchList, matchResultRel] using bindings
    | cons _ _ => simp [pmatchList, matchResultRel]
  | cons pat pats ih => exact listCons es c left right pat pats (singleCore es c left right stores pat) ih

/-- Related recording states and environments preserve pattern matching. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "pmatch"]
theorem sourcePmatch {Config F : Type} (ci : CompilerInstance Config) (s t : State F)
    (es : EvalOracleState) (env env' : SemEnv Value)
    (premises : stateRel ci s t ∧ es = oracleState t.evalState ∧ envRel (ValueRel es) env env') :
    (∀ (envC : Namespace ModN ConN (Nat × Stamp)) (sRefs : Store Value) (p : Pat)
      (x : Value) (binds : List (VarN × Value)) (y : Value) (binds' : List (VarN × Value)),
      sRefs = s.refs ∧ envC = env.c ∧ ValueRel es x y ∧ List.Forall₂ (Flapjack.holRprod (· = ·) (ValueRel es)) binds binds' →
      matchResultRel true (List.Forall₂ (Flapjack.holRprod (· = ·) (ValueRel es))) (pmatch envC sRefs p x binds) (pmatch env'.c t.refs p y binds')) ∧
    (∀ (envC : Namespace ModN ConN (Nat × Stamp)) (sRefs : Store Value) (ps : List Pat)
      (xs : List Value) (binds : List (VarN × Value)) (ys : List Value) (binds' : List (VarN × Value)),
      sRefs = s.refs ∧ envC = env.c ∧ List.Forall₂ (ValueRel es) xs ys ∧ List.Forall₂ (Flapjack.holRprod (· = ·) (ValueRel es)) binds binds' →
      matchResultRel true (List.Forall₂ (Flapjack.holRprod (· = ·) (ValueRel es))) (pmatchList envC sRefs ps xs binds) (pmatchList env'.c t.refs ps ys binds')) := by
  obtain ⟨⟨decState, oracle, refs, target, stores, _⟩, stateEq, environments⟩ := premises
  subst t
  have oracleEq : es = oracle := by simpa [oracleState] using stateEq
  subst es
  have constructors : env.c = env'.c := environments.1
  constructor
  · intro envC sRefs p x binds y binds'
    rintro ⟨rfl, rfl, values, bindings⟩
    rw [← constructors]
    exact singleCore oracle env.c s.refs refs stores p x y binds binds' values bindings
  · intro envC sRefs ps xs binds ys binds'
    rintro ⟨rfl, rfl, values, bindings⟩
    rw [← constructors]
    exact listCore oracle env.c s.refs refs stores ps xs ys binds binds' values bindings

end Flapjack.Compiler.Backend.SourceEval.Proofs
