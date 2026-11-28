module

public import Flapjack.SemanticPrimitivesHOL.PatternMatch
public import Flapjack.NamespaceProps.AppendLookup

@[expose] public section

/-! Appending constructor environments in source pattern matching. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL

/-- Appending a constructor environment never changes a pattern-match result
unless the original environment already produced a type error. -/
private theorem pmatch_nsAppend_same (envC : Namespace ModN ConN (Nat × Stamp))
    (store : Store Value) (ns' : Namespace ModN ConN (Nat × Stamp)) :
    (∀ (pattern : Pat) (value : Value) (env : List (VarN × Value)),
        pmatch (nsAppend envC ns') store pattern value env = pmatch envC store pattern value env ∨
          pmatch envC store pattern value env = .typeError) ∧
      (∀ (patterns : List Pat) (values : List Value) (env : List (VarN × Value)),
        pmatchList (nsAppend envC ns') store patterns values env =
            pmatchList envC store patterns values env ∨
          pmatchList envC store patterns values env = .typeError) := by
  apply pmatch.mutual_induct envC store
    (motive1 := fun pattern value env =>
      pmatch (nsAppend envC ns') store pattern value env = pmatch envC store pattern value env ∨
        pmatch envC store pattern value env = .typeError)
    (motive2 := fun patterns values env =>
      pmatchList (nsAppend envC ns') store patterns values env =
          pmatchList envC store patterns values env ∨
        pmatchList envC store patterns values env = .typeError)
  · intro value env
    simp [pmatch]
  · intro value env name
    simp [pmatch]
  · intro env actual
    simp [pmatch]
  · intro env lit actual hne hsame
    simp [pmatch, if_neg hne, if_pos hsame]
  · intro env lit actual hne hnotsame
    simp [pmatch, if_neg hne, if_neg hnotsame]
  · intro env name patterns actual values hnone
    simp [pmatch, hnone]
  · intro env name patterns actual values arity expected hlook fits same lengthOk ih
    have appendLookup : nsLookup (nsAppend envC ns') name = some (arity, expected) :=
      (nsLookup_nsAppend_some envC name ns' (arity, expected)).mpr (Or.inl hlook)
    simp only [pmatch, hlook, appendLookup, if_pos fits, if_pos same, if_pos lengthOk]
    exact ih
  · intro env name patterns actual values arity expected hlook fits same hnotLength
    have appendLookup : nsLookup (nsAppend envC ns') name = some (arity, expected) :=
      (nsLookup_nsAppend_some envC name ns' (arity, expected)).mpr (Or.inl hlook)
    simp only [pmatch, hlook, appendLookup, if_pos fits, if_pos same, if_neg hnotLength]
    exact Or.inl trivial
  · intro env name patterns actual values arity expected hlook fits hnotSame
    have appendLookup : nsLookup (nsAppend envC ns') name = some (arity, expected) :=
      (nsLookup_nsAppend_some envC name ns' (arity, expected)).mpr (Or.inl hlook)
    simp only [pmatch, hlook, appendLookup, if_pos fits, if_neg hnotSame]
    exact Or.inl trivial
  · intro env name patterns actual values arity expected hlook hnotFits
    have appendLookup : nsLookup (nsAppend envC ns') name = some (arity, expected) :=
      (nsLookup_nsAppend_some envC name ns' (arity, expected)).mpr (Or.inl hlook)
    simp only [pmatch, hlook, appendLookup, if_neg hnotFits]
    exact Or.inl trivial
  · intro env patterns values lengthOk ih
    simp only [pmatch, if_pos lengthOk]
    exact ih
  · intro env patterns values hnotLength
    simp only [pmatch, if_neg hnotLength]
    exact Or.inl trivial
  · intro env pattern a index value hstore ih
    simp only [pmatch, hstore]
    exact ih
  · intro env pattern a index hnot
    cases hlook : storeLookup index store with
    | none => simp [pmatch, hlook]
    | some entry =>
      cases entry with
      | refv contents => exact absurd hlook (hnot contents)
      | w8array ws => simp [pmatch, hlook]
      | varray vs => simp [pmatch, hlook]
      | thunk mode v => simp [pmatch, hlook]
  · intro value env pattern name ih
    simp only [pmatch]
    exact ih
  · intro value env pattern a ih
    simp only [pmatch]
    exact ih
  · intro pattern value env hnotAny hnotVar hnotPas hnotTannot hnotLit hnotCon hnotNilCon hnotPref
    cases pattern
    all_goals cases value
    all_goals simp_all [pmatch]
  · intro env
    simp [pmatchList]
  · intro env pattern patterns value values headNoMatch tailError ihHead ihTail
    simp [pmatchList, headNoMatch, tailError]
  · intro env pattern patterns value values headNoMatch htailNotError ihHead ihTail
    have headEq : pmatch (nsAppend envC ns') store pattern value env = .noMatch := by
      rcases ihHead with h | h
      · rw [h, headNoMatch]
      · rw [h] at headNoMatch
        cases headNoMatch
    have tailEq : pmatchList (nsAppend envC ns') store patterns values env =
        pmatchList envC store patterns values env := by
      rcases ihTail with h | h
      · exact h
      · exact absurd h htailNotError
    simp [pmatchList, headEq, tailEq, headNoMatch]
  · intro env pattern patterns value values headError ihHead
    simp [pmatchList, headError]
  · intro env pattern patterns value values env' headMatch ihHead ihTail
    have headEq : pmatch (nsAppend envC ns') store pattern value env = .match env' := by
      rcases ihHead with h | h
      · rw [h, headMatch]
      · rw [h] at headMatch
        cases headMatch
    simp only [pmatchList, headEq, headMatch]
    exact ihTail
  · intro patterns values env hnotNil hnotCons
    cases patterns with
    | nil =>
      cases values with
      | nil => exact absurd rfl (hnotNil rfl)
      | cons value values => simp [pmatchList]
    | cons pattern patterns =>
      cases values with
      | nil => simp [pmatchList]
      | cons value values => exact False.elim (hnotCons pattern patterns value values rfl rfl)

/-- Original `pmatch_nsAppend`: extending the constructor environment keeps
    non-type-error results unchanged. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "pmatch_nsAppend"]
theorem pmatch_nsAppend :
    (∀ (ns : Namespace ModN ConN (Nat × Stamp)) (st : Store Value) (pat : Pat) (v : Value)
        (env m : List (VarN × Value)) (ns' : Namespace ModN ConN (Nat × Stamp)),
      (pmatch ns st pat v env = .noMatch → pmatch (nsAppend ns ns') st pat v env = .noMatch) ∧
        (pmatch ns st pat v env = .match m → pmatch (nsAppend ns ns') st pat v env = .match m)) ∧
    (∀ (ns : Namespace ModN ConN (Nat × Stamp)) (st : Store Value) (pats : List Pat)
        (vs : List Value) (env m : List (VarN × Value)) (ns' : Namespace ModN ConN (Nat × Stamp)),
      (pmatchList ns st pats vs env = .noMatch →
          pmatchList (nsAppend ns ns') st pats vs env = .noMatch) ∧
        (pmatchList ns st pats vs env = .match m →
          pmatchList (nsAppend ns ns') st pats vs env = .match m)) := by
  constructor
  · intro ns st pat v env m ns'
    obtain ⟨same1, _⟩ := pmatch_nsAppend_same ns st ns'
    rcases same1 pat v env with hsame | herr
    · constructor
      · intro noMatch
        rw [hsame, noMatch]
      · intro matched
        rw [hsame, matched]
    · constructor
      · intro noMatch
        rw [herr] at noMatch
        cases noMatch
      · intro matched
        rw [herr] at matched
        cases matched
  · intro ns st pats vs env m ns'
    obtain ⟨_, same2⟩ := pmatch_nsAppend_same ns st ns'
    rcases same2 pats vs env with hsame | herr
    · constructor
      · intro noMatch
        rw [hsame, noMatch]
      · intro matched
        rw [hsame, matched]
    · constructor
      · intro noMatch
        rw [herr] at noMatch
        cases noMatch
      · intro matched
        rw [herr] at matched
        cases matched

/-- Original `pmatch_nsAppend_No_match`: the first direction of
    `pmatch_nsAppend`. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "pmatch_nsAppend_No_match"]
theorem pmatch_nsAppend_noMatch :
    ∀ (ns : Namespace ModN ConN (Nat × Stamp)) (st : Store Value) (pat : Pat) (v : Value)
      (env _m : List (VarN × Value)) (ns' : Namespace ModN ConN (Nat × Stamp)),
      pmatch ns st pat v env = .noMatch → pmatch (nsAppend ns ns') st pat v env = .noMatch :=
  fun ns st pat v env _ ns' => (pmatch_nsAppend.1 ns st pat v env [] ns').1

/-- Original `pmatch_nsAppend_Match`: the second direction of
    `pmatch_nsAppend`. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "pmatch_nsAppend_Match"]
theorem pmatch_nsAppend_match :
    ∀ (ns : Namespace ModN ConN (Nat × Stamp)) (st : Store Value) (pat : Pat) (v : Value)
      (env m : List (VarN × Value)) (ns' : Namespace ModN ConN (Nat × Stamp)),
      pmatch ns st pat v env = .match m → pmatch (nsAppend ns ns') st pat v env = .match m :=
  fun ns st pat v env m ns' => (pmatch_nsAppend.1 ns st pat v env m ns').2

end Flapjack.SemanticPrimitivesProps
