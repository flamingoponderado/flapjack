import Flapjack.Compiler.Backend.PatternComp.Proofs.RowSelection

/-! Proof-side traversal and guard lemmas for the pattern compiler. The
abstract term and finite-map carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.PatternComp
open Flapjack PatternCommon PatternSemantics

/-- Traverse constructor fields and references along a list of indices. -/
def walk (refs : HolFiniteMapExact Nat Term) : List Nat → Term → Option Term
  | [], value => some value
  | index :: path, .term _ values => do
    let value ← values[index]?
    walk refs path value
  | 0 :: path, .refPtr address => do
    let value ← refs.lookup address
    walk refs path value
  | _ :: _, _ => none

/-- The position representation and list traversal select the same term. -/
theorem appPos_getPos (refs : HolFiniteMapExact Nat Term) (path : List Nat) (value : Term) :
    appPos refs (getPos path) value = walk refs path value := by
  induction path generalizing value with
  | nil => rfl
  | cons index path ih =>
    cases value with
    | term tag values => simp [getPos, appPos, walk, ih]
    | refPtr address => cases index <;> simp [getPos, appPos, walk, ih]
    | litv lit => simp [getPos, appPos, walk]
    | other => simp [getPos, appPos, walk]

/-- Traversing concatenated paths is sequential traversal. -/
theorem walk_append (refs : HolFiniteMapExact Nat Term) (left right : List Nat) (value : Term) :
    walk refs (left ++ right) value = (walk refs left value).bind (walk refs right) := by
  induction left generalizing value with
  | nil => rfl
  | cons index left ih =>
    cases value with
    | term tag values => simp [walk, ih, Option.bind_assoc]
    | refPtr address => cases index <;> simp [walk, ih, Option.bind_assoc]
    | litv lit => simp [walk]
    | other => simp [walk]

/-- Removing literal-true conjuncts preserves guard evaluation, including errors. -/
theorem dtEvalGuard_mkConj (refs : HolFiniteMapExact Nat Term) (value : Term) (p q : DGuard) :
    dtEvalGuard refs value (mkConj p q) = dtEvalGuard refs value (.conj p q) := by
  have bindTrue (x : Option Bool) :
      x.bind (fun first => if first then some true else some false) = x := by
    cases x with
    | none => rfl
    | some b => cases b <;> rfl
  cases p <;> cases q <;> simp [mkConj, isTrue, dtEvalGuard, bindTrue]

/-- Eliminating a literal-true guard preserves decision-tree evaluation. -/
theorem dtEval_mkIf (refs : HolFiniteMapExact Nat Term) (value : Term)
    (guard : DGuard) (yes no : DTree) :
    dtEval refs value (mkIf guard yes no) = dtEval refs value (.if_ guard yes no) := by
  cases guard <;> simp [mkIf, isTrue, dtEval, dtEvalGuard]

/-- Decision-tree construction preserves a safe row match when every generated
pattern guard has been shown to simulate its corresponding pattern. This is a
conditional infrastructure lemma; proving guard simulation remains open. -/
theorem patsToCode_of_guard_simulation (refs : HolFiniteMapExact Nat Term) (value : Term)
    (rows : List (Pat × Nat))
    (guardSimulation : ∀ pattern, pmatch refs pattern value ≠ .typeFailure →
      dtEvalGuard refs value (patToGuard [] pattern) =
        some (decide (pmatch refs pattern value = .success)))
    (safe : matchRows refs rows value ≠ none) :
    dtEval refs value (patsToCode rows) = matchRows refs rows value := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨pattern, index⟩ := row
    have headSafe : pmatch refs pattern value ≠ .typeFailure :=
      matchRows_member_safe refs value ((pattern, index) :: rows) safe (pattern, index) (by simp)
    have guardEq := guardSimulation pattern headSafe
    cases head : pmatch refs pattern value with
    | typeFailure => exact (headSafe head).elim
    | failure =>
      have tailSafe : matchRows refs rows value ≠ none := by simpa [matchRows, head] using safe
      simpa [patsToCode, dtEval_mkIf, dtEval, guardEq, head, matchRows] using ih tailSafe
    | success =>
      cases tail : matchRows refs rows value with
      | none =>
        have bad : matchRows refs ((pattern, index) :: rows) value = none := by
          rw [matchRows, head, tail]
        exact (safe bad).elim
      | some result => simp [patsToCode, dtEval_mkIf, dtEval, guardEq, head, matchRows, tail]

/-- A pattern-list scan without a type error has equal input lengths. -/
theorem pmatchList_length (refs : HolFiniteMapExact Nat Term) (patterns : List Pat)
    (values : List Term) (safe : pmatchList refs patterns values ≠ .typeFailure) :
    values.length = patterns.length := by
  induction patterns generalizing values with
  | nil => cases values <;> simp_all [pmatchList]
  | cons pattern patterns ih =>
    cases values with
    | nil => simp [pmatchList] at safe
    | cons value values =>
      have tailSafe : pmatchList refs patterns values ≠ .typeFailure := by
        cases head : pmatch refs pattern value <;>
          cases tail : pmatchList refs patterns values <;>
          simp_all [pmatchList]
      simp [ih values tailSafe]

/-- The generated wildcard guard always agrees with wildcard matching. -/
theorem patToGuard_any (refs : HolFiniteMapExact Nat Term) (value : Term) :
    dtEvalGuard refs value (patToGuard [] .any) =
      some (decide (pmatch refs .any value = .success)) := by
  simp [patToGuard, dtEvalGuard, pmatch]

/-- The generated literal guard agrees with every non-error literal match. -/
theorem patToGuard_lit (refs : HolFiniteMapExact Nat Term) (value : Term)
    (literal : Flapjack.AstHOL.Lit) (safe : pmatch refs (.lit literal) value ≠ .typeFailure) :
    dtEvalGuard refs value (patToGuard [] (.lit literal)) =
      some (decide (pmatch refs (.lit literal) value = .success)) := by
  cases value with
  | term _ _ | refPtr _ | other => simp [pmatch] at safe
  | litv actual =>
    simp only [patToGuard, List.reverse_nil, getPos, dtEvalGuard, appPos,
      dtTest, pmatch] at safe ⊢
    split at safe <;> simp_all

/-- A literal guard at any valid path agrees with its non-error match. -/
theorem patToGuard_lit_at (refs : HolFiniteMapExact Nat Term) (value selected : Term)
    (path : List Nat) (literal : Flapjack.AstHOL.Lit)
    (walked : walk refs path.reverse value = some selected)
    (safe : pmatch refs (.lit literal) selected ≠ .typeFailure) :
    dtEvalGuard refs value (patToGuard path (.lit literal)) =
      some (decide (pmatch refs (.lit literal) selected = .success)) := by
  cases selected with
  | term _ _ | refPtr _ | other => simp [pmatch] at safe
  | litv actual =>
    simp only [patToGuard, dtEvalGuard, appPos_getPos, walked, dtTest, pmatch] at safe ⊢
    split at safe <;> simp_all

end Flapjack.Compiler.Backend.PatternComp
