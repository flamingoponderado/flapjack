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
conditional infrastructure lemma; the guard simulation is established below. -/
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

/-- Simplifying a disjunction preserves evaluation if its left guard is total.
Without this premise, a literal true right guard could hide a left error. -/
theorem dtEvalGuard_mkDisj_of_left_total (refs : HolFiniteMapExact Nat Term) (value : Term)
    (p q : DGuard) (result : Bool) (left : dtEvalGuard refs value p = some result) :
    dtEvalGuard refs value (mkDisj p q) = dtEvalGuard refs value (.disj p q) := by
  cases p <;> cases q <;> cases result <;>
    simp_all [mkDisj, isTrue, dtEvalGuard]

/-- The alternative-pattern guard case, assuming the two recursive simulations. -/
theorem patToGuard_or_at (refs : HolFiniteMapExact Nat Term) (value selected : Term)
    (path : List Nat) (first second : Pat)
    (firstSimulation : pmatch refs first selected ≠ .typeFailure →
      dtEvalGuard refs value (patToGuard path first) =
        some (decide (pmatch refs first selected = .success)))
    (secondSimulation : pmatch refs second selected ≠ .typeFailure →
      dtEvalGuard refs value (patToGuard path second) =
        some (decide (pmatch refs second selected = .success)))
    (safe : pmatch refs (.or first second) selected ≠ .typeFailure) :
    dtEvalGuard refs value (patToGuard path (.or first second)) =
      some (decide (pmatch refs (.or first second) selected = .success)) := by
  cases firstResult : pmatch refs first selected <;>
    cases secondResult : pmatch refs second selected <;>
    simp [pmatch, firstResult, secondResult] at safe ⊢
  all_goals
    have firstGuard := firstSimulation (by simp [firstResult])
    have secondGuard := secondSimulation (by simp [secondResult])
    simp [firstResult] at firstGuard
    simp [secondResult] at secondGuard
    rw [patToGuard, dtEvalGuard_mkDisj_of_left_total refs value _ _ _ firstGuard]
    simp [dtEvalGuard, firstGuard, secondGuard]

/-- The reference-pattern guard case, assuming the recursive pattern simulation. -/
theorem patToGuard_ref_at (refs : HolFiniteMapExact Nat Term) (value selected : Term)
    (path : List Nat) (pattern : Pat)
    (simulation : ∀ path' child, pmatch refs pattern child ≠ .typeFailure →
      walk refs path'.reverse value = some child →
      dtEvalGuard refs value (patToGuard path' pattern) =
        some (decide (pmatch refs pattern child = .success)))
    (walked : walk refs path.reverse value = some selected)
    (safe : pmatch refs (.ref pattern) selected ≠ .typeFailure) :
    dtEvalGuard refs value (patToGuard path (.ref pattern)) =
      some (decide (pmatch refs (.ref pattern) selected = .success)) := by
  cases selected with
  | term _ _ | litv _ | other => simp [pmatch] at safe
  | refPtr address =>
    cases lookup : refs.lookup address with
    | none => simp [pmatch, lookup] at safe
    | some child =>
      have childSafe : pmatch refs pattern child ≠ .typeFailure := by simpa [pmatch, lookup] using safe
      have childWalk : walk refs (0 :: path).reverse value = some child := by
        simp [List.reverse_cons, walk_append, walked, walk, lookup]
      simpa [patToGuard, pmatch, lookup] using simulation (0 :: path) child childSafe childWalk

/-- Extract the constructor fields reached by a traversal, if any. -/
def walkList (refs : HolFiniteMapExact Nat Term) (path : List Nat) (value : Term) : Option (List Term) :=
  match walk refs path value with
  | some (.term _ fields) => some fields
  | _ => none

/-- If a traversal reaches fields with a known prefix, appending the prefix
length to the path reaches the next field. -/
theorem walkList_next (refs : HolFiniteMapExact Nat Term) (value : Term)
    (path : List Nat) (before after : List Term) (next : Term)
    (walked : walkList refs path value = some (before ++ next :: after)) :
    walk refs (path ++ [before.length]) value = some next := by
  cases found : walk refs path value with
  | none => simp [walkList, found] at walked
  | some selected =>
    cases selected with
    | litv _ | refPtr _ | other => simp [walkList, found] at walked
    | term tag fields =>
      have fieldsEq : fields = before ++ next :: after := by simpa [walkList, found] using walked
      subst fields
      rw [walk_append, found]
      simp [walk]

/-- The nonempty tail case of pattern-list guard simulation. -/
theorem patsToGuard_cons_at (refs : HolFiniteMapExact Nat Term) (value : Term)
    (path : List Nat) (before : List Term) (firstValue : Term) (otherValues : List Term)
    (first second : Pat) (otherPatterns : List Pat)
    (walked : walkList refs path.reverse value = some (before ++ firstValue :: otherValues))
    (headSimulation : ∀ path' selected, pmatch refs first selected ≠ .typeFailure →
      walk refs path'.reverse value = some selected →
      dtEvalGuard refs value (patToGuard path' first) =
        some (decide (pmatch refs first selected = .success)))
    (tailSimulation : pmatchList refs (second :: otherPatterns) otherValues ≠ .typeFailure →
      walkList refs path.reverse value = some ((before ++ [firstValue]) ++ otherValues) →
      dtEvalGuard refs value (patsToGuard path (before.length + 1) (second :: otherPatterns)) =
        some (decide (pmatchList refs (second :: otherPatterns) otherValues = .success)))
    (safe : pmatchList refs (first :: second :: otherPatterns) (firstValue :: otherValues) ≠ .typeFailure) :
    dtEvalGuard refs value (patsToGuard path before.length (first :: second :: otherPatterns)) =
      some (decide (pmatchList refs (first :: second :: otherPatterns) (firstValue :: otherValues) = .success)) := by
  have headSafe : pmatch refs first firstValue ≠ .typeFailure := by
    cases head : pmatch refs first firstValue <;>
      cases tail : pmatchList refs (second :: otherPatterns) otherValues <;>
      simp_all [pmatchList]
  have tailSafe : pmatchList refs (second :: otherPatterns) otherValues ≠ .typeFailure := by
    cases head : pmatch refs first firstValue <;>
      cases tail : pmatchList refs (second :: otherPatterns) otherValues <;>
      simp_all [pmatchList]
  have headWalk : walk refs (before.length :: path).reverse value = some firstValue := by
    simpa [List.reverse_cons] using walkList_next refs value path.reverse before otherValues firstValue walked
  have tailWalk : walkList refs path.reverse value = some ((before ++ [firstValue]) ++ otherValues) := by
    simpa [List.append_assoc] using walked
  have headGuard := headSimulation (before.length :: path) firstValue headSafe headWalk
  have tailGuard := tailSimulation tailSafe tailWalk
  rw [patsToGuard, dtEvalGuard_mkConj]
  cases head : pmatch refs first firstValue <;>
    cases tail : pmatchList refs (second :: otherPatterns) otherValues <;>
    simp_all [dtEvalGuard, pmatchList]

/-- The singleton pattern-list guard case. -/
theorem patsToGuard_singleton_at (refs : HolFiniteMapExact Nat Term) (value : Term)
    (path : List Nat) (before : List Term) (selected : Term) (pattern : Pat)
    (walked : walkList refs path.reverse value = some (before ++ [selected]))
    (simulation : ∀ path' child, pmatch refs pattern child ≠ .typeFailure →
      walk refs path'.reverse value = some child →
      dtEvalGuard refs value (patToGuard path' pattern) =
        some (decide (pmatch refs pattern child = .success)))
    (safe : pmatchList refs [pattern] [selected] ≠ .typeFailure) :
    dtEvalGuard refs value (patsToGuard path before.length [pattern]) =
      some (decide (pmatchList refs [pattern] [selected] = .success)) := by
  have headSafe : pmatch refs pattern selected ≠ .typeFailure := by
    cases result : pmatch refs pattern selected <;> simp_all [pmatchList]
  have headWalk : walk refs (before.length :: path).reverse value = some selected := by
    simpa [List.reverse_cons] using walkList_next refs value path.reverse before [] selected walked
  have result := simulation (before.length :: path) selected headSafe headWalk
  cases head : pmatch refs pattern selected <;> simp_all [patsToGuard, pmatchList]

/-- An untagged constructor guard follows its field-list simulation. -/
theorem patToGuard_consNone_at (refs : HolFiniteMapExact Nat Term) (value selected : Term)
    (path : List Nat) (patterns : List Pat)
    (simulation : ∀ path' k fields before,
      pmatchList refs patterns fields ≠ .typeFailure → before.length = k →
      walkList refs path'.reverse value = some (before ++ fields) → fields.length = patterns.length →
      dtEvalGuard refs value (patsToGuard path' k patterns) =
        some (decide (pmatchList refs patterns fields = .success)))
    (walked : walk refs path.reverse value = some selected)
    (safe : pmatch refs (.cons none patterns) selected ≠ .typeFailure) :
    dtEvalGuard refs value (patToGuard path (.cons none patterns)) =
      some (decide (pmatch refs (.cons none patterns) selected = .success)) := by
  cases selected with
  | litv _ | refPtr _ | other => simp [pmatch] at safe
  | term tag fields =>
    cases tag with
    | some actual => simp [pmatch] at safe
    | none =>
      have listSafe : pmatchList refs patterns fields ≠ .typeFailure := by simpa [pmatch] using safe
      have listLength := pmatchList_length refs patterns fields listSafe
      have listWalk : walkList refs path.reverse value = some ([] ++ fields) := by simp [walkList, walked]
      simpa [patToGuard, pmatch] using simulation path 0 fields [] listSafe rfl listWalk listLength

/-- A tagged constructor guard agrees with matching when its field guards do. -/
theorem patToGuard_consSome_at (refs : HolFiniteMapExact Nat Term) (value selected : Term)
    (path : List Nat) (tag : Nat) (siblings : Option (List (Nat × Nat))) (patterns : List Pat)
    (simulation : ∀ path' k fields before,
      pmatchList refs patterns fields ≠ .typeFailure → before.length = k →
      walkList refs path'.reverse value = some (before ++ fields) → fields.length = patterns.length →
      dtEvalGuard refs value (patsToGuard path' k patterns) =
        some (decide (pmatchList refs patterns fields = .success)))
    (walked : walk refs path.reverse value = some selected)
    (safe : pmatch refs (.cons (some (tag, siblings)) patterns) selected ≠ .typeFailure) :
    dtEvalGuard refs value (patToGuard path (.cons (some (tag, siblings)) patterns)) =
      some (decide (pmatch refs (.cons (some (tag, siblings)) patterns) selected = .success)) := by
  cases selected with
  | litv _ | refPtr _ | other => simp [pmatch] at safe
  | term actual fields =>
    cases actual with
    | none => simp [pmatch] at safe
    | some actual =>
      by_cases tagsMatch : tag = actual ∧ patterns.length = fields.length
      · have listSafe : pmatchList refs patterns fields ≠ .typeFailure := by simpa [pmatch, tagsMatch] using safe
        have listWalk : walkList refs path.reverse value = some ([] ++ fields) := by simp [walkList, walked]
        have fieldsGuard := simulation path 0 fields [] listSafe rfl listWalk tagsMatch.2.symm
        simp [patToGuard, dtEvalGuard_mkConj, dtEvalGuard, appPos_getPos, walked,
          dtTest, tagsMatch.1, tagsMatch.2, pmatch, fieldsGuard]
      · have fail : pmatch refs (.cons (some (tag, siblings)) patterns) (.term (some actual) fields) = .failure := by
          simp only [pmatch, tagsMatch, ↓reduceIte] at safe ⊢
          split at safe <;> simp_all
        simp [patToGuard, dtEvalGuard_mkConj, dtEvalGuard, appPos_getPos, walked, dtTest, fail]
        simp_all

mutual
/-- A generated guard agrees with every non-error pattern match reached by
its path. The abstract carriers and matcher remain pending source review. -/
theorem patToGuard_correct (refs : HolFiniteMapExact Nat Term) (value : Term) (pattern : Pat)
    (path : List Nat) (selected : Term)
    (safe : pmatch refs pattern selected ≠ .typeFailure)
    (walked : walk refs path.reverse value = some selected) :
    dtEvalGuard refs value (patToGuard path pattern) =
      some (decide (pmatch refs pattern selected = .success)) := by
  cases pattern with
  | any => simp [patToGuard, dtEvalGuard, pmatch]
  | lit literal => exact patToGuard_lit_at refs value selected path literal walked safe
  | or first second =>
    apply patToGuard_or_at refs value selected path first second
    · intro firstSafe
      exact patToGuard_correct refs value first path selected firstSafe walked
    · intro secondSafe
      exact patToGuard_correct refs value second path selected secondSafe walked
    · exact safe
  | ref pattern =>
    apply patToGuard_ref_at refs value selected path pattern
    · intro path' child childSafe childWalk
      exact patToGuard_correct refs value pattern path' child childSafe childWalk
    · exact walked
    · exact safe
  | cons info patterns =>
    cases info with
    | none =>
      apply patToGuard_consNone_at refs value selected path patterns
      · intro path' k fields before listSafe len listWalk fieldLen
        exact patsToGuard_correct refs value patterns path' k fields before listSafe len listWalk fieldLen
      · exact walked
      · exact safe
    | some info =>
      obtain ⟨tag, siblings⟩ := info
      apply patToGuard_consSome_at refs value selected path tag siblings patterns
      · intro path' k fields before listSafe len listWalk fieldLen
        exact patsToGuard_correct refs value patterns path' k fields before listSafe len listWalk fieldLen
      · exact walked
      · exact safe
termination_by sizeOf pattern

/-- Generated field guards agree with every non-error pattern-list match. -/
theorem patsToGuard_correct (refs : HolFiniteMapExact Nat Term) (value : Term) (patterns : List Pat)
    (path : List Nat) (k : Nat) (fields before : List Term)
    (safe : pmatchList refs patterns fields ≠ .typeFailure) (beforeLen : before.length = k)
    (walked : walkList refs path.reverse value = some (before ++ fields))
    (fieldsLen : fields.length = patterns.length) :
    dtEvalGuard refs value (patsToGuard path k patterns) =
      some (decide (pmatchList refs patterns fields = .success)) := by
  cases patterns with
  | nil =>
    cases fields with
    | nil => simp [patsToGuard, dtEvalGuard, pmatchList]
    | cons _ _ => simp [pmatchList] at safe
  | cons first rest =>
    cases fields with
    | nil => simp [pmatchList] at safe
    | cons firstValue otherValues =>
      subst k
      cases rest with
      | nil =>
        cases otherValues with
        | cons _ _ => simp at fieldsLen
        | nil =>
          apply patsToGuard_singleton_at refs value path before firstValue first walked
          · intro path' child childSafe childWalk
            exact patToGuard_correct refs value first path' child childSafe childWalk
          · exact safe
      | cons second otherPatterns =>
        apply patsToGuard_cons_at refs value path before firstValue otherValues first second otherPatterns walked
        · intro path' child childSafe childWalk
          exact patToGuard_correct refs value first path' child childSafe childWalk
        · intro tailSafe tailWalk
          apply patsToGuard_correct refs value (second :: otherPatterns) path (before.length + 1)
            otherValues (before ++ [firstValue]) tailSafe
          · simp
          · exact tailWalk
          · simpa using fieldsLen
        · exact safe
termination_by sizeOf patterns
end

/-- Compiled decision trees select the same result as safe pattern-row matching.
HOL correspondence for the underlying matcher and map carrier remains pending. -/
theorem patsToCode_correct (refs : HolFiniteMapExact Nat Term) (value : Term)
    (rows : List (Pat × Nat)) (safe : matchRows refs rows value ≠ none) :
    dtEval refs value (patsToCode rows) = matchRows refs rows value := by
  apply patsToCode_of_guard_simulation refs value rows
  · intro pattern patternSafe
    exact patToGuard_correct refs value pattern [] value patternSafe rfl
  · exact safe

/-- The complete pattern compiler is correct if its exhaustiveness analysis
is sound for the reordered rows. The outstanding source theorem establishes
that premise; this conditional lemma is not a port of the source result. -/
theorem comp_correct_of_exhaustiveness (refs : HolFiniteMapExact Nat Term) (value : Term)
    (rows : List (Pat × Nat)) (safe : matchRows refs rows value ≠ none)
    (exhaustiveSound : PatternExh.exhRows (moveConstUp rows) = true →
      matchRows refs (moveConstUp rows) value ≠ some .failure) :
    dtEval refs value (comp rows) = matchRows refs rows value := by
  have movedEq := matchRows_moveConstUp refs value rows safe
  have movedSafe : matchRows refs (moveConstUp rows) value ≠ none := by rw [movedEq]; exact safe
  by_cases exhaustive : PatternExh.exhRows (moveConstUp rows) = true
  · obtain ⟨insertedSafe, insertedEq⟩ := matchRows_insertAny refs value (moveConstUp rows) movedSafe
    have codeEq := patsToCode_correct refs value (insertAny (moveConstUp rows)) insertedSafe
    simpa [comp, exhaustive, insertedEq (exhaustiveSound exhaustive), movedEq] using codeEq
  · have codeEq := patsToCode_correct refs value (moveConstUp rows) movedSafe
    simpa [comp, exhaustive, movedEq] using codeEq

end Flapjack.Compiler.Backend.PatternComp
