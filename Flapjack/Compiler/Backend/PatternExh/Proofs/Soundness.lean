import Flapjack.Compiler.Backend.PatternComp.Proofs.GuardCompilation

/-! Proof-side soundness infrastructure for CakeML's exhaustiveness matrix.
The matcher and finite-map carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.PatternExh
open Flapjack PatternCommon PatternSemantics PatternComp

/-- Combine two pattern results, retaining any type failure. -/
def pand : PmatchResult → PmatchResult → PmatchResult
  | .success, result => result
  | .failure, .typeFailure => .typeFailure
  | .failure, _ => .failure
  | .typeFailure, _ => .typeFailure

@[simp] theorem pand_success_right (x : PmatchResult) : pand x .success = x := by
  cases x <;> rfl

@[simp] theorem pand_typeFailure_iff (x y : PmatchResult) :
    pand x y = .typeFailure ↔ x = .typeFailure ∨ y = .typeFailure := by
  cases x <;> cases y <;> simp [pand]

@[simp] theorem pand_success_iff (x y : PmatchResult) :
    pand x y = .success ↔ x = .success ∧ y = .success := by
  cases x <;> cases y <;> simp [pand]

@[simp] theorem pand_assoc (x y z : PmatchResult) : pand (pand x y) z = pand x (pand y z) := by
  cases x <;> cases y <;> cases z <;> rfl

@[simp] theorem pmatchList_cons (refs : HolFiniteMapExact Nat Term) (pattern : Pat)
    (patterns : List Pat) (value : Term) (values : List Term) :
    pmatchList refs (pattern :: patterns) (value :: values) =
      pand (pmatch refs pattern value) (pmatchList refs patterns values) := by
  cases head : pmatch refs pattern value <;>
    cases tail : pmatchList refs patterns values <;> simp [pmatchList, pand, head, tail]

/-- Matching appended pattern/value segments composes their three-valued results. -/
theorem pmatchList_append (refs : HolFiniteMapExact Nat Term)
    (patterns rest : List Pat) (values more : List Term) (lengths : patterns.length = values.length) :
    pmatchList refs (patterns ++ rest) (values ++ more) =
      pand (pmatchList refs patterns values) (pmatchList refs rest more) := by
  induction patterns generalizing values with
  | nil =>
    cases values <;> simp_all [pmatchList, pand]
  | cons pattern patterns ih =>
    cases values with
    | nil => simp at lengths
    | cons value values =>
      have tailLength : patterns.length = values.length := by simpa using lengths
      simp only [List.cons_append, pmatchList_cons, ih values tailLength, pand_assoc]

@[simp] theorem length_anys (n : Nat) : (anys n).length = n := by
  induction n <;> simp_all [anys]

/-- Wildcard vectors succeed precisely when their widths agree. -/
theorem pmatchList_anys (refs : HolFiniteMapExact Nat Term) (n : Nat) (values : List Term) :
    pmatchList refs (anys n) values = if values.length = n then .success else .typeFailure := by
  induction n generalizing values with
  | zero => cases values <;> simp [anys, pmatchList]
  | succ n ih =>
    cases values with
    | nil => simp [anys, pmatchList]
    | cons value values => simp [anys, pmatch, pand, ih]

/-- A successful row scan cannot return failure when a row matched. -/
theorem matchRows_exists_success (refs : HolFiniteMapExact Nat Term) (value : Term)
    (rows : List (Pat × Nat)) (safe : matchRows refs rows value ≠ none)
    (hit : ∃ row ∈ rows, pmatch refs row.1 value = .success) :
    matchRows refs rows value ≠ some .failure := by
  induction rows with
  | nil => simp at hit
  | cons row rows ih =>
    obtain ⟨pattern, index⟩ := row
    cases head : pmatch refs pattern value with
    | typeFailure => simp [matchRows, head] at safe
    | success =>
      cases tail : matchRows refs rows value <;> simp_all [matchRows]
    | failure =>
      have tailSafe : matchRows refs rows value ≠ none := by simpa [matchRows, head] using safe
      have tailHit : ∃ row ∈ rows, pmatch refs row.1 value = .success := by
        rcases hit with ⟨candidate, member, matched⟩
        simp only [List.mem_cons] at member
        rcases member with equal | member
        · subst candidate
          simp [head] at matched
        · exact ⟨candidate, member, matched⟩
      simpa [matchRows, head] using ih tailSafe tailHit

/-- A row retained by the default matrix matches the remaining values in
exactly the same way as the original row matches the full vector. -/
theorem defaultRow_match (refs : HolFiniteMapExact Nat Term) (value : Term) (values : List Term)
    (original row : List Pat) (member : row ∈ defaultRow original) :
    pmatchList refs row values = pmatchList refs original (value :: values) := by
  cases original with
  | nil => simp [defaultRow] at member
  | cons pattern rest =>
    cases pattern <;> simp_all [defaultRow, pmatchList_cons, pmatch, pand]

/-- Every default-matrix row corresponds to a row in the original matrix. -/
theorem defaultMat_member (refs : HolFiniteMapExact Nat Term) (value : Term) (values : List Term)
    (matrix : List (List Pat)) (row : List Pat) (member : row ∈ defaultMat matrix) :
    ∃ original ∈ matrix, pmatchList refs row values = pmatchList refs original (value :: values) := by
  induction matrix with
  | nil => simp [defaultMat] at member
  | cons first rest ih =>
    simp only [defaultMat, List.mem_append] at member
    rcases member with here | later
    · exact ⟨first, by simp, defaultRow_match refs value values first row here⟩
    · obtain ⟨original, originalMember, result⟩ := ih later
      exact ⟨original, List.mem_cons_of_mem _ originalMember, result⟩

/-- Rows generated for a list of constructors contain each corresponding
specialized matrix. -/
theorem specMat_mem_specMats (constructors : List Ctor) (constructor : Ctor)
    (matrix : List (List Pat)) (member : constructor ∈ constructors) :
    specMat constructor matrix ∈ specMats constructors matrix := by
  induction constructors with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · simp [specMats]
    · simp [specMats, ih member]

/-- Extract the constructor class and arguments of a term or valid reference. -/
def destVal (refs : HolFiniteMapExact Nat Term) : Term → Option (Ctor × List Term)
  | .term (some tag) fields => some (.tagC tag fields.length, fields)
  | .term none fields => some (.tupC fields.length, fields)
  | .refPtr address => (refs.lookup address).map (fun value => (.refC, [value]))
  | .litv _ | .other => none

/-- The argument vector extracted from a value has the constructor's arity. -/
theorem destVal_length (refs : HolFiniteMapExact Nat Term) (value : Term)
    (constructor : Ctor) (fields : List Term)
    (found : destVal refs value = some (constructor, fields)) :
    fields.length = ctorArity constructor := by
  cases value with
  | litv _ | other => simp [destVal] at found
  | term tag values =>
    cases tag <;> simp only [destVal, Option.some.injEq, Prod.mk.injEq] at found <;>
      rcases found with ⟨rfl, rfl⟩ <;> rfl
  | refPtr address =>
    cases lookup : refs.lookup address with
    | none => simp [destVal, lookup] at found
    | some val =>
      simp only [destVal, lookup, Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
      rcases found with ⟨rfl, rfl⟩
      rfl

/-- Duplicate removal preserves constructor membership. -/
theorem mem_ctorNub (constructors : List Ctor) (constructor : Ctor) :
    constructor ∈ ctorNub constructors ↔ constructor ∈ constructors := by
  induction constructors with
  | nil => simp [ctorNub]
  | cons first rest ih =>
    by_cases member : first ∈ rest <;> simp_all [ctorNub]

/-- Constructor intersection retains exactly the constructors in both lists. -/
theorem mem_ctorKeep (left right : List Ctor) (constructor : Ctor) :
    constructor ∈ ctorKeep left right ↔ constructor ∈ left ∧ constructor ∈ right := by
  induction left with
  | nil => simp [ctorKeep]
  | cons first rest ih =>
    by_cases member : first ∈ right
    · simp only [ctorKeep, if_pos member, List.mem_cons, ih]
      constructor
      · intro h
        rcases h with equal | both
        · exact ⟨Or.inl equal, equal ▸ member⟩
        · exact ⟨Or.inr both.1, both.2⟩
      · intro ⟨h, inRight⟩
        rcases h with equal | inRest
        · exact Or.inl equal
        · exact Or.inr ⟨inRest, inRight⟩
    · simp only [ctorKeep, if_neg member, List.mem_cons, ih]
      constructor
      · intro ⟨inRest, inRight⟩
        exact ⟨Or.inr inRest, inRight⟩
      · intro ⟨h, inRight⟩
        rcases h with equal | inRest
        · exact (member (equal ▸ inRight)).elim
        · exact ⟨inRest, inRight⟩

/-- Specializing a row preserves its match against the extracted arguments. -/
theorem specRow_match (refs : HolFiniteMapExact Nat Term) (value : Term) (values : List Term)
    (constructor : Ctor) (fields : List Term) (original row : List Pat)
    (found : destVal refs value = some (constructor, fields)) (member : row ∈ specRow constructor original) :
    pmatchList refs row (fields ++ values) = pmatchList refs original (value :: values) := by
  cases original with
  | nil => simp [specRow] at member
  | cons pattern rest =>
    cases pattern with
    | lit _ | or _ _ => simp [specRow] at member
    | any =>
      simp only [specRow, List.mem_singleton] at member
      subst row
      have lengthEq := destVal_length refs value constructor fields found
      rw [pmatchList_append refs (anys (ctorArity constructor)) rest fields values (by simp [lengthEq])]
      simp [pmatchList_anys, lengthEq, pmatch, pand]
    | ref pattern =>
      by_cases isRef : constructor = .refC
      · subst constructor
        simp only [specRow, ↓reduceIte, List.mem_singleton] at member
        subst row
        cases value with
        | litv _ | other => simp [destVal] at found
        | term tag fields' => cases tag <;> simp [destVal] at found
        | refPtr address =>
          cases lookup : refs.lookup address with
          | none => simp [destVal, lookup] at found
          | some child =>
            simp only [destVal, lookup, Option.map_some, Option.some.injEq, Prod.mk.injEq,
              true_and] at found
            subst fields
            simp [pmatch, lookup]
      · simp [specRow, isRef] at member
    | cons info patterns =>
      cases info with
      | none =>
        by_cases ctorEq : constructor = .tupC patterns.length
        · subst constructor
          simp only [specRow, ↓reduceIte, List.mem_singleton] at member
          subst row
          cases value with
          | litv _ | other => simp [destVal] at found
          | refPtr address => cases lookup : refs.lookup address <;> simp [destVal, lookup] at found
          | term tag args =>
            cases tag with
            | some actual => simp [destVal] at found
            | none =>
              simp only [destVal, Option.some.injEq, Prod.mk.injEq, Ctor.tupC.injEq] at found
              obtain ⟨lengthEq, rfl⟩ := found
              rw [pmatchList_append refs patterns rest args values lengthEq.symm]
              simp [pmatch]
        · simp [specRow, ctorEq] at member
      | some info =>
        obtain ⟨tag, siblings⟩ := info
        by_cases ctorEq : constructor = .tagC tag patterns.length
        · subst constructor
          simp only [specRow, ↓reduceIte, List.mem_singleton] at member
          subst row
          cases value with
          | litv _ | other => simp [destVal] at found
          | refPtr address => cases lookup : refs.lookup address <;> simp [destVal, lookup] at found
          | term actual args =>
            cases actual with
            | none => simp [destVal] at found
            | some actual =>
              simp only [destVal, Option.some.injEq, Prod.mk.injEq, Ctor.tagC.injEq] at found
              obtain ⟨⟨rfl, lengthEq⟩, rfl⟩ := found
              rw [pmatchList_append refs patterns rest args values lengthEq.symm]
              simp [pmatch, lengthEq]
        · simp [specRow, ctorEq] at member

/-- Each row of a specialized matrix comes from an equally matching source row. -/
theorem specMat_member (refs : HolFiniteMapExact Nat Term) (value : Term) (values : List Term)
    (constructor : Ctor) (fields : List Term) (matrix : List (List Pat)) (row : List Pat)
    (found : destVal refs value = some (constructor, fields)) (member : row ∈ specMat constructor matrix) :
    ∃ original ∈ matrix, pmatchList refs row (fields ++ values) =
      pmatchList refs original (value :: values) := by
  induction matrix with
  | nil => simp [specMat] at member
  | cons first rest ih =>
    simp only [specMat, List.mem_append] at member
    rcases member with here | later
    · exact ⟨first, by simp, specRow_match refs value values constructor fields first row found here⟩
    · obtain ⟨original, inRest, result⟩ := ih later
      exact ⟨original, List.mem_cons_of_mem _ inRest, result⟩

/-- Tagged constructor membership corresponds to sibling-pair membership. -/
theorem mem_tagCtors (siblings : List (Nat × Nat)) (tag arity : Nat) :
    Ctor.tagC tag arity ∈ tagCtors siblings ↔ (tag, arity) ∈ siblings := by
  induction siblings with
  | nil => simp [tagCtors]
  | cons sibling rest ih =>
    obtain ⟨otherTag, otherArity⟩ := sibling
    simp [tagCtors, ih]

/-- An accepted pattern constructor set contains the class of any value
that does not make the pattern type-fail. -/
theorem ctorsOf_sound (refs : HolFiniteMapExact Nat Term) (pattern : Pat) (value : Term)
    (constructors : List Ctor) (known : ctorsOf pattern = some constructors)
    (safe : pmatch refs pattern value ≠ .typeFailure) :
    ∃ constructor fields, destVal refs value = some (constructor, fields) ∧ constructor ∈ constructors := by
  cases pattern with
  | any | lit _ | or _ _ => simp [ctorsOf] at known
  | ref pattern =>
    simp [ctorsOf] at known
    subst constructors
    cases value with
    | litv _ | other | term _ _ => simp [pmatch] at safe
    | refPtr address =>
      cases lookup : refs.lookup address with
      | none => simp [pmatch, lookup] at safe
      | some child => exact ⟨.refC, [child], by simp [destVal, lookup], by simp⟩
  | cons info patterns =>
    cases info with
    | none =>
      simp [ctorsOf] at known
      subst constructors
      cases value with
      | litv _ | other | refPtr _ => simp [pmatch] at safe
      | term tag fields =>
        cases tag with
        | some actual => simp [pmatch] at safe
        | none =>
          have listSafe : pmatchList refs patterns fields ≠ .typeFailure := by simpa [pmatch] using safe
          have sameLength := pmatchList_length refs patterns fields listSafe
          exact ⟨.tupC fields.length, fields, rfl, by simp [sameLength]⟩
    | some info =>
      obtain ⟨tag, siblings⟩ := info
      cases siblings with
      | none => simp [ctorsOf] at known
      | some siblings =>
        simp [ctorsOf] at known
        subst constructors
        cases value with
        | litv _ | other | refPtr _ => simp [pmatch] at safe
        | term actual fields =>
          cases actual with
          | none => simp [pmatch] at safe
          | some actual =>
            refine ⟨.tagC actual fields.length, fields, rfl, ?_⟩
            rw [mem_ctorNub]
            simp only [List.mem_cons, Ctor.tagC.injEq, mem_tagCtors]
            by_cases same : tag = actual ∧ patterns.length = fields.length
            · exact Or.inl ⟨same.1.symm, same.2.symm⟩
            · right
              have sibling : isSibling (actual, fields.length) (some siblings) = true := by
                simpa [pmatch, same] using safe
              simpa [isSibling] using sibling

/-- If a column provides constructor information and its rows are safe,
the current value has a constructor in that information. -/
theorem colCtors_sound (refs : HolFiniteMapExact Nat Term) (value : Term) (values : List Term)
    (matrix : List (List Pat)) (constructors : List Ctor)
    (known : colCtors matrix = some constructors)
    (safe : ∀ row ∈ matrix, pmatchList refs row (value :: values) ≠ .typeFailure) :
    ∃ constructor fields, destVal refs value = some (constructor, fields) ∧ constructor ∈ constructors := by
  induction matrix generalizing constructors with
  | nil => simp [colCtors] at known
  | cons row rest ih =>
    have tailSafe : ∀ row ∈ rest, pmatchList refs row (value :: values) ≠ .typeFailure := by
      intro candidate member
      exact safe candidate (List.mem_cons_of_mem _ member)
    cases row with
    | nil => exact ih constructors (by simpa [colCtors] using known) tailSafe
    | cons pattern patterns =>
      have headSafe : pmatch refs pattern value ≠ .typeFailure := by
        have rowSafe := safe (pattern :: patterns) (by simp)
        simpa using (by
          intro bad
          apply rowSafe
          simp [bad] : pmatch refs pattern value ≠ .typeFailure)
      cases headInfo : ctorsOf pattern with
      | none => exact ih constructors (by simpa [colCtors, headInfo, ctorInter] using known) tailSafe
      | some headCtors =>
        obtain ⟨headCtor, headFields, headFound, headMember⟩ :=
          ctorsOf_sound refs pattern value headCtors headInfo headSafe
        cases tailInfo : colCtors rest with
        | none =>
          have equality : headCtors = constructors := by simpa [colCtors, headInfo, tailInfo, ctorInter] using known
          subst constructors
          exact ⟨headCtor, headFields, headFound, headMember⟩
        | some tailCtors =>
          have equality : ctorKeep headCtors tailCtors = constructors := by
            simpa [colCtors, headInfo, tailInfo, ctorInter] using known
          obtain ⟨tailCtor, tailFields, tailFound, tailMember⟩ := ih tailCtors tailInfo tailSafe
          have same : (headCtor, headFields) = (tailCtor, tailFields) := Option.some.inj (headFound.symm.trans tailFound)
          have ctorSame : headCtor = tailCtor := congrArg Prod.fst same
          subst tailCtor
          subst constructors
          exact ⟨headCtor, headFields, headFound, (mem_ctorKeep headCtors tailCtors headCtor).mpr ⟨headMember, tailMember⟩⟩

/-- A matrix accepted by the exhaustiveness checker contains a matching row
whenever every row is free of type errors. -/
theorem exhMatrix_sound (matrix : List (List Pat)) :
    ∀ (refs : HolFiniteMapExact Nat Term) (values : List Term),
      exhMatrix matrix = true →
      (∀ row ∈ matrix, pmatchList refs row values ≠ .typeFailure) →
      ∃ row ∈ matrix, pmatchList refs row values = .success := by
  refine exhMatrix.induct
    (motive1 := fun matrix => ∀ (refs : HolFiniteMapExact Nat Term) (values : List Term),
      exhMatrix matrix = true →
      (∀ row ∈ matrix, pmatchList refs row values ≠ .typeFailure) →
      ∃ row ∈ matrix, pmatchList refs row values = .success)
    (motive2 := fun matrices => ∀ (matrix : List (List Pat)), matrix ∈ matrices →
      ∀ (refs : HolFiniteMapExact Nat Term) (values : List Term),
        exhMats matrices = true →
        (∀ row ∈ matrix, pmatchList refs row values ≠ .typeFailure) →
        ∃ row ∈ matrix, pmatchList refs row values = .success)
    ?_ ?_ ?_ ?_ ?_ ?_ matrix
  · intro refs values accepted
    simp [exhMatrix] at accepted
  · intro row rows empty refs values accepted safe
    cases row with
    | cons first rest => simp at empty
    | nil =>
      cases values with
      | nil => exact ⟨[], by simp, by simp [pmatchList]⟩
      | cons value values =>
        have bad := safe [] (by simp)
        simp [pmatchList] at bad
  · intro row rows nonempty unknown ih refs values accepted safe
    have defaultAccepted : exhMatrix (defaultMat (row :: rows)) = true := by
      rw [exhMatrix] at accepted
      split at accepted
      · simp_all
      · split at accepted <;> simp_all
    cases values with
    | nil =>
      cases row with
      | nil => simp at nonempty
      | cons first rest =>
        have bad := safe (first :: rest) (by simp)
        simp [pmatchList] at bad
    | cons value values =>
      have defaultSafe : ∀ r ∈ defaultMat (row :: rows), pmatchList refs r values ≠ .typeFailure := by
        intro r member
        obtain ⟨original, originalMember, result⟩ := defaultMat_member refs value values (row :: rows) r member
        rw [result]
        exact safe original originalMember
      obtain ⟨r, member, hit⟩ := ih refs values defaultAccepted defaultSafe
      obtain ⟨original, originalMember, result⟩ := defaultMat_member refs value values (row :: rows) r member
      exact ⟨original, originalMember, result ▸ hit⟩
  · intro row rows nonempty constructors known ih refs values accepted safe
    have allAccepted : exhMats (specMats constructors (row :: rows)) = true := by
      rw [exhMatrix] at accepted
      split at accepted
      · simp_all
      · split at accepted <;> simp_all
    cases values with
    | nil =>
      cases row with
      | nil => simp at nonempty
      | cons first rest =>
        have bad := safe (first :: rest) (by simp)
        simp [pmatchList] at bad
    | cons value values =>
      obtain ⟨constructor, fields, found, member⟩ := colCtors_sound refs value values (row :: rows) constructors known safe
      have specializedSafe : ∀ r ∈ specMat constructor (row :: rows),
          pmatchList refs r (fields ++ values) ≠ .typeFailure := by
        intro r inMatrix
        obtain ⟨original, originalMember, result⟩ :=
          specMat_member refs value values constructor fields (row :: rows) r found inMatrix
        rw [result]
        exact safe original originalMember
      obtain ⟨r, inMatrix, hit⟩ := ih (specMat constructor (row :: rows))
        (specMat_mem_specMats constructors constructor (row :: rows) member)
        refs (fields ++ values) allAccepted specializedSafe
      obtain ⟨original, originalMember, result⟩ :=
        specMat_member refs value values constructor fields (row :: rows) r found inMatrix
      exact ⟨original, originalMember, result ▸ hit⟩
  · intro matrix member
    simp at member
  · intro first rest ihFirst ihRest matrix member refs values accepted safe
    have both : exhMatrix first = true ∧ exhMats rest = true := by simpa [exhMats] using accepted
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ihFirst refs values both.1 safe
    · exact ihRest matrix member refs values both.2 safe

/-- Prefixing rows preserves their membership witnesses. -/
theorem mem_addHead {α : Type} (item : α) (rows : List (List α)) (row : List α) :
    row ∈ addHead item rows ↔ ∃ rest ∈ rows, row = item :: rest := by
  induction rows with
  | nil => simp [addHead]
  | cons first rest ih => simp [addHead, ih, eq_comm]

/-- Membership in a Cartesian product gives one choice from each input. -/
theorem mem_mkProds {α : Type} (items : List α) (rows : List (List α)) (row : List α) :
    row ∈ mkProds items rows ↔ ∃ item ∈ items, ∃ rest ∈ rows, row = item :: rest := by
  induction items with
  | nil => simp [mkProds]
  | cons first rest ih => simp [mkProds, mem_addHead, ih, eq_comm]

/-- Expanded reference patterns retain their original alternatives. -/
theorem mem_mkRefs (patterns : List Pat) (pattern : Pat) :
    pattern ∈ mkRefs patterns ↔ ∃ original ∈ patterns, pattern = .ref original := by
  induction patterns with
  | nil => simp [mkRefs]
  | cons first rest ih => simp [mkRefs, ih, eq_comm]

/-- Expanded constructor patterns retain their argument rows. -/
theorem mem_mkConses (info : Option (Nat × Option (List (Nat × Nat))))
    (rows : List (List Pat)) (pattern : Pat) :
    pattern ∈ mkConses info rows ↔ ∃ original ∈ rows, pattern = .cons info original := by
  induction rows with
  | nil => simp [mkConses]
  | cons first rest ih => simp [mkConses, ih, eq_comm]

/-- Expanded one-column matrix rows retain their original pattern. -/
theorem mem_mkRows (patterns : List Pat) (row : List Pat) :
    row ∈ mkRows patterns ↔ ∃ original ∈ patterns, row = [original] := by
  induction patterns with
  | nil => simp [mkRows]
  | cons first rest ih => simp [mkRows, ih, eq_comm]

/-- Expanding a list of patterns does not change its width. -/
theorem expandList_length (patterns row : List Pat) (member : row ∈ expandList patterns) :
    row.length = patterns.length := by
  induction patterns generalizing row with
  | nil => simp [expandList] at member; subst row; rfl
  | cons first rest ih =>
    simp only [expandList, mem_mkProds] at member
    obtain ⟨item, _, tail, tailMember, rfl⟩ := member
    simp [ih tail tailMember]

mutual
/-- Expanding alternatives preserves non-error matching and reflects success. -/
theorem expand_sound (pattern : Pat) (expanded : Pat) (refs : HolFiniteMapExact Nat Term) (value : Term)
    (member : expanded ∈ expand pattern) (safe : pmatch refs pattern value ≠ .typeFailure) :
    pmatch refs expanded value ≠ .typeFailure ∧
      (pmatch refs expanded value = .success → pmatch refs pattern value = .success) := by
  cases pattern with
  | any => simp [expand] at member; subst expanded; simp [safe]
  | lit literal => simp [expand] at member; subst expanded; simp [safe]
  | or first second =>
    simp only [expand, List.mem_append] at member
    have firstSafe : pmatch refs first value ≠ .typeFailure := by
      cases a : pmatch refs first value <;> cases b : pmatch refs second value <;> simp_all [pmatch]
    have secondSafe : pmatch refs second value ≠ .typeFailure := by
      cases a : pmatch refs first value <;> cases b : pmatch refs second value <;> simp_all [pmatch]
    rcases member with firstMember | secondMember
    · obtain ⟨expandedSafe, success⟩ := expand_sound first expanded refs value firstMember firstSafe
      refine ⟨expandedSafe, ?_⟩
      intro hit
      have firstHit := success hit
      cases b : pmatch refs second value <;> simp_all [pmatch]
    · obtain ⟨expandedSafe, success⟩ := expand_sound second expanded refs value secondMember secondSafe
      refine ⟨expandedSafe, ?_⟩
      intro hit
      have secondHit := success hit
      cases a : pmatch refs first value <;> simp_all [pmatch]
  | ref pattern =>
    simp only [expand, mem_mkRefs] at member
    obtain ⟨child, childMember, rfl⟩ := member
    cases value with
    | litv _ | term _ _ | other => simp [pmatch] at safe
    | refPtr address =>
      cases lookup : refs.lookup address with
      | none => simp [pmatch, lookup] at safe
      | some v =>
        have innerSafe : pmatch refs pattern v ≠ .typeFailure := by simpa [pmatch, lookup] using safe
        simpa [pmatch, lookup] using expand_sound pattern child refs v childMember innerSafe
  | cons info patterns =>
    simp only [expand, mem_mkConses] at member
    obtain ⟨args, argsMember, rfl⟩ := member
    have argsLength := expandList_length patterns args argsMember
    cases value with
    | litv _ | refPtr _ | other => simp [pmatch] at safe
    | term tag fields =>
      cases info with
      | none =>
        cases tag with
        | some actual => simp [pmatch] at safe
        | none =>
          have listSafe : pmatchList refs patterns fields ≠ .typeFailure := by simpa [pmatch] using safe
          simpa [pmatch] using expandList_sound patterns args refs fields argsMember listSafe
      | some info =>
        obtain ⟨expected, siblings⟩ := info
        cases tag with
        | none => simp [pmatch] at safe
        | some actual =>
          by_cases tagsMatch : expected = actual ∧ patterns.length = fields.length
          · have listSafe : pmatchList refs patterns fields ≠ .typeFailure := by simpa [pmatch, tagsMatch] using safe
            have listResult := expandList_sound patterns args refs fields argsMember listSafe
            simpa [pmatch, tagsMatch, argsLength] using listResult
          · have mismatch : ¬(expected = actual ∧ args.length = fields.length) := by simpa [argsLength] using tagsMatch
            simp only [pmatch, tagsMatch, mismatch, ↓reduceIte] at safe ⊢
            split <;> simp_all
termination_by sizeOf pattern

/-- Expanding argument vectors preserves non-error matching and reflects success. -/
theorem expandList_sound (patterns expanded : List Pat) (refs : HolFiniteMapExact Nat Term) (values : List Term)
    (member : expanded ∈ expandList patterns) (safe : pmatchList refs patterns values ≠ .typeFailure) :
    pmatchList refs expanded values ≠ .typeFailure ∧
      (pmatchList refs expanded values = .success → pmatchList refs patterns values = .success) := by
  cases patterns with
  | nil => simp [expandList] at member; subst expanded; simp [safe]
  | cons first rest =>
    simp only [expandList, mem_mkProds] at member
    obtain ⟨child, childMember, tail, tailMember, rfl⟩ := member
    cases values with
    | nil => simp [pmatchList] at safe
    | cons value values =>
      have bothSafe : pmatch refs first value ≠ .typeFailure ∧
          pmatchList refs rest values ≠ .typeFailure := by simpa using safe
      obtain ⟨firstSafe, restSafe⟩ := bothSafe
      obtain ⟨childSafe, childHit⟩ := expand_sound first child refs value childMember firstSafe
      obtain ⟨tailSafe, tailHit⟩ := expandList_sound rest tail refs values tailMember restSafe
      simp only [pmatchList_cons]
      constructor
      · intro bad
        rcases (pand_typeFailure_iff _ _).mp bad with badHead | badTail
        · exact childSafe badHead
        · exact tailSafe badTail
      · intro hit
        obtain ⟨headHit, restHit⟩ := (pand_success_iff _ _).mp hit
        exact (pand_success_iff _ _).mpr ⟨childHit headHit, tailHit restHit⟩
termination_by sizeOf patterns
end

/-- Each expanded matrix row originates in one input row and one of its
expanded patterns. -/
theorem orRows_member (rows : List (Pat × Nat)) (row : List Pat) (member : row ∈ orRows rows) :
    ∃ pattern index, (pattern, index) ∈ rows ∧
      ∃ expanded ∈ expand pattern, row = [expanded] := by
  induction rows with
  | nil => simp [orRows] at member
  | cons first rest ih =>
    obtain ⟨pattern, index⟩ := first
    simp only [orRows, List.mem_append] at member
    rcases member with here | later
    · obtain ⟨expanded, expandedMember, equality⟩ := (mem_mkRows _ _).mp here
      exact ⟨pattern, index, by simp, expanded, expandedMember, equality⟩
    · obtain ⟨original, originalIndex, inRest, expanded, expandedMember, equality⟩ := ih later
      exact ⟨original, originalIndex, List.mem_cons_of_mem _ inRest, expanded, expandedMember, equality⟩

/-- Exhaustive rows cannot all fail when the row scan has no type error.
HOL correspondence for the underlying matcher and map carrier remains pending. -/
theorem exhRows_sound (refs : HolFiniteMapExact Nat Term) (value : Term) (rows : List (Pat × Nat))
    (safe : matchRows refs rows value ≠ none) (exhaustive : exhRows rows = true) :
    matchRows refs rows value ≠ some .failure := by
  have matrixSafe : ∀ row ∈ orRows rows, pmatchList refs row [value] ≠ .typeFailure := by
    intro row member
    obtain ⟨pattern, index, originalMember, expanded, expandedMember, rfl⟩ := orRows_member rows row member
    have originalSafe := matchRows_member_safe refs value rows safe (pattern, index) originalMember
    have expandedSafe := (expand_sound pattern expanded refs value expandedMember originalSafe).1
    simpa [pmatchList_cons, pmatchList] using expandedSafe
  obtain ⟨row, member, hit⟩ := exhMatrix_sound (orRows rows) refs [value] exhaustive matrixSafe
  obtain ⟨pattern, index, originalMember, expanded, expandedMember, rfl⟩ := orRows_member rows row member
  have originalSafe := matchRows_member_safe refs value rows safe (pattern, index) originalMember
  have expandedHit : pmatch refs expanded value = .success := by simpa [pmatchList_cons, pmatchList] using hit
  have originalHit := (expand_sound pattern expanded refs value expandedMember originalSafe).2 expandedHit
  exact matchRows_exists_success refs value rows safe ⟨(pattern, index), originalMember, originalHit⟩


end Flapjack.Compiler.Backend.PatternExh
