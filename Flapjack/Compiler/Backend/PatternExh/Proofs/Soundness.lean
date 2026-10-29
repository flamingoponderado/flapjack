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

end Flapjack.Compiler.Backend.PatternExh
