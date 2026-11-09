module

public import Flapjack.Compiler.Backend.PatternComp.Proofs.GuardCompilation
public import Aesop

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Proof-side soundness infrastructure for CakeML's exhaustiveness matrix.
The row and decision-tree evaluators remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.PatternExh
open Flapjack PatternCommon PatternSemantics PatternComp

/-- Combine two pattern results, retaining any type failure. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "pand_def"]
def pand : PmatchResult → PmatchResult → PmatchResult
  | .success, result => result
  | .failure, result => if result = .typeFailure then .typeFailure else .failure
  | .typeFailure, _ => .typeFailure

/-- The source's identity and type-failure equations for `pand`. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "pand_simps"]
theorem pand_simps (x y : PmatchResult) :
    pand .success y = y ∧ pand x .success = x ∧
    pand .typeFailure y = .typeFailure ∧ pand x .typeFailure = .typeFailure := by
  cases x <;> cases y <;> simp [pand]

@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "pand_eq_PTypeFailure", simp]
theorem pand_typeFailure_iff (x y : PmatchResult) :
    pand x y = .typeFailure ↔ x = .typeFailure ∨ y = .typeFailure := by
  cases x <;> cases y <;> simp [pand]

@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "pand_eq_PMatchSuccess", simp]
theorem pand_success_iff (x y : PmatchResult) :
    pand x y = .success ↔ x = .success ∧ y = .success := by
  cases x <;> cases y <;> simp [pand]

@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "pand_assoc", simp]
theorem pand_assoc (x y z : PmatchResult) : pand (pand x y) z = pand x (pand y z) := by
  cases x <;> cases y <;> cases z <;> rfl

private def toBroad (refs : HolFiniteMapExact Nat Term) : Nat → Option Term :=
  refs.lookup

private def ofBroad (lookup : Nat → Option Term)
    (support : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact Nat Term := ⟨lookup, support⟩

/-- Canonical finite-map parameter roundtrips for the matcher lemmas. -/
theorem holFmapAsFiniteSupportParamWitness_pmatch_any_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs := by
  cases refs
  exact ⟨rfl, rfl, rfl⟩

theorem holFmapAsFiniteSupportParamWitness_pmatchList_nil_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_any_refs refs key

theorem holFmapAsFiniteSupportParamWitness_pmatchList_cons_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_any_refs refs key

theorem holFmapAsFiniteSupportParamWitness_pmatchList_length_source_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_any_refs refs key

theorem holFmapAsFiniteSupportParamWitness_pmatchList_append_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_any_refs refs key

theorem holFmapAsFiniteSupportParamWitness_pmatchList_anys_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_any_refs refs key

theorem holFmapAsFiniteSupportParamWitness_destVal_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_any_refs refs key

theorem holFmapAsFiniteSupportParamWitness_destVal_eq_some_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_any_refs refs key

theorem holFmapAsFiniteSupportParamWitness_destVal_length_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_any_refs refs key

theorem holFmapAsFiniteSupportParamWitness_ctorsOf_sound_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_any_refs refs key

theorem holFmapAsFiniteSupportParamWitness_colCtors_sound_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_any_refs refs key

theorem holFmapAsFiniteSupportParamWitness_specRow_match_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_any_refs refs key

theorem holFmapAsFiniteSupportParamWitness_specMat_member_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_any_refs refs key

theorem holFmapAsFiniteSupportParamWitness_defaultRow_match_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_any_refs refs key

theorem holFmapAsFiniteSupportParamWitness_defaultMat_member_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_any_refs refs key

theorem holFmapAsFiniteSupportParamWitness_exhMatrix_sound_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_any_refs refs key

theorem holFmapAsFiniteSupportParamWitness_matchRows_exists_success_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_any_refs refs key

theorem holFmapAsFiniteSupportParamWitness_orRows_safe_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_any_refs refs key

theorem holFmapAsFiniteSupportParamWitness_orRows_hit_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_any_refs refs key

theorem holFmapAsFiniteSupportParamWitness_exhRows_sound_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_any_refs refs key

/-- A wildcard matches every term. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "pmatch_Any"
  (fmap_as_finite_support_parameters := [refs])]
theorem pmatch_any (refs : HolFiniteMapExact Nat Term) (value : Term) :
    pmatch refs .any value = .success := by
  cases value <;> simp [pmatch]

/-- Matching empty lists succeeds exactly in the source's three base cases. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "pmatch_list_nil"
  (fmap_as_finite_support_parameters := [refs])]
theorem pmatchList_nil (refs : HolFiniteMapExact Nat Term) (value : Term)
    (values : List Term) (pattern : Pat) (patterns : List Pat) :
    pmatchList refs [] [] = .success ∧
    pmatchList refs [] (value :: values) = .typeFailure ∧
    pmatchList refs (pattern :: patterns) [] = .typeFailure := by
  simp [pmatchList]

@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "pmatch_list_cons"
  (fmap_as_finite_support_parameters := [refs]), simp]
theorem pmatchList_cons (refs : HolFiniteMapExact Nat Term) (pattern : Pat)
    (patterns : List Pat) (value : Term) (values : List Term) :
    pmatchList refs (pattern :: patterns) (value :: values) =
      pand (pmatch refs pattern value) (pmatchList refs patterns values) := by
  cases head : pmatch refs pattern value <;>
    cases tail : pmatchList refs patterns values <;> simp [pmatchList, pand, head, tail]

/-- A match without a type failure has equally long pattern and value lists. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "pmatch_list_LENGTH"
  (fmap_as_finite_support_parameters := [refs])]
theorem pmatchList_length_source (refs : HolFiniteMapExact Nat Term) (patterns : List Pat)
    (values : List Term) (safe : pmatchList refs patterns values ≠ .typeFailure) :
    patterns.length = values.length :=
  (PatternComp.pmatchList_length refs patterns values safe).symm

/-- Matching appended pattern/value segments composes their three-valued results. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "pmatch_list_append"
  (fmap_as_finite_support_parameters := [refs])]
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

@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "LENGTH_anys", simp]
theorem length_anys (n : Nat) : (anys n).length = n := by
  induction n <;> simp_all [anys]

/-- Wildcard vectors succeed precisely when their widths agree. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "pmatch_list_anys"
  (fmap_as_finite_support_parameters := [refs])]
theorem pmatchList_anys (refs : HolFiniteMapExact Nat Term) (n : Nat) (values : List Term) :
    pmatchList refs (anys n) values = if values.length = n then .success else .typeFailure := by
  induction n generalizing values with
  | zero => cases values <;> simp [anys, pmatchList]
  | succ n ih =>
    cases values with
    | nil => simp [anys, pmatchList]
    | cons value values => simp [anys, pmatch, pand, ih]

/-- A successful row scan cannot return failure when a row matched. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "match_EXISTS"
  (fmap_as_finite_support_parameters := [refs])]
theorem matchRows_exists_success (refs : HolFiniteMapExact Nat Term) (value : Term)
    (rows : List (Pat × Nat))
    (premises : matchRows refs rows value ≠ none ∧
      ∃ row ∈ rows, pmatch refs row.1 value = .success) :
    matchRows refs rows value ≠ some .failure := by
  obtain ⟨safe, hit⟩ := premises
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
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "default_row_thm"
  (fmap_as_finite_support_parameters := [refs])]
theorem defaultRow_match (refs : HolFiniteMapExact Nat Term) (value : Term) (values : List Term)
    (original row : List Pat) (member : row ∈ defaultRow original) :
    pmatchList refs row values = pmatchList refs original (value :: values) := by
  cases original with
  | nil => simp [defaultRow] at member
  | cons pattern rest =>
    cases pattern <;> simp_all [defaultRow, pmatchList_cons, pmatch, pand]

/-- Every default-matrix row corresponds to a row in the original matrix. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "default_mat_MEM"
  (fmap_as_finite_support_parameters := [refs])]
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
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "MEM_spec_mats"]
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
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "dest_val_def"
  (fmap_as_finite_support_parameters := [refs])]
def destVal (refs : HolFiniteMapExact Nat Term) : Term → Option (Ctor × List Term)
  | .term (some tag) fields => some (.tagC tag fields.length, fields)
  | .term none fields => some (.tupC fields.length, fields)
  | .refPtr address =>
    match refs.lookup address with
    | none => none
    | some value => some (.refC, [value])
  | .litv _ | .other => none

/-- The source characterization of successful constructor extraction. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "dest_val_eq_SOME"
  (fmap_as_finite_support_parameters := [refs])]
theorem destVal_eq_some (refs : HolFiniteMapExact Nat Term) (value : Term)
    (constructor : Ctor) (fields : List Term) :
    destVal refs value = some (constructor, fields) ↔
      (∃ tag, value = .term (some tag) fields ∧ constructor = .tagC tag fields.length) ∨
      (value = .term none fields ∧ constructor = .tupC fields.length) ∨
      (∃ address child, value = .refPtr address ∧ refs.lookup address = some child ∧
        fields = [child] ∧ constructor = .refC) := by
  cases value with
  | litv _ | other => simp [destVal]
  | term tag values => cases tag <;> simp [destVal] <;> aesop
  | refPtr address =>
    cases lookup : refs.lookup address with
    | none => simp [destVal, lookup]
    | some child => simp [destVal, lookup]; aesop

/-- The argument vector extracted from a value has the constructor's arity. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "LENGTH_dest_val"
  (fmap_as_finite_support_parameters := [refs])]
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
      simp only [destVal, lookup, Option.some.injEq, Prod.mk.injEq] at found
      rcases found with ⟨rfl, rfl⟩
      rfl

/-- Duplicate removal preserves membership for every element type. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "MEM_ctor_nub"]
theorem mem_ctorNub {α : Type} (constructors : List α) (constructor : α) :
    constructor ∈ ctorNubHOL constructors ↔ constructor ∈ constructors := by
  classical
  induction constructors with
  | nil => simp [ctorNubHOL]
  | cons first rest ih =>
    by_cases member : first ∈ rest <;> simp_all [ctorNubHOL]

/-- The source filter retains exactly the elements in both lists. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "MEM_ctor_keep"]
theorem mem_ctorKeep {α : Type} (left right : List α) (constructor : α) :
    constructor ∈ ctorKeepHOL left right ↔ constructor ∈ left ∧ constructor ∈ right := by
  classical
  induction left with
  | nil => simp [ctorKeepHOL]
  | cons first rest ih =>
    by_cases member : first ∈ right
    · simp only [ctorKeepHOL, if_pos member, List.mem_cons, ih]
      constructor
      · intro h
        rcases h with equal | both
        · exact ⟨Or.inl equal, equal ▸ member⟩
        · exact ⟨Or.inr both.1, both.2⟩
      · intro ⟨h, inRight⟩
        rcases h with equal | inRest
        · exact Or.inl equal
        · exact Or.inr ⟨inRest, inRight⟩
    · simp only [ctorKeepHOL, if_neg member, List.mem_cons, ih]
      constructor
      · intro ⟨inRest, inRight⟩
        exact ⟨Or.inr inRest, inRight⟩
      · intro ⟨h, inRight⟩
        rcases h with equal | inRest
        · exact (member (equal ▸ inRight)).elim
        · exact ⟨inRest, inRight⟩

/-- Specializing a row preserves its match against the extracted arguments. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "spec_row_thm"
  (fmap_as_finite_support_parameters := [refs])]
theorem specRow_match (constructor : Ctor) (original row : List Pat)
    (refs : HolFiniteMapExact Nat Term) (value : Term) (values fields : List Term)
    (premises : destVal refs value = some (constructor, fields) ∧ row ∈ specRow constructor original) :
    pmatchList refs row (fields ++ values) = pmatchList refs original (value :: values) := by
  obtain ⟨found, member⟩ := premises
  have lenEq := destVal_length refs value constructor fields found
  cases original with
  | nil => simp [specRow] at member
  | cons pattern rest =>
    cases pattern with
    | lit _ | or _ _ => simp [specRow] at member
    | any =>
      simp only [specRow, List.mem_singleton] at member
      subst row
      rw [pmatchList_append refs (anys (ctorArity constructor)) rest fields values (by simp [lenEq])]
      simp [pmatchList_anys, pmatch, pand, lenEq]
    | cons info qs =>
      cases info with
      | none =>
        by_cases ctorEq : constructor = .tupC qs.length
        · subst constructor
          simp only [specRow, ↓reduceIte, List.mem_singleton] at member
          subst row
          simp only [destVal] at found
          split at found
          all_goals try split at found
          all_goals simp_all [pmatch, pand, Ctor.tupC.injEq]
          all_goals rw [pmatchList_append refs qs rest fields values (by simp_all [ctorArity])]
          all_goals simp [pand]
        · simp [specRow, ctorEq] at member
      | some ts =>
        obtain ⟨tag, siblings⟩ := ts
        by_cases ctorEq : constructor = .tagC tag qs.length
        · subst constructor
          simp only [specRow, ↓reduceIte, List.mem_singleton] at member
          subst row
          simp only [destVal] at found
          split at found
          all_goals try split at found
          all_goals simp_all [pmatch, pand, Ctor.tagC.injEq]
          all_goals rw [pmatchList_append refs qs rest fields values (by simp_all [ctorArity])]
          all_goals simp [pand, ctorArity]
        · simp [specRow, ctorEq] at member
    | ref q =>
      by_cases ctorEq : constructor = .refC
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
            simp only [destVal, lookup, Option.some.injEq, Prod.mk.injEq, true_and] at found
            subst fields
            simp [pmatch, lookup]
      · simp [specRow, ctorEq] at member

/-- Each row of a specialized matrix comes from an equally matching source row. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "spec_mat_MEM"
  (fmap_as_finite_support_parameters := [refs])]
theorem specMat_member (matrix : List (List Pat)) (constructor : Ctor) (fields : List Term)
    (refs : HolFiniteMapExact Nat Term) (value : Term) (values : List Term) (row : List Pat)
    (premises : destVal refs value = some (constructor, fields) ∧ row ∈ specMat constructor matrix) :
    ∃ original ∈ matrix, pmatchList refs row (fields ++ values) =
      pmatchList refs original (value :: values) := by
  obtain ⟨found, member⟩ := premises
  induction matrix with
  | nil => simp [specMat] at member
  | cons first rest ih =>
    simp only [specMat, List.mem_append] at member
    rcases member with here | later
    · exact ⟨first, by simp, specRow_match constructor first row refs value values fields ⟨found, here⟩⟩
    · obtain ⟨original, inRest, result⟩ := ih later
      exact ⟨original, List.mem_cons_of_mem _ inRest, result⟩

/-- Tagged constructor membership corresponds to sibling-pair membership. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "MEM_tag_ctors"]
theorem mem_tagCtors (siblings : List (Nat × Nat)) (tag arity : Nat) :
    Ctor.tagC tag arity ∈ tagCtors siblings ↔ (tag, arity) ∈ siblings := by
  induction siblings with
  | nil => simp [tagCtors]
  | cons sibling rest ih =>
    obtain ⟨otherTag, otherArity⟩ := sibling
    simp [tagCtors, ih]

/-- An accepted pattern constructor set contains the class of any value
that does not make the pattern type-fail. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "ctors_of_thm"
  (fmap_as_finite_support_parameters := [refs])]
theorem ctorsOf_sound (pattern : Pat) (constructors : List Ctor)
    (refs : HolFiniteMapExact Nat Term) (value : Term)
    (premises : ctorsOf pattern = some constructors ∧ pmatch refs pattern value ≠ .typeFailure) :
    ∃ constructor fields, destVal refs value = some (constructor, fields) ∧ constructor ∈ constructors := by
  obtain ⟨known, safe⟩ := premises
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
          have sameLength := pmatchList_length_source refs patterns fields listSafe
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
            rw [ctorNub_eq_HOL, mem_ctorNub]
            simp only [List.mem_cons, Ctor.tagC.injEq, mem_tagCtors]
            by_cases same : tag = actual ∧ patterns.length = fields.length
            · exact Or.inl ⟨same.1.symm, same.2.symm⟩
            · right
              have sibling : isSibling (actual, fields.length) (some siblings) = true := by
                simpa [pmatch, same] using safe
              simpa [isSibling] using sibling

/-- If a column provides constructor information and its rows are safe,
the current value has a constructor in that information. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "col_ctors_thm"
  (fmap_as_finite_support_parameters := [refs])]
theorem colCtors_sound (matrix : List (List Pat)) (constructors : List Ctor)
    (refs : HolFiniteMapExact Nat Term) (value : Term) (values : List Term)
    (premises : colCtors matrix = some constructors ∧
      ∀ row ∈ matrix, pmatchList refs row (value :: values) ≠ .typeFailure) :
    ∃ constructor fields, destVal refs value = some (constructor, fields) ∧ constructor ∈ constructors := by
  obtain ⟨known, safe⟩ := premises
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
          ctorsOf_sound pattern headCtors refs value ⟨headInfo, headSafe⟩
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
          refine ⟨headCtor, headFields, headFound, ?_⟩
          rw [ctorKeep_eq_HOL]
          exact (mem_ctorKeep headCtors tailCtors headCtor).mpr ⟨headMember, tailMember⟩

/-- A matrix accepted by the exhaustiveness checker contains a matching row
whenever every row is free of type errors. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "exh_matrix_thm"
  (fmap_as_finite_support_parameters := [refs])]
theorem exhMatrix_sound (matrix : List (List Pat)) (refs : HolFiniteMapExact Nat Term) :
    ∀ (values : List Term),
      exhMatrix matrix = true →
      (∀ row ∈ matrix, pmatchList refs row values ≠ .typeFailure) →
      ∃ row ∈ matrix, pmatchList refs row values = .success := by
  revert refs
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
      obtain ⟨constructor, fields, found, member⟩ := colCtors_sound (row :: rows) constructors refs value values ⟨known, safe⟩
      have specializedSafe : ∀ r ∈ specMat constructor (row :: rows),
          pmatchList refs r (fields ++ values) ≠ .typeFailure := by
        intro r inMatrix
        obtain ⟨original, originalMember, result⟩ :=
          specMat_member (row :: rows) constructor fields refs value values r ⟨found, inMatrix⟩
        rw [result]
        exact safe original originalMember
      obtain ⟨r, inMatrix, hit⟩ := ih (specMat constructor (row :: rows))
        (specMat_mem_specMats constructors constructor (row :: rows) member)
        refs (fields ++ values) allAccepted specializedSafe
      obtain ⟨original, originalMember, result⟩ :=
        specMat_member (row :: rows) constructor fields refs value values r ⟨found, inMatrix⟩
      exact ⟨original, originalMember, result ▸ hit⟩
  · intro matrix member
    simp at member
  · intro first rest ihFirst ihRest matrix member refs values accepted safe
    have both : exhMatrix first = true ∧ exhMats rest = true := by simpa [exhMats] using accepted
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ihFirst refs values both.1 safe
    · exact ihRest matrix member refs values both.2 safe

/-- Both source matrix and matrix-list soundness statements, with independent
reference maps for the two conjuncts. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "exh_matrix_thm"
  (fmap_as_finite_support_relation := [matrixRefs, matricesRefs])]
theorem exh_matrix_thm :
    (∀ (matrix : List (List Pat)) (matrixRefs : HolFiniteMapExact Nat Term) (values : List Term),
      exhMatrix matrix = true ∧ (∀ row ∈ matrix, pmatchList matrixRefs row values ≠ .typeFailure) →
      ∃ row ∈ matrix, pmatchList matrixRefs row values = .success) ∧
    (∀ (matrices : List (List (List Pat))) (matrix : List (List Pat))
      (matricesRefs : HolFiniteMapExact Nat Term) (values : List Term),
      exhMats matrices = true ∧ matrix ∈ matrices ∧
        (∀ row ∈ matrix, pmatchList matricesRefs row values ≠ .typeFailure) →
      ∃ row ∈ matrix, pmatchList matricesRefs row values = .success) := by
  constructor
  · intro matrix refs values ⟨accepted, safe⟩
    exact exhMatrix_sound matrix refs values accepted safe
  · intro matrices
    induction matrices with
    | nil =>
      intro matrix refs values ⟨_, member, _⟩
      simp at member
    | cons first rest ih =>
      intro matrix refs values ⟨accepted, member, safe⟩
      have both : exhMatrix first = true ∧ exhMats rest = true := by simpa [exhMats] using accepted
      rcases List.mem_cons.mp member with rfl | member
      · exact exhMatrix_sound _ refs values both.1 safe
      · exact ih matrix refs values ⟨both.2, member, safe⟩

/-- Prefixing rows preserves their membership witnesses. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "MEM_add_head"]
theorem mem_addHead {α : Type} (item : α) (rows : List (List α)) (row : List α) :
    row ∈ addHead item rows ↔ ∃ rest ∈ rows, row = item :: rest := by
  induction rows with
  | nil => simp [addHead]
  | cons first rest ih => simp [addHead, ih, eq_comm]

/-- Membership in a Cartesian product gives one choice from each input. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "MEM_mk_prods"]
theorem mem_mkProds {α : Type} (items : List α) (rows : List (List α)) (row : List α) :
    row ∈ mkProds items rows ↔ ∃ item rest, item ∈ items ∧ rest ∈ rows ∧ row = item :: rest := by
  induction items with
  | nil => simp [mkProds]
  | cons first rest ih => simp [mkProds, mem_addHead, ih, eq_comm]

/-- Expanded reference patterns retain their original alternatives. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "MEM_mk_refs"]
theorem mem_mkRefs (patterns : List Pat) (pattern : Pat) :
    pattern ∈ mkRefs patterns ↔ ∃ original ∈ patterns, pattern = .ref original := by
  induction patterns with
  | nil => simp [mkRefs]
  | cons first rest ih => simp [mkRefs, ih, eq_comm]

/-- Expanded constructor patterns retain their argument rows. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "MEM_mk_conses"]
theorem mem_mkConses (info : Option (Nat × Option (List (Nat × Nat))))
    (rows : List (List Pat)) (pattern : Pat) :
    pattern ∈ mkConses info rows ↔ ∃ original ∈ rows, pattern = .cons info original := by
  induction rows with
  | nil => simp [mkConses]
  | cons first rest ih => simp [mkConses, ih, eq_comm]

/-- Singleton rows retain exactly the original list elements. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "MEM_mk_rows"]
theorem mem_mkRows {α : Type} (items : List α) (row : List α) :
    row ∈ mkRows items ↔ ∃ original ∈ items, row = [original] := by
  induction items with
  | nil => simp [mkRows]
  | cons first rest ih => simp [mkRows, ih, eq_comm]

/-- Expanding a list of patterns does not change its width. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "LENGTH_expand_list"]
theorem expandList_length (patterns row : List Pat) (member : row ∈ expandList patterns) :
    row.length = patterns.length := by
  induction patterns generalizing row with
  | nil => simp [expandList] at member; subst row; rfl
  | cons first rest ih =>
    simp only [expandList, mem_mkProds] at member
    obtain ⟨item, tail, _, tailMember, rfl⟩ := member
    simp [ih tail tailMember]

mutual
/-- Internal pattern induction step used to prove the full expansion theorem. -/
private theorem expand_sound (pattern : Pat) (expanded : Pat) (refs : HolFiniteMapExact Nat Term) (value : Term)
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

/-- Internal list induction step used to prove the full expansion theorem. -/
private theorem expandList_sound (patterns expanded : List Pat) (refs : HolFiniteMapExact Nat Term) (values : List Term)
    (member : expanded ∈ expandList patterns) (safe : pmatchList refs patterns values ≠ .typeFailure) :
    pmatchList refs expanded values ≠ .typeFailure ∧
      (pmatchList refs expanded values = .success → pmatchList refs patterns values = .success) := by
  cases patterns with
  | nil => simp [expandList] at member; subst expanded; simp [safe]
  | cons first rest =>
    simp only [expandList, mem_mkProds] at member
    obtain ⟨child, tail, childMember, tailMember, rfl⟩ := member
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

/-- Pattern and pattern-list expansion preserve non-error matching and reflect
success, with independently quantified reference maps in the two conjuncts. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "expand_thm"
  (fmap_as_finite_support_relation := [patternRefs, listRefs])]
theorem expand_thm :
    (∀ (pattern expanded : Pat) (patternRefs : HolFiniteMapExact Nat Term) (value : Term),
      expanded ∈ expand pattern ∧ pmatch patternRefs pattern value ≠ .typeFailure →
        pmatch patternRefs expanded value ≠ .typeFailure ∧
          (pmatch patternRefs expanded value = .success → pmatch patternRefs pattern value = .success)) ∧
    (∀ (patterns expanded : List Pat) (listRefs : HolFiniteMapExact Nat Term) (values : List Term),
      expanded ∈ expandList patterns ∧ pmatchList listRefs patterns values ≠ .typeFailure →
        pmatchList listRefs expanded values ≠ .typeFailure ∧
          (pmatchList listRefs expanded values = .success → pmatchList listRefs patterns values = .success)) := by
  constructor
  · intro pattern expanded refs value assumptions
    exact expand_sound pattern expanded refs value assumptions.1 assumptions.2
  · intro patterns expanded refs values assumptions
    exact expandList_sound patterns expanded refs values assumptions.1 assumptions.2

/-- Each expanded matrix row originates in one input row and one of its
expanded patterns. This Flapjack helper replaces the HOL proofs' row induction. -/
theorem orRows_member {α : Type} (rows : List (Pat × α)) (row : List Pat) (member : row ∈ orRows rows) :
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

/-- Expanded rows preserve non-type-failure for every original row. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "or_rows_ok"
  (fmap_as_finite_support_parameters := [refs])]
theorem orRows_safe {α : Type} (refs : HolFiniteMapExact Nat Term) (value : Term)
    (rows : List (Pat × α)) (safe : ∀ row ∈ rows, pmatch refs row.1 value ≠ .typeFailure) :
    ∀ row ∈ orRows rows, pmatchList refs row [value] ≠ .typeFailure := by
  intro row member
  obtain ⟨pattern, payload, originalMember, expanded, expandedMember, rfl⟩ := orRows_member rows row member
  have originalSafe := safe (pattern, payload) originalMember
  have expandedSafe := (expand_sound pattern expanded refs value expandedMember originalSafe).1
  simpa [pmatchList_cons, pmatchList] using expandedSafe

/-- A successful expanded row reflects success back to an original pattern. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "or_rows_hit"
  (fmap_as_finite_support_parameters := [refs])]
theorem orRows_hit {α : Type} (refs : HolFiniteMapExact Nat Term) (value : Term)
    (rows : List (Pat × α))
    (premises : (∀ row ∈ rows, pmatch refs row.1 value ≠ .typeFailure) ∧
      ∃ row ∈ orRows rows, pmatchList refs row [value] = .success) :
    ∃ row ∈ rows, pmatch refs row.1 value = .success := by
  obtain ⟨safe, hit⟩ := premises
  obtain ⟨row, member, matched⟩ := hit
  obtain ⟨pattern, payload, originalMember, expanded, expandedMember, rfl⟩ := orRows_member rows row member
  have originalSafe := safe (pattern, payload) originalMember
  have expandedHit : pmatch refs expanded value = .success := by simpa [pmatchList_cons, pmatchList] using matched
  have originalHit := (expand_sound pattern expanded refs value expandedMember originalSafe).2 expandedHit
  exact ⟨(pattern, payload), originalMember, originalHit⟩

/-- Exhaustive rows cannot all fail when the row scan has no type error. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml" "exh_rows_thm"
  (fmap_as_finite_support_parameters := [refs])]
theorem exhRows_sound (refs : HolFiniteMapExact Nat Term) (rows : List (Pat × Nat)) (value : Term)
    (premises : matchRows refs rows value ≠ none ∧ exhRows rows = true) :
    matchRows refs rows value ≠ some .failure := by
  obtain ⟨safe, exhaustive⟩ := premises
  have rowSafe := matchRows_member_safe refs value rows safe
  have matrixSafe := orRows_safe refs value rows rowSafe
  have matrixHit := exhMatrix_sound (orRows rows) refs [value] exhaustive matrixSafe
  exact matchRows_exists_success refs value rows ⟨safe, orRows_hit refs value rows ⟨rowSafe, matrixHit⟩⟩


end Flapjack.Compiler.Backend.PatternExh
