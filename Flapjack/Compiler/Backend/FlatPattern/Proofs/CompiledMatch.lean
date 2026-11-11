module

public import Flapjack.Compiler.Backend.FlatPattern.Proofs.DecisionEncoding
public import Flapjack.Compiler.Backend.PatternComp.Proofs.Correctness
public import Flapjack.Misc.Sptree.ToList

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! The decision-tree path of flat pattern compilation. Its evaluator and
finite-map carrier remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.Compiler.Backend

private def toBroad (refs : HolFiniteMapExact Nat PatternSemantics.Term) : Nat → Option PatternSemantics.Term :=
  refs.lookup

private def ofBroad (lookup : Nat → Option PatternSemantics.Term)
    (support : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact Nat PatternSemantics.Term := ⟨lookup, support⟩

/-- The pattern-reference map roundtrips through its lookup view. -/
theorem holFmapAsFiniteSupportParamWitness_compThm_refs
    (refs : HolFiniteMapExact Nat PatternSemantics.Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs := by
  cases refs
  exact ⟨rfl, rfl, rfl⟩

/-- Non-error pattern matching is preserved by decision-tree compilation. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "comp_thm"
  (fmap_as_finite_support_parameters := [refs])]
theorem compThm (refs : HolFiniteMapExact Nat PatternSemantics.Term)
    (rows : List (PatternSemantics.Pat × Nat)) (value : PatternSemantics.Term) :
    ∀ result, PatternSemantics.matchRows refs rows value = some result →
      PatternSemantics.dtEval refs value (PatternComp.comp rows) = some result := by
  intro result matched
  have safe : PatternSemantics.matchRows refs rows value ≠ none := by rw [matched]; simp
  exact (PatternComp.comp_correct refs value rows safe).trans matched

/-- Inserting sequential branches leaves earlier keys unchanged. -/
theorem branchFold_lookup_before {α : Type} (branches : List α) (start key : Nat)
    (tree : Spt α) (before : key < start) :
    sptLookup key (branches.foldl (fun (state : Nat × Spt α) branch =>
      (state.1 + 1, sptInsert state.1 branch state.2)) (start, tree)).2 = sptLookup key tree := by
  induction branches generalizing start tree with
  | nil => rfl
  | cons branch rest ih =>
    simp only [List.foldl_cons]
    rw [ih (start + 1) (sptInsert start branch tree) (by omega)]
    exact sptLookup_sptInsert_ne start key branch tree (by omega)

/-- A sequential branch-table fold maps every inserted index to its expression. -/
theorem branchFold_lookup {α : Type} (branches : List α) (start : Nat) (tree : Spt α)
    (index : Nat) (branch : α) (atIndex : branches[index]? = some branch) :
    sptLookup (start + index) (branches.foldl (fun (state : Nat × Spt α) branch =>
      (state.1 + 1, sptInsert state.1 branch state.2)) (start, tree)).2 = some branch := by
  induction branches generalizing start tree index with
  | nil => simp at atIndex
  | cons first rest ih =>
    cases index with
    | zero =>
      simp at atIndex
      subst branch
      simp only [List.foldl_cons, Nat.add_zero]
      rw [branchFold_lookup_before rest (start + 1) start (sptInsert start first tree) (by omega)]
      exact sptLookup_sptInsert_same start first tree
    | succ index =>
      simp only [List.getElem?_cons_succ] at atIndex
      simp only [List.foldl_cons]
      have found := ih (start + 1) (sptInsert start first tree) index atIndex
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found

private theorem branchFold_lookup_mem {α : Type} (branches : List α) (start : Nat) (tree : Spt α)
    (index : Nat) (value : α)
    (found : sptLookup index (branches.foldl (fun (state : Nat × Spt α) branch =>
      (state.1 + 1, sptInsert state.1 branch state.2)) (start, tree)).2 = some value) :
    value ∈ branches ∨ ∃ key, sptLookup key tree = some value := by
  induction branches generalizing start tree with
  | nil => exact Or.inr ⟨index, found⟩
  | cons first rest ih =>
    simp only [List.foldl_cons] at found
    rcases ih (start + 1) (sptInsert start first tree) found with mem | ⟨key, lookup⟩
    · exact Or.inl (List.mem_cons_of_mem _ mem)
    · by_cases equal : key = start
      · subst key
        rw [sptLookup_sptInsert_same] at lookup
        cases lookup
        exact Or.inl (by simp)
      · rw [sptLookup_sptInsert_ne start key first tree equal] at lookup
        exact Or.inr ⟨key, lookup⟩

/-- The values in a sparse tree built from a list are exactly the list values. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "set_toList_fromList"]
theorem setToList_fromList {α : Type} (xs : List α) :
    {x | x ∈ sptToList (sptFromList xs)} = {x | x ∈ xs} := by
  ext x
  constructor
  · intro mem
    obtain ⟨index, found⟩ := (sptMemToList x _).1 mem
    have result := branchFold_lookup_mem xs 0 .ln index x found
    rcases result with mem | ⟨key, found⟩
    · exact mem
    · simp [sptLookup] at found
  · intro mem
    obtain ⟨index, atIndex⟩ := List.mem_iff_getElem?.1 mem
    apply (sptMemToList x _).2
    exact ⟨index, by simpa [sptFromList] using branchFold_lookup xs 0 .ln index x atIndex⟩

/-- Both pattern-compilation paths evaluate the branch chosen by FlatLang's matcher. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "evaluate_compile_pats"]
theorem evaluate_compilePats {C F : Type} (rows : List (FlatLang.Pat × FlatLang.Exp))
    (state : FlatSem.State C F) (value : FlatSem.Value) (env : FlatSem.Environment FlatSem.Value)
    (expression : FlatLang.Exp) (cfg : Config) (naive : Bool) (trace : BackendCommon.Tra) (n : Nat)
    (default : FlatLang.Exp)
    (premises : FlatSem.pmatchRows rows state value ≠ .typeError ∧ pureEvalTo state env expression value) :
    FlatSem.evaluate env state [compilePats cfg naive trace n expression default rows] =
      FlatSem.evaluate env state [match FlatSem.pmatchRows rows state value with
        | .match (_, pattern, body) => compilePatRhs trace n expression (pattern, body)
        | _ => default] := by
  obtain ⟨safe, pure⟩ := premises
  cases naive with
  | false =>
    let encoded := (rows.zipIdx 0).map (fun (row, index) => (encodePat row.1, index))
    let branches := rows.map (compilePatRhs trace n expression)
    have encoding := encodeRows_simulation state value rows 0
    cases source : FlatSem.pmatchRows rows state value with
    | typeError => exact (safe source).elim
    | noMatch =>
      have abstractMatch : PatternSemantics.matchRows (encodeRefs state) encoded (encodeValue value) = some .failure := by
        simpa [source, encoded] using encoding
      have treeEval : PatternSemantics.dtEval (encodeRefs state) (encodeValue value) (PatternComp.comp encoded) =
          some .failure := compThm (encodeRefs state) encoded (encodeValue value) .failure abstractMatch
      have decoded := decodeDtree_simulation state value (PatternComp.comp encoded) .failure env expression trace
        (branchTree branches) default ⟨treeEval, pure⟩
      simpa [compilePats, encoded, branches, source] using decoded
    | «match» selected =>
      rcases selected with ⟨bindings, pattern, body⟩
      obtain ⟨index, rowAt, abstractMatch⟩ : ∃ index, rows[index]? = some (pattern, body) ∧
          PatternSemantics.matchRows (encodeRefs state) encoded (encodeValue value) = some (.success index) := by
        simpa [source, encoded] using encoding
      have treeEval : PatternSemantics.dtEval (encodeRefs state) (encodeValue value) (PatternComp.comp encoded) =
          some (.success index) := compThm (encodeRefs state) encoded (encodeValue value) (.success index) abstractMatch
      have branchAt : branches[index]? = some (compilePatRhs trace n expression (pattern, body)) := by
        simp [branches, List.getElem?_map, rowAt]
      have lookup : sptLookup index (branchTree branches) = some (compilePatRhs trace n expression (pattern, body)) := by
        simpa [branchTree, sptFromList] using
          branchFold_lookup branches 0 .ln index (compilePatRhs trace n expression (pattern, body)) branchAt
      have decoded := decodeDtree_simulation state value (PatternComp.comp encoded) (.success index) env expression trace
        (branchTree branches) default ⟨treeEval, pure⟩
      simpa [compilePats, encoded, branches, source, lookup] using decoded
  | true => exact evaluate_compilePats_naive cfg trace n expression default rows env state value pure safe

end Flapjack.Compiler.Backend.FlatPattern
