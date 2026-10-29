import Flapjack.Compiler.Backend.FlatPattern.Proofs.DecisionEncoding
import Flapjack.Compiler.Backend.PatternComp.Proofs.Correctness

/-! The decision-tree path of flat pattern compilation. Its evaluator and
finite-map carrier remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.Compiler.Backend

/-- Inserting sequential branches leaves earlier keys unchanged. -/
theorem branchFold_lookup_before (branches : List FlatLang.Exp) (start key : Nat)
    (tree : Spt FlatLang.Exp) (before : key < start) :
    sptLookup key (branches.foldl (fun (state : Nat × Spt FlatLang.Exp) branch =>
      (state.1 + 1, sptInsert state.1 branch state.2)) (start, tree)).2 = sptLookup key tree := by
  induction branches generalizing start tree with
  | nil => rfl
  | cons branch rest ih =>
    simp only [List.foldl_cons]
    rw [ih (start + 1) (sptInsert start branch tree) (by omega)]
    exact sptLookup_sptInsert_ne start key branch tree (by omega)

/-- A sequential branch-table fold maps every inserted index to its expression. -/
theorem branchFold_lookup (branches : List FlatLang.Exp) (start : Nat) (tree : Spt FlatLang.Exp)
    (index : Nat) (branch : FlatLang.Exp) (atIndex : branches[index]? = some branch) :
    sptLookup (start + index) (branches.foldl (fun (state : Nat × Spt FlatLang.Exp) branch =>
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

/-- Each branch stored by the compiler is found at its original index. -/
theorem branchTree_lookup (branches : List FlatLang.Exp) (index : Nat) (branch : FlatLang.Exp)
    (atIndex : branches[index]? = some branch) : sptLookup index (branchTree branches) = some branch := by
  simpa [branchTree] using branchFold_lookup branches 0 .ln index branch atIndex

/-- The decision-tree branch lowering evaluates the same selected source row
as the flat matcher, provided matching does not type-fail. -/
theorem evaluate_compilePats_decision {C F : Type} (cfg : Config) (trace : BackendCommon.Tra) (n : Nat)
    (expression default : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [value]))
    (safe : FlatSem.pmatchRows rows state value ≠ .typeError) :
    FlatSem.evaluate env state [compilePats cfg false trace n expression default rows] =
      FlatSem.evaluate env state [match FlatSem.pmatchRows rows state value with
        | .match (_, pattern, body) => compilePatRhs trace n expression (pattern, body)
        | _ => default] := by
  let encoded := (rows.zipIdx 0).map (fun (row, index) => (encodePat row.1, index))
  let branches := rows.map (compilePatRhs trace n expression)
  have encoding := encodeRows_simulation state value rows 0
  cases source : FlatSem.pmatchRows rows state value with
  | typeError => exact (safe source).elim
  | noMatch =>
    have abstractMatch : PatternSemantics.matchRows (encodeRefs state) encoded (encodeValue value) = some .failure := by
      simpa [source, encoded] using encoding
    have compiled := PatternComp.comp_correct (encodeRefs state) (encodeValue value) encoded (by rw [abstractMatch]; simp)
    have treeEval : PatternSemantics.dtEval (encodeRefs state) (encodeValue value) (PatternComp.comp encoded) =
        some .failure := compiled.trans abstractMatch
    have decoded := decodeDtree_simulation trace (branchTree branches) expression default state env value
      (PatternComp.comp encoded) .failure treeEval pure
    simpa [compilePats, encoded, branches, source] using decoded
  | «match» selected =>
    rcases selected with ⟨bindings, pattern, body⟩
    obtain ⟨index, rowAt, abstractMatch⟩ : ∃ index, rows[index]? = some (pattern, body) ∧
        PatternSemantics.matchRows (encodeRefs state) encoded (encodeValue value) = some (.success index) := by
      simpa [source, encoded] using encoding
    have compiled := PatternComp.comp_correct (encodeRefs state) (encodeValue value) encoded (by rw [abstractMatch]; simp)
    have treeEval : PatternSemantics.dtEval (encodeRefs state) (encodeValue value) (PatternComp.comp encoded) =
        some (.success index) := compiled.trans abstractMatch
    have branchAt : branches[index]? = some (compilePatRhs trace n expression (pattern, body)) := by
      simp [branches, List.getElem?_map, rowAt]
    have lookup := branchTree_lookup branches index (compilePatRhs trace n expression (pattern, body)) branchAt
    have decoded := decodeDtree_simulation trace (branchTree branches) expression default state env value
      (PatternComp.comp encoded) (.success index) treeEval pure
    simpa [compilePats, encoded, branches, source, lookup] using decoded

/-- Both pattern-compilation paths evaluate the branch chosen by FlatLang's
matcher. The source evaluator and map carriers remain pending HOL review. -/
theorem evaluate_compilePats {C F : Type} (cfg : Config) (naive : Bool) (trace : BackendCommon.Tra) (n : Nat)
    (expression default : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [value]))
    (safe : FlatSem.pmatchRows rows state value ≠ .typeError) :
    FlatSem.evaluate env state [compilePats cfg naive trace n expression default rows] =
      FlatSem.evaluate env state [match FlatSem.pmatchRows rows state value with
        | .match (_, pattern, body) => compilePatRhs trace n expression (pattern, body)
        | _ => default] := by
  cases naive with
  | false => exact evaluate_compilePats_decision cfg trace n expression default rows env state value pure safe
  | true => exact evaluate_compilePats_naive cfg trace n expression default rows env state value pure safe

end Flapjack.Compiler.Backend.FlatPattern
