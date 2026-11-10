import Flapjack.Compiler.Backend.ClosAnnotate.Original
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.CodeLocations

/-! Label preservation for the original closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang ClosProps

/-- Original annotation preserves the labels of a program. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "MAP_FST_compile"]
theorem mapFst_compile {α : Type} (program : List (α × Nat × Exp)) :
    (compileSource program).map Prod.fst = program.map Prod.fst := by
  simp [compileSource, List.map_map]

/-- A zero constant contains no code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "code_locs_const_0"]
theorem codeLocs_const0 (trace : BackendCommon.Tra) :
    codeLocations [const0 trace] = [] := by
  simpa using codeLocations_replicate_const0 1 trace

/-- Original free-variable discovery introduces no code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "alt_free_code_locs"]
theorem altFree_codeLocs (expressions : List Exp) :
    codeLocations (altFreeSource expressions).1 ⊆ codeLocations expressions := by
  rw [altFreeSource_sing_eq.2.1]
  exact altFreeList_codeLocations expressions

/-- Original free-variable discovery preserves distinct code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "alt_free_code_locs_distinct"]
theorem altFree_codeLocs_distinct (expressions : List Exp)
    (distinct : (codeLocations expressions).Nodup) :
    (codeLocations (altFreeSource expressions).1).Nodup := by
  rw [altFreeSource_sing_eq.2.1]
  exact (altFreeList_codeLocations_sublist expressions).nodup distinct

/-- Source shifting preserves the complete ordered list of code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "code_locs_shift"]
theorem codeLocs_shift (expressions : List Exp) (m l : Nat) (i : Spt Nat) :
    codeLocations (shiftSource expressions m l i) = codeLocations expressions := by
  rw [shiftSource_eq_shiftList]
  exact shiftList_codeLocations expressions m l i

/-- Every location in a source free-variable result occurred in its input. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "code_locs_alt_free"]
theorem codeLocs_altFree (expressions result : List Exp) (vars : DbVars.DbVarSet)
    (h : altFreeSource expressions = (result, vars)) :
    codeLocations result ⊆ codeLocations expressions := by
  rw [altFreeSource_sing_eq.2.1] at h
  have resultEq : (altFreeList expressions).1 = result := congrArg Prod.fst h
  rw [← resultEq]
  exact altFreeList_codeLocations expressions

/-- Source annotation introduces no new code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "code_locs_annotate"]
theorem codeLocs_annotate (arity : Nat) (expressions : List Exp) :
    codeLocations (annotateSource arity expressions) ⊆ codeLocations expressions := by
  rw [(annotateSource_sing_eq arity (.var .none 0) expressions).2]
  simpa [annotateList, shiftList_codeLocations] using altFreeList_codeLocations expressions

/-- Source annotation introduces no locations and preserves distinctness. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "annotate_code_locs"]
theorem annotate_codeLocs (arity : Nat) (expressions : List Exp) :
    codeLocations (annotateSource arity expressions) ⊆ codeLocations expressions ∧
      ((codeLocations expressions).Nodup → (codeLocations (annotateSource arity expressions)).Nodup) := by
  constructor
  · exact codeLocs_annotate arity expressions
  · intro distinct
    rw [(annotateSource_sing_eq arity (.var .none 0) expressions).2]
    exact (annotateList_codeLocations_sublist arity expressions).nodup distinct

end Flapjack.Compiler.Backend.ClosAnnotate
