module

public import Flapjack.Compiler.Backend.BvlConst.Proofs.SmartOp
public import Flapjack.Compiler.Backend.BvlConst.Extract
public import Flapjack.Compiler.Backend.Semantics.BvlProps.CodeLabels

@[expose] public section

/-! Code-label facts for constant propagation. -/
namespace Flapjack.Compiler.Backend.BvlConst.Proofs
open Flapjack.Compiler.Backend.BvlProps

/-- Deleting a variable alias preserves the expression's code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "delete_var_code_labels"]
theorem deleteVar_codeLabels (x : Bvl.Exp) :
    getCodeLabels (deleteVar x) = getCodeLabels x := by
  cases x <;> try rfl
  simp [deleteVar_var, getCodeLabels, getCodeLabelsList, ClosLang.assignGetCodeLabel]

/-- A recognized integer constant contains no code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "dest_simple_SOME_code_labels"]
theorem simple_some_codeLabels (x : Bvl.Exp) (y : Int)
    (found : simple x = some y) : getCodeLabels x = ∅ := by
  have eq := (simple_eq x y).1 found
  subst x
  simp [getCodeLabels, getCodeLabelsList, ClosLang.assignGetCodeLabel]

/-- Unary constant folding preserves every code label in the original operation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp1_code_labels"]
theorem smartOp1_codeLabels (op : ClosLang.Op) (x : Bvl.Exp) :
    getCodeLabels (smartOp1 op x) = getCodeLabels (.op op [x]) := by
  cases op <;> try rfl
  case blockOp block =>
    cases block <;> try rfl
    case equalConst constant =>
      cases constant <;> try rfl
      case int value =>
        cases found : simple x with
        | none => simp [smartOp1, found]
        | some n =>
          have empty := simple_some_codeLabels x n found
          simp [smartOp1, found, bool, getCodeLabels, getCodeLabelsList,
            ClosLang.assignGetCodeLabel, empty]

/-- An extracted constant or alias introduces no code labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "MEM_extract_list_code_labels"]
theorem extractList_codeLabels (xs : List Bvl.Exp) (x : Bvl.Exp)
    (member : some x ∈ extractList xs) : getCodeLabels x = ∅ := by
  induction xs with
  | nil => simp [extractList] at member
  | cons head tail ih =>
    rw [extractList_cons] at member
    simp only [List.mem_cons] at member
    rcases member with found | rest
    · cases head <;> try simp [extractSource] at found
      case var n =>
        subst x
        rfl
      case op op args =>
        cases op <;> try simp at found
        case intOp operation =>
          cases operation <;> try simp at found
          case const n =>
            subst x
            simp [getCodeLabels, getCodeLabelsList, ClosLang.assignGetCodeLabel]
        case blockOp operation =>
          cases operation <;> try simp at found
          case cons tag =>
            cases args <;> simp at found
            subst x
            simp [getCodeLabels, getCodeLabelsList, ClosLang.assignGetCodeLabel]
    · exact ih rest

end Flapjack.Compiler.Backend.BvlConst.Proofs
