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

/-- The addition case needed for the binary optimizer label proof. -/
private theorem smartOp2_add_codeLabels (x y : Bvl.Exp) :
    getCodeLabels (smartOp2 (.intOp .add, x, y)) =
      getCodeLabels x ∪ getCodeLabels y := by
  change getCodeLabels
    (match simple y with
    | some n => match opConst x with
      | some (.intOp .add, a, m) =>
          if n + m == 0 then a
          else .op (.intOp .add) [a, .op (.intOp (.const (n + m))) []]
      | some (.intOp .sub, a, m) =>
          .op (.intOp .sub) [a, .op (.intOp (.const (n + m))) []]
      | some _ => .op (.intOp .add) [x, y]
      | none => match simple x with
        | some m => .op (.intOp (.const (n + m))) []
        | none =>
            if n == 0 then x
            else .op (.intOp .add) [x, .op (.intOp (.const n)) []]
    | none => match opConst x, opConst y with
      | some (.intOp .add, a, m), some (.intOp .add, b, n) =>
          if n + m == 0 then .op (.intOp .add) [a, b]
          else .op (.intOp .add)
            [.op (.intOp .add) [a, b], .op (.intOp (.const (n + m))) []]
      | some (.intOp .add, a, m), some (.intOp .sub, b, n) =>
          .op (.intOp .sub)
            [.op (.intOp .sub) [a, b], .op (.intOp (.const (n + m))) []]
      | some (.intOp .sub, a, m), some (.intOp .add, b, n) =>
          if n + m == 0 then .op (.intOp .sub) [a, b]
          else .op (.intOp .add)
            [.op (.intOp .sub) [a, b], .op (.intOp (.const (n + m))) []]
      | _, _ => .op (.intOp .add) [x, y]) = _
  repeat' split
  all_goals simp_all [simple_eq, opConst_eq, getCodeLabels, getCodeLabelsList,
    ClosLang.assignGetCodeLabel, Set.union_comm]

/-- The subtraction case needed for the binary optimizer label proof. -/
private theorem smartOp2_sub_codeLabels (x y : Bvl.Exp) :
    getCodeLabels (smartOp2 (.intOp .sub, x, y)) =
      getCodeLabels x ∪ getCodeLabels y := by
  change getCodeLabels
    (match simple y with
    | some n => match opConst x with
      | some (.intOp .add, a, m) => .op (.intOp .sub) [a, .op (.intOp (.const (n - m))) []]
      | some (.intOp .sub, a, m) =>
          if n - m == 0 then a else .op (.intOp .add) [a, .op (.intOp (.const (n - m))) []]
      | some _ => .op (.intOp .sub) [x, y]
      | none => match simple x with
        | some m => .op (.intOp (.const (n - m))) []
        | none => .op (.intOp .sub) [x, y]
    | none => match opConst x, opConst y with
      | some (.intOp .add, a, m), some (.intOp .add, b, n) =>
          .op (.intOp .add) [.op (.intOp .sub) [a, b], .op (.intOp (.const (n - m))) []]
      | some (.intOp .add, a, m), some (.intOp .sub, b, n) =>
          .op (.intOp .sub) [.op (.intOp .add) [a, b], .op (.intOp (.const (n - m))) []]
      | some (.intOp .sub, a, m), some (.intOp .add, b, n) =>
          if n - m == 0 then .op (.intOp .add) [a, b]
          else .op (.intOp .add)
            [.op (.intOp .add) [a, b], .op (.intOp (.const (n - m))) []]
      | _, _ => .op (.intOp .sub) [x, y]) = _
  repeat' split
  all_goals simp_all [simple_eq, opConst_eq, getCodeLabels, getCodeLabelsList,
    ClosLang.assignGetCodeLabel, Set.union_comm]

/-- The multiplication case needed for the binary optimizer label proof. -/
private theorem smartOp2_mul_codeLabels (x y : Bvl.Exp) :
    getCodeLabels (smartOp2 (.intOp .mult, x, y)) =
      getCodeLabels x ∪ getCodeLabels y := by
  change getCodeLabels
    (match simple y with
    | some n => match opConst x with
      | some (.intOp .mult, a, m) => .op (.intOp .mult) [a, .op (.intOp (.const (n * m))) []]
      | some _ => .op (.intOp .mult) [x, y]
      | none => match simple x with
        | some m => .op (.intOp (.const (n * m))) []
        | none => if n == 1 then x else if n == -1 then
            smartOp2 (.intOp .sub, x, .op (.intOp (.const 0)) [])
          else .op (.intOp .mult) [x, y]
    | none => match opConst x, opConst y with
      | some (.intOp .mult, a, m), some (.intOp .mult, b, n) =>
          .op (.intOp .mult) [.op (.intOp (.const (n * m))) [], .op (.intOp .mult) [a, b]]
      | _, _ => .op (.intOp .mult) [x, y]) = _
  repeat' split
  all_goals simp_all [simple_eq, opConst_eq, smartOp2_sub_codeLabels,
    getCodeLabels, getCodeLabelsList, ClosLang.assignGetCodeLabel, Set.union_comm]

/-- Binary constant folding preserves the labels of the operation and operands. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_code_labels"]
theorem smartOp2_codeLabels (op : ClosLang.Op) (x y : Bvl.Exp) :
    getCodeLabels (smartOp2 (op, x, y)) =
      ClosLang.assignGetCodeLabel op ∪ getCodeLabels x ∪ getCodeLabels y := by
  cases op <;> try (simp [smartOp2, getCodeLabels, getCodeLabelsList,
    ClosLang.assignGetCodeLabel])
  case intOp op =>
    cases op
    case add => simpa [smartOp2] using smartOp2_add_codeLabels x y
    case sub => simpa [smartOp2] using smartOp2_sub_codeLabels x y
    case mult => simpa [smartOp2] using smartOp2_mul_codeLabels x y
    all_goals
      repeat' split
      all_goals simp_all [simple_eq, getCodeLabels, getCodeLabelsList, bool,
        ClosLang.assignGetCodeLabel, Set.union_comm]
      all_goals try (change getCodeLabels (.op (.intOp (.const _)) []) = ∅)
      all_goals simp [getCodeLabels, getCodeLabelsList, ClosLang.assignGetCodeLabel]
  all_goals
    try simp only [smartOp2, getCodeLabels, getCodeLabelsList, ClosLang.assignGetCodeLabel,
      Set.empty_union]
    repeat' split
    all_goals try simp_all [simple_eq, getCodeLabels, getCodeLabelsList, bool,
      ClosLang.assignGetCodeLabel, Set.union_comm]
    all_goals (ext label; simp [or_assoc])

/-- The orientation step preserves the operation's labels and both operand
label sets. It is the orientation case of the source SmartOp label proof. -/
private theorem smartOpFlip_codeLabels (op : ClosLang.Op) (x y : Bvl.Exp) :
    (let (op', x', y') := smartOpFlip op x y
     ClosLang.assignGetCodeLabel op' ∪ getCodeLabels x' ∪ getCodeLabels y') =
      ClosLang.assignGetCodeLabel op ∪ getCodeLabels x ∪ getCodeLabels y := by
  cases found : simple x with
  | none => simp [smartOpFlip, found]
  | some n =>
    have empty := simple_some_codeLabels x n found
    cases op <;> try simp [smartOpFlip, found]
    case intOp intOp =>
      cases intOp <;> try simp
      case add => simp [ClosLang.assignGetCodeLabel, empty]
      case mult => simp [ClosLang.assignGetCodeLabel, empty]
      case sub =>
        change ClosLang.assignGetCodeLabel (.intOp .add) ∪ getCodeLabels y ∪
          getCodeLabels (.op (.intOp (.const (-n))) []) = _
        simp [getCodeLabels, getCodeLabelsList, ClosLang.assignGetCodeLabel, empty]

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

/-- Constant-folding an operation preserves its complete code-label set. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp_code_labels"]
theorem smartOp_codeLabels (op : ClosLang.Op) (xs : List Bvl.Exp) :
    getCodeLabels (smartOp op xs) =
      ClosLang.assignGetCodeLabel op ∪ ⋃₀ (getCodeLabels '' {e | e ∈ xs}) := by
  rw [← getCodeLabelsList_eq]
  cases xs with
  | nil => simp [smartOp, getCodeLabels, getCodeLabelsList]
  | cons x rest =>
    cases rest with
    | nil =>
      simpa [smartOp, getCodeLabels, getCodeLabelsList] using smartOp1_codeLabels op x
    | cons y rest =>
      cases rest with
      | nil =>
        change getCodeLabels (smartOp2 (smartOpFlip op x y)) = _
        have oriented := smartOpFlip_codeLabels op x y
        cases h : smartOpFlip op x y with
        | mk op' pair =>
          cases pair with
          | mk left right =>
            simp only [h] at oriented ⊢
            rw [smartOp2_codeLabels]
            simpa [getCodeLabelsList, Set.union_assoc] using oriented
      | cons z tail => simp [smartOp, getCodeLabels, getCodeLabelsList]

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
