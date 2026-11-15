module

public import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationParity
public import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLabels

@[expose] public section

/-! Exact sets of labels produced by closure numbering. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open ClosLang ClosProps

private def labelRange (start stop : Nat) : Set Nat :=
  {label | ∃ k, label = start + 2 * k ∧ label < stop}

private theorem labelRange_join {start middle stop : Nat}
    (hm : start ≤ middle) (hs : middle ≤ stop)
    (startEven : start % 2 = 0) (middleEven : middle % 2 = 0) :
    labelRange start middle ∪ labelRange middle stop = labelRange start stop := by
  ext label
  simp only [labelRange, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨k, rfl, bound⟩ | ⟨k, rfl, bound⟩)
    · exact ⟨k, rfl, by omega⟩
    · refine ⟨(middle - start) / 2 + k, ?_, bound⟩
      omega
  · rintro ⟨k, rfl, bound⟩
    by_cases h : start + 2 * k < middle
    · exact Or.inl ⟨k, rfl, h⟩
    · refine Or.inr ⟨(start + 2 * k - middle) / 2, ?_, bound⟩
      omega

private theorem labelRange_empty (start : Nat) : labelRange start start = ∅ := by
  ext label
  simp only [labelRange, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨k, eq, bound⟩
  omega

private theorem labelRange_block (start count : Nat) :
    ((fun k => start + 2 * k) '' Set.Iio count) = labelRange start (start + 2 * count) := by
  ext label
  simp only [labelRange, Set.mem_image, Set.mem_Iio, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, bound, rfl⟩
    exact ⟨k, rfl, by omega⟩
  · rintro ⟨k, rfl, bound⟩
    exact ⟨k, by omega, rfl⟩

private theorem labelRange_step {start middle : Nat} (hm : start ≤ middle)
    (startEven : start % 2 = 0) (middleEven : middle % 2 = 0) :
    labelRange start middle ∪ {middle} = labelRange start (middle + 2) := by
  have last : labelRange middle (middle + 2) = {middle} := by
    ext label
    simp only [labelRange, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, eq, bound⟩
      omega
    · intro eq
      subst label
      exact ⟨0, by simp⟩
  rw [← last]
  exact labelRange_join hm (by omega) startEven middleEven

private theorem labels_union_empty {a b : Set Nat} (h : a ∪ b = ∅) : a = ∅ ∧ b = ∅ := by
  exact sup_eq_bot_iff.mp h

private theorem renumberFuns_even (functions : List (Nat × Exp)) (start : Nat)
    (even : start % 2 = 0) : (renumberFuns start functions).1 % 2 = 0 := by
  cases functions with
  | nil => simpa [renumberFuns] using even
  | cons first rest =>
    obtain ⟨arity, body⟩ := first
    have h := (renumberCodeLocs_even.2 start body even).1
    simpa [renumberFuns] using renumberFuns_even rest (renumber start body).1 h
termination_by sizeOf functions

mutual

private theorem renumberLabelsExpr (expression : Exp) (start : Nat)
    (clear : getCodeLabels expression = ∅) (even : start % 2 = 0) :
    getCodeLabels (renumber start expression).2 = labelRange start (renumber start expression).1 := by
  cases expression with
  | var t v => simp [renumber, getCodeLabels, labelRange_empty]
  | raise t body =>
    have bodyClear : getCodeLabels body = ∅ := by simpa [getCodeLabels] using clear
    simpa [renumber, getCodeLabels] using renumberLabelsExpr body start bodyClear even
  | tick t body =>
    have bodyClear : getCodeLabels body = ∅ := by simpa [getCodeLabels] using clear
    simpa [renumber, getCodeLabels] using renumberLabelsExpr body start bodyClear even
  | call t ticks loc args =>
    have member : loc ∈ getCodeLabels (.call t ticks loc args) := by simp [getCodeLabels]
    rw [clear] at member
    exact False.elim member
  | ifThenElse t a b c =>
    have source : (getCodeLabels a ∪ getCodeLabels b) ∪ getCodeLabels c = ∅ := by
      simpa only [getCodeLabels] using clear
    obtain ⟨abClear, cClear⟩ := labels_union_empty source
    obtain ⟨aClear, bClear⟩ := labels_union_empty abClear
    have aLabels := renumberLabelsExpr a start aClear even
    have aEven := (renumberCodeLocs_even.2 start a even).1
    have bLabels := renumberLabelsExpr b (renumber start a).1 bClear aEven
    have bEven := (renumberCodeLocs_even.2 (renumber start a).1 b aEven).1
    have cLabels := renumberLabelsExpr c (renumber (renumber start a).1 b).1 cClear bEven
    have aLe := renumber_start_le a start
    have bLe := renumber_start_le b (renumber start a).1
    have cLe := renumber_start_le c (renumber (renumber start a).1 b).1
    simp only [renumber, getCodeLabels]
    rw [aLabels, bLabels, cLabels, labelRange_join aLe bLe even aEven,
      labelRange_join (by omega) cLe even bEven]
  | «let» t args body =>
    obtain ⟨argsClear, bodyClear⟩ := labels_union_empty (by simpa [getCodeLabels] using clear)
    have argsLabels := renumberLabelsList args start argsClear even
    have middleEven := (renumberCodeLocs_even.1 start args even).1
    have bodyLabels := renumberLabelsExpr body (renumberList start args).1 bodyClear middleEven
    have middleLe := renumberList_start_le args start
    have stopLe := renumber_start_le body (renumberList start args).1
    simp only [renumber, getCodeLabels]
    rw [argsLabels, bodyLabels]
    exact labelRange_join middleLe stopLe even middleEven
  | handle t a b =>
    obtain ⟨aClear, bClear⟩ := labels_union_empty (by simpa [getCodeLabels] using clear)
    have aLabels := renumberLabelsExpr a start aClear even
    have middleEven := (renumberCodeLocs_even.2 start a even).1
    have bLabels := renumberLabelsExpr b (renumber start a).1 bClear middleEven
    have middleLe := renumber_start_le a start
    have stopLe := renumber_start_le b (renumber start a).1
    simp only [renumber, getCodeLabels]
    rw [aLabels, bLabels]
    exact labelRange_join middleLe stopLe even middleEven
  | app t loc fn args =>
    have source : getCodeLabels fn ∪ getCodeLabelsList args = ∅ := by
      cases loc with
      | none => simpa [getCodeLabels] using clear
      | some n =>
        have member : n ∈ getCodeLabels (.app t (some n) fn args) := by simp [getCodeLabels]
        rw [clear] at member
        exact False.elim member
    obtain ⟨fnClear, argsClear⟩ := labels_union_empty source
    have fnLabels := renumberLabelsExpr fn start fnClear even
    have middleEven := (renumberCodeLocs_even.2 start fn even).1
    have argsLabels := renumberLabelsList args (renumber start fn).1 argsClear middleEven
    have middleLe := renumber_start_le fn start
    have stopLe := renumberList_start_le args (renumber start fn).1
    simp only [renumber, getCodeLabels, Set.empty_union]
    rw [fnLabels, argsLabels]
    exact labelRange_join middleLe stopLe even middleEven
  | fn name loc vars arity body =>
    have bodyClear : getCodeLabels body = ∅ := by
      cases loc with
      | none => simpa [getCodeLabels] using clear
      | some n =>
        have member : n ∈ getCodeLabels (.fn name (some n) vars arity body) := by simp [getCodeLabels]
        rw [clear] at member
        exact False.elim member
    have bodyLabels := renumberLabelsExpr body start bodyClear even
    have middleEven := (renumberCodeLocs_even.2 start body even).1
    have middleLe := renumber_start_le body start
    simp only [renumber, getCodeLabels]
    rw [bodyLabels]
    simpa [Set.union_comm] using (labelRange_step middleLe even middleEven)
  | letrec names loc vars functions body =>
    have source : (match loc with
        | none => ∅
        | some n => (fun k => n + 2 * k) '' Set.Iio functions.length) ∪
        getCodeLabels body ∪ getCodeLabelsFuns functions = ∅ := by
      cases loc <;> simpa only [getCodeLabels] using clear
    obtain ⟨prefixClear, funsClear⟩ := labels_union_empty source
    obtain ⟨_, bodyClear⟩ := labels_union_empty prefixClear
    let middle := (renumberFuns start functions).1
    let count := (renumberFuns start functions).2.length
    let bodyStart := middle + 2 * count
    have funLabels := renumberLabelsFuns functions start funsClear even
    have middleEven : middle % 2 = 0 := renumberFuns_even functions start even
    have bodyEven : bodyStart % 2 = 0 := by dsimp [bodyStart]; omega
    have bodyLabels := renumberLabelsExpr body bodyStart bodyClear bodyEven
    have firstLe : start ≤ middle := renumberFuns_start_le functions start
    have stopLe := renumber_start_le body bodyStart
    simp only [renumber, getCodeLabels]
    change ((fun k => middle + 2 * k) '' Set.Iio count) ∪
      getCodeLabels (renumber bodyStart body).2 ∪
      getCodeLabelsFuns (renumberFuns start functions).2 = _
    rw [labelRange_block, bodyLabels, funLabels]
    have joined := labelRange_join firstLe (show middle ≤ bodyStart by dsimp [bodyStart]; omega)
      even middleEven
    have all := labelRange_join (show start ≤ bodyStart by dsimp [bodyStart]; omega)
      stopLe even bodyEven
    rw [← joined] at all
    simpa only [Set.union_assoc, Set.union_comm, Set.union_left_comm] using all
  | op t op args =>
    obtain ⟨argsClear, opClear⟩ := labels_union_empty (by simpa [getCodeLabels] using clear)
    have argsLabels := renumberLabelsList args start argsClear even
    simp only [renumber, getCodeLabels]
    rw [argsLabels, opClear, Set.union_empty]
termination_by sizeOf expression

private theorem renumberLabelsList (expressions : List Exp) (start : Nat)
    (clear : getCodeLabelsList expressions = ∅) (even : start % 2 = 0) :
    getCodeLabelsList (renumberList start expressions).2 = labelRange start (renumberList start expressions).1 := by
  cases expressions with
  | nil => simp [renumberList, getCodeLabelsList, labelRange_empty]
  | cons first rest =>
    obtain ⟨firstClear, restClear⟩ := labels_union_empty (by simpa [getCodeLabelsList] using clear)
    have firstLabels := renumberLabelsExpr first start firstClear even
    have middleEven := (renumberCodeLocs_even.2 start first even).1
    have restLabels := renumberLabelsList rest (renumber start first).1 restClear middleEven
    have middleLe := renumber_start_le first start
    have stopLe := renumberList_start_le rest (renumber start first).1
    simp only [renumberList, getCodeLabelsList]
    rw [firstLabels, restLabels]
    exact labelRange_join middleLe stopLe even middleEven
termination_by sizeOf expressions

private theorem renumberLabelsFuns (functions : List (Nat × Exp)) (start : Nat)
    (clear : getCodeLabelsFuns functions = ∅) (even : start % 2 = 0) :
    getCodeLabelsFuns (renumberFuns start functions).2 = labelRange start (renumberFuns start functions).1 := by
  cases functions with
  | nil => simp [renumberFuns, getCodeLabelsFuns, labelRange_empty]
  | cons first rest =>
    cases first with
    | mk arity body =>
      obtain ⟨bodyClear, restClear⟩ := labels_union_empty (by simpa [getCodeLabelsFuns] using clear)
      have bodyLabels := renumberLabelsExpr body start bodyClear even
      have middleEven := (renumberCodeLocs_even.2 start body even).1
      have restLabels := renumberLabelsFuns rest (renumber start body).1 restClear middleEven
      have middleLe := renumber_start_le body start
      have stopLe := renumberFuns_start_le rest (renumber start body).1
      simp only [renumberFuns, getCodeLabelsFuns]
      rw [bodyLabels, restLabels]
      exact labelRange_join middleLe stopLe even middleEven
termination_by sizeOf functions
decreasing_by all_goals (subst_vars; simp_wf; omega)

end

private theorem labelsList_eq_empty (expressions : List Exp)
    (clear : ∀ e ∈ expressions, getCodeLabels e = ∅) : getCodeLabelsList expressions = ∅ := by
  induction expressions with
  | nil => simp [getCodeLabelsList]
  | cons first rest ih =>
    have firstClear : getCodeLabels first = ∅ := clear first (by simp)
    have restClear : ∀ e ∈ rest, getCodeLabels e = ∅ := by
      intro e member
      exact clear e (by simp [member])
    simp [getCodeLabelsList, firstClear, ih restClear]

/-- Numbering an unlabeled expression assigns exactly the even-spaced labels
between the starting and final locations. The first conjunct covers lists. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "renumber_code_locs_get_code_labels"]
theorem renumber_code_locs_get_code_labels :
    (∀ n es next out, renumberList n es = (next, out) ∧
      (∀ e ∈ es, getCodeLabels e = ∅) ∧ n % 2 = 0 →
      ⋃₀ (getCodeLabels '' {e | e ∈ out}) = {label | ∃ k, label = n + 2 * k ∧ label < next}) ∧
    (∀ n e next out, renumber n e = (next, out) ∧
      getCodeLabels e = ∅ ∧ n % 2 = 0 →
      getCodeLabels out = {label | ∃ k, label = n + 2 * k ∧ label < next}) := by
  constructor
  · intro n es next out ⟨run, clear, even⟩
    have result := renumberLabelsList es n (labelsList_eq_empty es clear) even
    simpa only [run, Prod.fst, Prod.snd, getCodeLabelsList_eq, labelRange] using result
  · intro n e next out ⟨run, clear, even⟩
    have result := renumberLabelsExpr e n clear even
    simpa only [run, Prod.fst, Prod.snd, labelRange] using result

end Flapjack.Compiler.Backend.ClosNumber
