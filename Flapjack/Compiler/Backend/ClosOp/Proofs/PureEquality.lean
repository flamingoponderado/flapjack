import Flapjack.Compiler.Backend.ClosOp.Proofs.DirectEvaluate
import Flapjack.Compiler.Backend.ClosOp.Proofs.PureEvaluate
import Flapjack.Compiler.Backend.Semantics.ClosProps.EqualitySym
import Flapjack.Compiler.Backend.ClosOp.Proofs.EqPureSimple

/-! Semantic cases for the source pure-equality optimization. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang ClosSem

namespace PureEqualityPort
/-- Canonical closure-state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end PureEqualityPort

/-- Successful operand evaluation and source value equality evaluate the
ordinary equality operation. This is proof infrastructure. -/
private theorem evaluateEqual {C F : Type} (x y : ClosLang.Exp) (vx vy : Value)
    (env : List Value) (s : State C F) (b : Bool)
    (run : evaluate [x, y] env s = (.val [vx, vy], s))
    (eq : doEq vx vy = .val b) :
    evaluate [.op .none (.blockOp .equal) [x, y]] env s = (.val [boolValue b], s) := by
  rw [evaluate_ordinaryOp_eq .none _ _ env s (by simp) (by simp), run]
  have reverseEq : doEq vy vx = .val b := by rw [ClosProps.doEqSym.1, eq]
  simp [doApp, applyBlock, reverseEq]

/-- Direct-recognizer case of pure-equality correctness. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "eq_pure_thm"
  (fmap_as_finite_support := [refs, code])]
theorem eqPureThmDirect {C F : Type} (x y z : ClosLang.Exp) (vx vy : Value)
    (env : List Value) (s : State C F) (b : Bool) (direct : directEq x y = some z)
    (h : evaluate [x, y] env s = (.val [vx, vy], s) ∧ SimpleExp x ∧ SimpleExp y ∧
      doEq vx vy = .val b) :
    evaluate [eqPure x y] env s = (.val [boolValue b], s) := by
  have original := evaluateEqual x y vx vy env s b h.1 h.2.2.2
  have optimized := eqDirectThm x y env s (.val [boolValue b]) s .none z
    ⟨original, by simp, direct⟩
  have result : eqPure x y = z := by
    simp [eqPure, eqPureList, direct, Flapjack.appListAppend, Flapjack.appendAux, conjList]
  simpa [result] using optimized

/-- Fallback case of pure-equality correctness when neither operand is a
constructor and the direct recognizer does not match. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "eq_pure_thm"
  (fmap_as_finite_support := [refs, code])]
theorem eqPureThmFallback {C F : Type} (x y : ClosLang.Exp) (vx vy : Value)
    (env : List Value) (s : State C F) (b : Bool) (direct : directEq x y = none)
    (noX : cons x = none) (noY : cons y = none)
    (h : evaluate [x, y] env s = (.val [vx, vy], s) ∧ SimpleExp x ∧ SimpleExp y ∧
      doEq vx vy = .val b) :
    evaluate [eqPure x y] env s = (.val [boolValue b], s) := by
  have result : eqPure x y = .op .none (.blockOp .equal) [x, y] := by
    unfold eqPure
    rw [eqPureList, direct]
    dsimp only
    split
    all_goals simp_all [Flapjack.appListAppend, Flapjack.appendAux, conjList]
  rw [result]
  exact evaluateEqual x y vx vy env s b h.1 h.2.2.2

/-- A successful pure pair evaluates each component in the original state.
This is proof infrastructure. -/
private theorem purePair {C F : Type} (x y : ClosLang.Exp) (vx vy : Value)
    (env : List Value) (s : State C F)
    (hx : SimpleExp x) (run : evaluate [x, y] env s = (.val [vx, vy], s)) :
    evaluate [x] env s = (.val [vx], s) ∧ evaluate [y] env s = (.val [vy], s) := by
  have headPure : pureList [x] = true := by simp [pureList, simpleExpPure x hx]
  cases headRun : evaluate [x] env s with
  | mk headResult headState =>
    cases headResult with
    | err err =>
      rw [ClosProps.evaluate_cons_error x [y] env s headState err headRun] at run
      cases run
    | val headValues =>
      obtain ⟨v, rfl⟩ := evaluate_singleton_value x env s headState headValues headRun
      obtain ⟨_, _, stateEq⟩ := ClosProps.evaluate_pure [x] env s headState (.val [v])
        headPure headRun (by simp)
      subst headState
      rw [ClosProps.evaluate_cons_value x [y] env s s v headRun] at run
      cases tailRun : evaluate [y] env s with
      | mk tailResult tailState =>
        cases tailResult with
        | err err => simp [tailRun] at run
        | val tailValues =>
          obtain ⟨v', rfl⟩ := evaluate_singleton_value y env s tailState tailValues tailRun
          simp only [tailRun, Prod.mk.injEq, Flapjack.SemanticPrimitivesHOL.Result.val.injEq,
            List.cons.injEq] at run
          rcases run with ⟨⟨rfl, rfl, _⟩, rfl⟩
          exact ⟨rfl, rfl⟩

/-- Successful evaluation of a constructor exposes the values and length
of its argument list. This is proof infrastructure. -/
private theorem pureConstructor {C F : Type} (trace : BackendCommon.Tra) (tag : Nat)
    (args : List ClosLang.Exp) (env : List Value) (s : State C F) (v : Value)
    (run : evaluate [.op trace (.blockOp (.cons tag)) args] env s = (.val [v], s)) :
    ∃ values, evaluate args env s = (.val values, s) ∧
      v = .block tag values.reverse ∧ values.length = args.length := by
  rw [evaluateConstructor] at run
  cases argsRun : evaluate args env s with
  | mk result next =>
    cases result with
    | err err => simp [argsRun] at run
    | val values =>
      simp only [argsRun, Prod.mk.injEq, Flapjack.SemanticPrimitivesHOL.Result.val.injEq,
        List.cons.injEq] at run
      rcases run with ⟨⟨rfl, _⟩, rfl⟩
      exact ⟨values, rfl, rfl, evaluate_length.1 args env _ _ values argsRun⟩

/-- A successful list of simple expressions can be evaluated pointwise in
the original state. This is proof infrastructure. -/
private theorem pureEvalList {C F : Type} (xs : List ClosLang.Exp) (values : List Value)
    (env : List Value) (s : State C F)
    (simple : ∀ x ∈ xs, SimpleExp x)
    (run : evaluate xs env s = (.val values, s)) :
    List.Forall₂ (fun x v => evaluate [x] env s = (.val [v], s) ∧ SimpleExp x) xs values := by
  induction xs generalizing values with
  | nil =>
    simp only [evaluate, Prod.mk.injEq, Flapjack.SemanticPrimitivesHOL.Result.val.injEq] at run
    rcases run with ⟨rfl, _⟩
    exact .nil
  | cons x xs ih =>
    have hx := simple x (by simp)
    have headPure : pureList [x] = true := by simp [pureList, simpleExpPure x hx]
    cases headRun : evaluate [x] env s with
    | mk headResult headState =>
      cases headResult with
      | err err =>
        rw [ClosProps.evaluate_cons_error x xs env s headState err headRun] at run
        cases run
      | val headValues =>
        obtain ⟨v, rfl⟩ := evaluate_singleton_value x env s headState headValues headRun
        obtain ⟨_, _, stateEq⟩ := ClosProps.evaluate_pure [x] env s headState (.val [v])
          headPure headRun (by simp)
        subst headState
        rw [ClosProps.evaluate_cons_value x xs env s s v headRun] at run
        cases tailRun : evaluate xs env s with
        | mk tailResult tailState =>
          cases tailResult with
          | err err => simp [tailRun] at run
          | val vs =>
            simp only [tailRun, Prod.mk.injEq, Flapjack.SemanticPrimitivesHOL.Result.val.injEq] at run
            rcases run with ⟨rfl, rfl⟩
            exact .cons ⟨headRun, hx⟩ (ih vs (fun y hy => simple y (by simp [hy])) tailRun)

/-- Zipping two pointwise relations preserves both relations. -/
private theorem forall₂Zip {α β γ δ : Type} {R : α → γ → Prop} {S : β → δ → Prop}
    {as : List α} {bs : List β} {cs : List γ} {ds : List δ}
    (ac : List.Forall₂ R as cs) (bd : List.Forall₂ S bs ds) :
    List.Forall₂ (fun p q => R p.1 q.1 ∧ S p.2 q.2) (as.zip bs) (cs.zip ds) := by
  induction ac generalizing bs ds with
  | nil => cases bd <;> simp
  | cons h t ih =>
    cases bd with
    | nil => simp
    | cons h' t' => exact .cons ⟨h, h'⟩ (ih t')

/-- Constructor mismatch case of the source pure-equality theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "eq_pure_thm"
  (fmap_as_finite_support := [refs, code])]
theorem eqPureThmConstructorMismatch {C F : Type} (tx ty : BackendCommon.Tra)
    (tagX tagY : Nat) (xs ys : List ClosLang.Exp) (vx vy : Value)
    (env : List Value) (s : State C F) (b : Bool)
    (direct : directEq (.op tx (.blockOp (.cons tagX)) xs)
      (.op ty (.blockOp (.cons tagY)) ys) = none)
    (different : (tagX != tagY || xs.length != ys.length) = true)
    (h : evaluate [.op tx (.blockOp (.cons tagX)) xs, .op ty (.blockOp (.cons tagY)) ys] env s =
        (.val [vx, vy], s) ∧
      SimpleExp (.op tx (.blockOp (.cons tagX)) xs) ∧
      SimpleExp (.op ty (.blockOp (.cons tagY)) ys) ∧ doEq vx vy = .val b) :
    evaluate [eqPure (.op tx (.blockOp (.cons tagX)) xs)
      (.op ty (.blockOp (.cons tagY)) ys)] env s = (.val [boolValue b], s) := by
  obtain ⟨runX, runY⟩ := purePair _ _ vx vy env s h.2.1 h.1
  obtain ⟨valuesX, _, rfl, lenX⟩ := pureConstructor tx tagX xs env s vx runX
  obtain ⟨valuesY, _, rfl, lenY⟩ := pureConstructor ty tagY ys env s vy runY
  have mismatch : ¬(tagX = tagY ∧ valuesX.reverse.length = valuesY.reverse.length) := by
    simp only [Bool.or_eq_true, bne_iff_ne] at different
    simp only [List.length_reverse, lenX, lenY]
    rcases different with hd | hl
    · exact fun h => hd h.1
    · exact fun h => hl h.2
  have bFalse : b = false := by
    have eq := h.2.2.2
    rw [doEq, if_neg mismatch] at eq
    cases eq
    rfl
  subst b
  have result : eqPure (.op tx (.blockOp (.cons tagX)) xs)
      (.op ty (.blockOp (.cons tagY)) ys) = mkBool false := by
    unfold eqPure
    rw [eqPureList, direct]
    simp [cons, destOp, destCons, different, Flapjack.appListAppend, Flapjack.appendAux, conjList]
  rw [result, mkBool, evaluate_ordinaryOp_eq _ _ _ _ _ (by simp) (by simp)]
  simp [evaluate, doApp, applyBlock, boolValue, BackendCommon.falseTag]

/-- Matching-constructor case of pure equality, with the source functional
induction hypothesis for the zipped constructor fields. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "eq_pure_thm"
  (fmap_as_finite_support := [refs, code])]
theorem eqPureThmConstructorMatch {C F : Type} (tx ty : BackendCommon.Tra)
    (tagX tagY : Nat) (xs ys : List ClosLang.Exp) (vx vy : Value)
    (env : List Value) (s : State C F) (b : Bool)
    (direct : directEq (.op tx (.blockOp (.cons tagX)) xs)
      (.op ty (.blockOp (.cons tagY)) ys) = none)
    (same : (tagX != tagY || xs.length != ys.length) = false)
    (ih : ∀ (hs : List (Value × Value)) (flag : Bool),
      List.Forall₂ (fun p q => evaluate [p.1, p.2] env s = (.val [q.1, q.2], s) ∧
        SimpleExp p.1 ∧ SimpleExp p.2) (xs.reverse.zip ys.reverse) hs ∧
      doEqList (hs.map Prod.fst) (hs.map Prod.snd) = .val flag ∧
      (∀ e ∈ Flapjack.appListAppend (eqPureList (xs.reverse.zip ys.reverse)), SimpleExp e) →
      evaluate [conjList (Flapjack.appListAppend (eqPureList (xs.reverse.zip ys.reverse)))]
        env s = (.val [boolValue flag], s))
    (h : evaluate [.op tx (.blockOp (.cons tagX)) xs, .op ty (.blockOp (.cons tagY)) ys] env s =
        (.val [vx, vy], s) ∧
      SimpleExp (.op tx (.blockOp (.cons tagX)) xs) ∧
      SimpleExp (.op ty (.blockOp (.cons tagY)) ys) ∧ doEq vx vy = .val b) :
    evaluate [eqPure (.op tx (.blockOp (.cons tagX)) xs)
      (.op ty (.blockOp (.cons tagY)) ys)] env s = (.val [boolValue b], s) := by
  obtain ⟨runX, runY⟩ := purePair _ _ vx vy env s h.2.1 h.1
  obtain ⟨valuesX, argsX, rfl, lenX⟩ := pureConstructor tx tagX xs env s vx runX
  obtain ⟨valuesY, argsY, rfl, lenY⟩ := pureConstructor ty tagY ys env s vy runY
  have tagEq : tagX = tagY := by
    simp at same
    exact same.1
  have lengthEq : xs.length = ys.length := by
    simp at same
    exact same.2
  have valuesLength : valuesX.reverse.length = valuesY.reverse.length := by
    simpa [lenX, lenY] using lengthEq
  have listEq : doEqList valuesX.reverse valuesY.reverse = .val b := by
    have eq := h.2.2.2
    rw [doEq, if_pos ⟨tagEq, valuesLength⟩] at eq
    exact eq
  have simpleX : ∀ x ∈ xs, SimpleExp x := by cases h.2.1 with | cons _ _ _ children => exact children
  have simpleY : ∀ y ∈ ys, SimpleExp y := by cases h.2.2.1 with | cons _ _ _ children => exact children
  have relX := pureEvalList xs valuesX env s simpleX argsX
  have relY := pureEvalList ys valuesY env s simpleY argsY
  have zipped := forall₂Zip (List.rel_reverse relX) (List.rel_reverse relY)
  have paired : List.Forall₂ (fun p q => evaluate [p.1, p.2] env s = (.val [q.1, q.2], s) ∧
      SimpleExp p.1 ∧ SimpleExp p.2) (xs.reverse.zip ys.reverse)
        (valuesX.reverse.zip valuesY.reverse) := by
    apply List.Forall₂.imp ?_ zipped
    rintro ⟨ex, ey⟩ ⟨v1, v2⟩ ⟨⟨rx, sx⟩, ⟨ry, sy⟩⟩
    refine ⟨?_, sx, sy⟩
    rw [ClosProps.evaluate_cons_value ex [ey] env s s v1 rx, ry]
  have pairSimple : ∀ p ∈ xs.reverse.zip ys.reverse, SimpleExp p.1 ∧ SimpleExp p.2 := by
    intro p hp
    have members := List.of_mem_zip hp
    exact ⟨simpleX _ (List.mem_reverse.mp members.1), simpleY _ (List.mem_reverse.mp members.2)⟩
  have outSimple := eqPureSimple (xs.reverse.zip ys.reverse) pairSimple
  have mappedEq : doEqList ((valuesX.reverse.zip valuesY.reverse).map Prod.fst)
      ((valuesX.reverse.zip valuesY.reverse).map Prod.snd) = .val b := by
    rw [List.map_fst_zip (Nat.le_of_eq valuesLength),
      List.map_snd_zip (Nat.le_of_eq valuesLength.symm)]
    exact listEq
  have recResult := ih (valuesX.reverse.zip valuesY.reverse) b ⟨paired, mappedEq, outSimple⟩
  have result : eqPure (.op tx (.blockOp (.cons tagX)) xs) (.op ty (.blockOp (.cons tagY)) ys) =
      conjList (Flapjack.appListAppend (eqPureList (xs.reverse.zip ys.reverse))) := by
    unfold eqPure
    rw [eqPureList, direct]
    simp [cons, destOp, destCons, same]
  rw [result]
  exact recResult

/-- One-constructor branch when the other value has a different tag or field
count: the source tag-and-length test short-circuits to false. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "eq_pure_thm"
  (fmap_as_finite_support := [refs, code])]
theorem eqPureThmOneConstructorMismatch {C F : Type} (tx : BackendCommon.Tra)
    (tagX tagY : Nat) (xs : List ClosLang.Exp) (y : ClosLang.Exp)
    (vx : Value) (fieldsY : List Value) (env : List Value) (s : State C F) (b : Bool)
    (direct : directEq (.op tx (.blockOp (.cons tagX)) xs) y = none)
    (noY : cons y = none)
    (different : (tagX != tagY || xs.length != fieldsY.length) = true)
    (h : evaluate [.op tx (.blockOp (.cons tagX)) xs, y] env s =
        (.val [vx, .block tagY fieldsY], s) ∧
      SimpleExp (.op tx (.blockOp (.cons tagX)) xs) ∧ SimpleExp y ∧
      doEq vx (.block tagY fieldsY) = .val b) :
    evaluate [eqPure (.op tx (.blockOp (.cons tagX)) xs) y] env s =
      (.val [boolValue b], s) := by
  obtain ⟨runX, runY⟩ := purePair _ _ vx (.block tagY fieldsY) env s h.2.1 h.1
  obtain ⟨valuesX, _, rfl, lenX⟩ := pureConstructor tx tagX xs env s vx runX
  have mismatch : ¬(tagX = tagY ∧ valuesX.reverse.length = fieldsY.length) := by
    simp only [Bool.or_eq_true, bne_iff_ne] at different
    simp only [List.length_reverse, lenX]
    rcases different with hd | hl
    · exact fun h => hd h.1
    · exact fun h => hl h.2
  have bFalse : b = false := by
    have eq := h.2.2.2
    rw [doEq, if_neg mismatch] at eq
    cases eq
    rfl
  subst b
  let fields := (xs.reverse.zip (List.range xs.length)).map fun p =>
    (p.1, ClosLang.Exp.op .none (.blockOp (.elemAt p.2)) [y])
  have flatten (e : ClosLang.Exp) (tree : Flapjack.AppList ClosLang.Exp) :
      Flapjack.appListAppend (.append (.list [e]) tree) = e :: Flapjack.appListAppend tree := by
    rw [(Flapjack.appListAppend_thm (.list [e]) tree []).1]
    rfl
  have result : eqPure (.op tx (.blockOp (.cons tagX)) xs) y =
      conjList (.op .none (.blockOp (.tagLenEq tagX xs.length)) [y] ::
        Flapjack.appListAppend (eqPureList fields)) := by
    unfold eqPure
    rw [eqPureList, direct]
    dsimp only
    split
    all_goals try solve | simp_all [cons, destOp, destCons]
    all_goals simp_all [cons, destOp, destCons, fields]
  have headRun : evaluate [.op .none (.blockOp (.tagLenEq tagX xs.length)) [y]] env s =
      (.val [boolValue false], s) := by
    rw [evaluate_ordinaryOp_eq .none _ _ env s (by simp) (by simp), runY]
    simp only [Bool.or_eq_true, bne_iff_ne] at different
    rcases different with hd | hl
    · have hd' : tagY ≠ tagX := Ne.symm hd
      have beq : (tagY == tagX) = false := beq_eq_false_iff_ne.mpr hd'
      simp [doApp, applyBlock, beq]
    · have hl' : fieldsY.length ≠ xs.length := Ne.symm hl
      have beq : (fieldsY.length == xs.length) = false := beq_eq_false_iff_ne.mpr hl'
      simp [doApp, applyBlock, beq]
  rw [result]
  exact evaluateConjListFalse _ _ env s headRun

/-- Projection expressions evaluate each field of an already evaluated block.
This is proof infrastructure. -/
private theorem fieldProjectionRel {C F : Type} (y : ClosLang.Exp) (tag : Nat)
    (fields : List Value) (n : Nat) (env : List Value) (s : State C F)
    (lengthEq : fields.length = n)
    (run : evaluate [y] env s = (.val [.block tag fields], s)) :
    List.Forall₂ (fun i v =>
      evaluate [.op .none (.blockOp (.elemAt i)) [y]] env s = (.val [v], s))
      (List.range n) fields := by
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp [lengthEq], ?_⟩
  intro i h1 h2
  simp only [List.get_eq_getElem, List.getElem_range]
  rw [evaluate_ordinaryOp_eq .none _ _ env s (by simp) (by simp), run]
  simp [doApp, applyBlock, List.getElem?_eq_getElem h2]

/-- One-constructor branch with matching runtime tag and field count, using
the source induction hypothesis for its generated projection pairs. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "eq_pure_thm"
  (fmap_as_finite_support := [refs, code])]
theorem eqPureThmOneConstructorMatch {C F : Type} (tx : BackendCommon.Tra)
    (tagX tagY : Nat) (xs : List ClosLang.Exp) (y : ClosLang.Exp)
    (vx : Value) (fieldsY : List Value) (env : List Value) (s : State C F) (b : Bool)
    (direct : directEq (.op tx (.blockOp (.cons tagX)) xs) y = none)
    (noY : cons y = none)
    (same : (tagX != tagY || xs.length != fieldsY.length) = false)
    (ih : let fields := (xs.reverse.zip (List.range xs.length)).map fun p =>
        (p.1, ClosLang.Exp.op .none (.blockOp (.elemAt p.2)) [y])
      ∀ (hs : List (Value × Value)) (flag : Bool),
        List.Forall₂ (fun p q => evaluate [p.1, p.2] env s = (.val [q.1, q.2], s) ∧
          SimpleExp p.1 ∧ SimpleExp p.2) fields hs ∧
        doEqList (hs.map Prod.fst) (hs.map Prod.snd) = .val flag ∧
        (∀ e ∈ Flapjack.appListAppend (eqPureList fields), SimpleExp e) →
        evaluate [conjList (Flapjack.appListAppend (eqPureList fields))] env s =
          (.val [boolValue flag], s))
    (h : evaluate [.op tx (.blockOp (.cons tagX)) xs, y] env s =
        (.val [vx, .block tagY fieldsY], s) ∧
      SimpleExp (.op tx (.blockOp (.cons tagX)) xs) ∧ SimpleExp y ∧
      doEq vx (.block tagY fieldsY) = .val b) :
    evaluate [eqPure (.op tx (.blockOp (.cons tagX)) xs) y] env s =
      (.val [boolValue b], s) := by
  obtain ⟨runX, runY⟩ := purePair _ _ vx (.block tagY fieldsY) env s h.2.1 h.1
  obtain ⟨valuesX, argsX, rfl, lenX⟩ := pureConstructor tx tagX xs env s vx runX
  have tagEq : tagX = tagY := by simp at same; exact same.1
  have lengthEq : xs.length = fieldsY.length := by simp at same; exact same.2
  have valuesLength : valuesX.reverse.length = fieldsY.length := by simpa [lenX] using lengthEq
  have listEq : doEqList valuesX.reverse fieldsY = .val b := by
    have eq := h.2.2.2
    rw [doEq, if_pos ⟨tagEq, valuesLength⟩] at eq
    exact eq
  have simpleX : ∀ x ∈ xs, SimpleExp x := by cases h.2.1 with | cons _ _ _ children => exact children
  have relX := pureEvalList xs valuesX env s simpleX argsX
  have projections := fieldProjectionRel y tagY fieldsY xs.length env s lengthEq.symm runY
  have zipped := forall₂Zip (List.rel_reverse relX) projections
  let fields := (xs.reverse.zip (List.range xs.length)).map fun p =>
    (p.1, ClosLang.Exp.op .none (.blockOp (.elemAt p.2)) [y])
  have paired : List.Forall₂ (fun p q => evaluate [p.1, p.2] env s = (.val [q.1, q.2], s) ∧
      SimpleExp p.1 ∧ SimpleExp p.2) fields (valuesX.reverse.zip fieldsY) := by
    apply List.forall₂_map_left_iff.mpr
    apply List.Forall₂.imp ?_ zipped
    rintro ⟨ex, index⟩ ⟨v1, v2⟩ ⟨⟨rx, sx⟩, ry⟩
    refine ⟨?_, sx, SimpleExp.elemAt _ _ _ h.2.2.1⟩
    rw [ClosProps.evaluate_cons_value ex _ env s s v1 rx, ry]
  have pairSimple : ∀ p ∈ fields, SimpleExp p.1 ∧ SimpleExp p.2 := by
    intro p hp
    simp only [fields, List.mem_map] at hp
    obtain ⟨⟨e, index⟩, member, rfl⟩ := hp
    exact ⟨simpleX e (List.mem_reverse.mp (List.of_mem_zip member).1),
      SimpleExp.elemAt _ _ _ h.2.2.1⟩
  have outSimple := eqPureSimple fields pairSimple
  have mappedEq : doEqList ((valuesX.reverse.zip fieldsY).map Prod.fst)
      ((valuesX.reverse.zip fieldsY).map Prod.snd) = .val b := by
    rw [List.map_fst_zip (Nat.le_of_eq valuesLength),
      List.map_snd_zip (Nat.le_of_eq valuesLength.symm)]
    exact listEq
  have recResult := ih (valuesX.reverse.zip fieldsY) b ⟨paired, mappedEq, outSimple⟩
  have flatten (e : ClosLang.Exp) (tree : Flapjack.AppList ClosLang.Exp) :
      Flapjack.appListAppend (.append (.list [e]) tree) = e :: Flapjack.appListAppend tree := by
    rw [(Flapjack.appListAppend_thm (.list [e]) tree []).1]
    rfl
  have result : eqPure (.op tx (.blockOp (.cons tagX)) xs) y =
      conjList (.op .none (.blockOp (.tagLenEq tagX xs.length)) [y] ::
        Flapjack.appListAppend (eqPureList fields)) := by
    unfold eqPure
    rw [eqPureList, direct]
    dsimp only
    split
    all_goals try solve | simp_all [cons, destOp, destCons]
    all_goals simp_all [cons, destOp, destCons, fields]
  have headRun : evaluate [.op .none (.blockOp (.tagLenEq tagX xs.length)) [y]] env s =
      (.val [boolValue true], s) := by
    rw [evaluate_ordinaryOp_eq .none _ _ env s (by simp) (by simp), runY]
    subst tagY
    simp [doApp, applyBlock, lengthEq]
  rw [result]
  exact evaluateConjListTrue _ _ env s _ ⟨headRun, recResult⟩

end Flapjack.Compiler.Backend.ClosOp
