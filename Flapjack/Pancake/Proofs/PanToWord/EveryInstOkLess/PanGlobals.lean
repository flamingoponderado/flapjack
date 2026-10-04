import Flapjack.Pancake.Proofs.PanToWord
import Flapjack.Pancake.Proofs.PanGlobals.CompileDecsStructural

/-!
# `pan_to_wordProofScript.sml` 1299-1409: `every_inst_ok_less` for `pan_globals`

The pan_globals compiler keeps every `Panop` at two arguments. HOL
`every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2)` is
`everyExpHOL panopArityTwoHOL`, `EVERY (every_exp P)` is `everyExpListHOL P`,
`exps_of` is `expsOfHOL`, and `EVERY good_panops` is `List.all goodPanopsHOL`,
as in the reviewed `good_panops_def`/`pancake_good_code_def` ports. The
compiler definitions are the reviewed exact pan_globals ports over
`PanGlobalsContextExact`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

namespace PanToWordEveryInstOkLessPanGlobals

/-- Same-module canonical witness for the `fmap_as_finite_support` qualifier
    on `PanGlobalsContextExact.globals`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width]
    (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

/-- `EVERY (every_exp P)` over an append (Flapjack infrastructure). -/
theorem everyExpListHOL_append {width : Nat} [NeZero width] (P : ExpHOL width → Bool)
    (xs ys : List (ExpHOL width)) :
    everyExpListHOL P (xs ++ ys) = (everyExpListHOL P xs && everyExpListHOL P ys) := by
  induction xs with
  | nil => simp [everyExpListHOL]
  | cons x xs ih => simp [everyExpListHOL, ih, Bool.and_assoc]

mutual
  /-- `compile_exp` on a single expression, with the list form below
      (Flapjack infrastructure for the tagged theorem). -/
  theorem compileExp_every {width : Nat} [NeZero width] (ctxt : PanGlobalsContextExact width) :
      ∀ e : ExpHOL width, everyExpHOL panopArityTwoHOL e = true →
        everyExpHOL panopArityTwoHOL (compileExpExactHOL ctxt e) = true
    | .const _, _ => by simp [compileExpExactHOL, everyExpHOL, panopArityTwoHOL]
    | .var .local _, _ => by simp [compileExpExactHOL, everyExpHOL, panopArityTwoHOL]
    | .var .global name, _ => by
        simp only [compileExpExactHOL]
        split <;> simp [everyExpHOL, everyExpListHOL, panopArityTwoHOL]
    | .rstruct es, h => by
        simp only [everyExpHOL, Bool.and_eq_true] at h
        simp only [compileExpExactHOL, everyExpHOL, Bool.and_eq_true]
        exact ⟨by simp [panopArityTwoHOL], (compileExpList_every ctxt es h.2).1⟩
    | .rfield i e, h => by
        simp only [everyExpHOL, Bool.and_eq_true] at h
        simp only [compileExpExactHOL, everyExpHOL, Bool.and_eq_true]
        exact ⟨by simp [panopArityTwoHOL], compileExp_every ctxt e h.2⟩
    | .nstruct _ _, _ => by simp [compileExpExactHOL, everyExpHOL, panopArityTwoHOL]
    | .nfield _ _, _ => by simp [compileExpExactHOL, everyExpHOL, panopArityTwoHOL]
    | .load sh e, h => by
        simp only [everyExpHOL, Bool.and_eq_true] at h
        simp only [compileExpExactHOL, everyExpHOL, Bool.and_eq_true]
        exact ⟨by simp [panopArityTwoHOL], compileExp_every ctxt e h.2⟩
    | .load32 e, h => by
        simp only [everyExpHOL, Bool.and_eq_true] at h
        simp only [compileExpExactHOL, everyExpHOL, Bool.and_eq_true]
        exact ⟨by simp [panopArityTwoHOL], compileExp_every ctxt e h.2⟩
    | .loadByte e, h => by
        simp only [everyExpHOL, Bool.and_eq_true] at h
        simp only [compileExpExactHOL, everyExpHOL, Bool.and_eq_true]
        exact ⟨by simp [panopArityTwoHOL], compileExp_every ctxt e h.2⟩
    | .op bop es, h => by
        simp only [everyExpHOL, Bool.and_eq_true] at h
        simp only [compileExpExactHOL, everyExpHOL, Bool.and_eq_true]
        exact ⟨by simp [panopArityTwoHOL], (compileExpList_every ctxt es h.2).1⟩
    | .panop op es, h => by
        simp only [everyExpHOL, Bool.and_eq_true] at h
        simp only [compileExpExactHOL, everyExpHOL, Bool.and_eq_true]
        have hl := compileExpList_every ctxt es h.2
        refine ⟨?_, hl.1⟩
        have h1 := h.1
        simp only [panopArityTwoHOL, decide_eq_true_eq] at h1 ⊢
        rw [hl.2, h1]
    | .cmp c e1 e2, h => by
        simp only [everyExpHOL, Bool.and_eq_true] at h
        simp only [compileExpExactHOL, everyExpHOL, Bool.and_eq_true]
        exact ⟨⟨by simp [panopArityTwoHOL], compileExp_every ctxt e1 h.1.2⟩,
          compileExp_every ctxt e2 h.2⟩
    | .shift sh e1 e2, h => by
        simp only [everyExpHOL, Bool.and_eq_true] at h
        simp only [compileExpExactHOL, everyExpHOL, Bool.and_eq_true]
        exact ⟨⟨by simp [panopArityTwoHOL], compileExp_every ctxt e1 h.1.2⟩,
          compileExp_every ctxt e2 h.2⟩
    | .baseAddr, _ => by simp [compileExpExactHOL, everyExpHOL, panopArityTwoHOL]
    | .topAddr, _ => by
        simp [compileExpExactHOL, everyExpHOL, everyExpListHOL, panopArityTwoHOL]
    | .bytesInWord, _ => by simp [compileExpExactHOL, everyExpHOL, panopArityTwoHOL]
  termination_by e => sizeOf e

  /-- `MAP (compile_exp ctxt)` preserves the property and the length. -/
  theorem compileExpList_every {width : Nat} [NeZero width] (ctxt : PanGlobalsContextExact width) :
      ∀ es : List (ExpHOL width), everyExpListHOL panopArityTwoHOL es = true →
        everyExpListHOL panopArityTwoHOL (compileExpExactHOLList ctxt es) = true ∧
          (compileExpExactHOLList ctxt es).length = es.length
    | [], _ => by simp [compileExpExactHOLList, everyExpListHOL]
    | e :: es, h => by
        simp only [everyExpListHOL, Bool.and_eq_true] at h
        have ih := compileExpList_every ctxt es h.2
        simp only [compileExpExactHOLList, everyExpListHOL, Bool.and_eq_true, List.length_cons]
        exact ⟨⟨compileExp_every ctxt e h.1, ih.1⟩, by rw [ih.2]⟩
  termination_by es => sizeOf es
end

/-- Full original `every_inst_ok_less_pan_globals_compile_exp`:
`∀ctxt e. every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2) e ⇒
every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2) (pan_globals$compile_exp ctxt e)`. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_globals_compile_exp"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem every_inst_ok_less_pan_globals_compile_exp {width : Nat} [NeZero width] :
    ∀ (ctxt : PanGlobalsContextExact width) (e : ExpHOL width),
      everyExpHOL panopArityTwoHOL e = true →
        everyExpHOL panopArityTwoHOL (compileExpExactHOL ctxt e) = true :=
  fun ctxt e h => compileExp_every ctxt e h

mutual
  theorem shapeVal_every {width : Nat} [NeZero width] :
      ∀ sh : ShapeHOL, everyExpHOL panopArityTwoHOL (shapeValHOL (width := width) sh) = true
    | .one => by simp [shapeValHOL, everyExpHOL, panopArityTwoHOL]
    | .comb shs => by
        simp only [shapeValHOL, everyExpHOL, Bool.and_eq_true]
        exact ⟨by simp [panopArityTwoHOL], shapeVals_every shs⟩
    | .named _ => by simp [shapeValHOL, everyExpHOL, panopArityTwoHOL]
  termination_by sh => sizeOf sh

  theorem shapeVals_every {width : Nat} [NeZero width] :
      ∀ shs : List ShapeHOL,
        everyExpListHOL panopArityTwoHOL (shapeValsHOL (width := width) shs) = true
    | [] => by simp [everyExpListHOL]
    | sh :: shs => by
        simp only [shapeValsHOL, everyExpListHOL, Bool.and_eq_true]
        exact ⟨shapeVal_every sh, shapeVals_every shs⟩
  termination_by shs => sizeOf shs
end

/-- Full original `every_inst_ok_less_shape_val`:
`(∀e. every_exp P ((shape_val e):'a panLang$exp)) ∧
(∀es. EVERY (every_exp P) ((shape_vals es):'a panLang$exp list))`
with `P` the two-argument `Panop` predicate. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_shape_val"
  (words_as_type_indexed_bitvec)]
theorem every_inst_ok_less_shape_val {width : Nat} [NeZero width] :
    (∀ e : ShapeHOL, everyExpHOL panopArityTwoHOL (shapeValHOL (width := width) e) = true) ∧
      (∀ es : List ShapeHOL,
        everyExpListHOL panopArityTwoHOL (shapeValsHOL (width := width) es) = true) :=
  ⟨shapeVal_every, shapeVals_every⟩

/-- Full original `every_inst_ok_less_pan_globals_compile`:
`∀ctxt code. EVERY (every_exp P) (exps_of code) ⇒
EVERY (every_exp P) (exps_of (pan_globals$compile ctxt code))`, by HOL's
`compile_ind` recursion (`compileProgExactHOL.induct`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_globals_compile"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem every_inst_ok_less_pan_globals_compile {width : Nat} [NeZero width] :
    ∀ (ctxt : PanGlobalsContextExact width) (code : ProgHOL width),
      everyExpListHOL panopArityTwoHOL (expsOfHOL code) = true →
        everyExpListHOL panopArityTwoHOL (expsOfHOL (compileProgExactHOL ctxt code)) = true := by
  intro ctxt code
  have hE := compileExp_every ctxt
  have hL := fun es h => (compileExpList_every ctxt es h).1
  induction code using compileProgExactHOL.induct ctxt
  case case30 =>
    rename_i p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    cases p <;> first
      | (simp_all [compileProgExactHOL, expsOfHOL]; done)
      | (rename_i h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; exact (h _ _ _ _ rfl).elim)
      | (rename_i h _ _ _ _ _; exact (h _ _ _ _ _ rfl).elim)
  all_goals
    rw [compileProgExactHOL]
    try simp_all [expsOfHOL, everyExpListHOL, everyExpListHOL_append, everyExpHOL,
      panopArityTwoHOL, shapeVal_every]
    try split <;> simp_all [expsOfHOL, everyExpListHOL, everyExpListHOL_append, everyExpHOL,
      panopArityTwoHOL, shapeVal_every]

end PanToWordEveryInstOkLessPanGlobals

end Flapjack
