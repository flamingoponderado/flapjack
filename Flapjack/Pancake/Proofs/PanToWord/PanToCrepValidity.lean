import Flapjack.Pancake.Proofs.PanToWord
import Flapjack.Pancake.Semantics.CrepProps
import Flapjack.Pancake.PanToCrep.CompileExact
import Flapjack.Pancake.CrepArith

namespace Flapjack

/-- Original Crepop binary-arity predicate rendered using the reviewed exact
expression codec and existing every_exp traversal. No separate HOL declaration. -/
def crepBinaryExp {width : Nat} [NeZero width] (e : CrepExpHOL width) : Bool :=
  crepEveryExp (fun x => match x with
    | .crepOp _ es => decide (es.length = 2)
    | _ => true) (crepExpOfHOL e)

abbrev crepBinaryList {width : Nat} [NeZero width] (es : List (CrepExpHOL width)) : Bool :=
  es.all crepBinaryExp
abbrev crepBinaryProg {width : Nat} [NeZero width] (p : CrepProgHOL width) : Bool :=
  crepBinaryList (crepExpsOfHOL p)

/-- Original expression-list equality for nested sequences, all constructors. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "exps_of_nested_seq"
  (words_as_type_indexed_bitvec)]
theorem crepExpsOfNestedSeqHOL {width : Nat} [NeZero width]
    (es : List (CrepProgHOL width)) :
    crepExpsOfHOL (crepNestedSeqHOL es) = (es.map crepExpsOfHOL).flatten := by
  induction es with
  | nil => simp only [crepNestedSeqHOL, crepExpsOfHOL, List.map_nil, List.flatten_nil]
  | cons e es ih => simp only [crepNestedSeqHOL, crepExpsOfHOL, List.map_cons,
      List.flatten_cons, ih]

/-- Original matched-length guard and full iff of nested declarations. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_nested_decs"
  (words_as_type_indexed_bitvec)]
theorem everyInstOk_nestedDecs {width : Nat} [NeZero width]
    (ns : List Nat) (ps : List (CrepExpHOL width)) (p : CrepProgHOL width)
    (lengths : ns.length = ps.length) :
    crepBinaryProg (nestedDecsHOL ns ps p) = true ↔
      crepBinaryList ps = true ∧ crepBinaryProg p = true := by
  induction ns generalizing ps with
  | nil =>
      cases ps <;> simp_all [nestedDecsHOL, crepBinaryProg, crepBinaryList]
  | cons n ns ih =>
      cases ps with
      | nil => simp at lengths
      | cons v vs =>
          have shorter : ns.length = vs.length := by simpa using lengths
          simp only [nestedDecsHOL, crepBinaryProg, crepExpsOfHOL, crepBinaryList,
            List.all_cons, Bool.and_eq_true]
          rw [show crepBinaryList (crepExpsOfHOL (nestedDecsHOL ns vs p)) = true ↔
            crepBinaryList vs = true ∧ crepBinaryProg p = true from ih vs shorter]
          simp only [crepBinaryList, and_assoc]

/-- Original store_globals iff; the fixed five-bit global address is retained. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_store_globals"
  (words_as_type_indexed_bitvec)]
theorem everyInstOkLess_storeGlobals {width : Nat} [NeZero width]
    (w : BitVec 5) (es : List (CrepExpHOL width)) :
    (storeGlobalsHOL w es).all crepBinaryProg = true ↔ crepBinaryList es = true := by
  induction es generalizing w with
  | nil => rfl
  | cons e es ih => simp [storeGlobalsHOL, crepBinaryProg, crepBinaryList,
      crepExpsOfHOL, ih]


/-- Original ordinary stores iff, including the empty-list conditional. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_stores"
  (words_as_type_indexed_bitvec)]
theorem everyInstOkLess_stores {width : Nat} [NeZero width]
    (e : CrepExpHOL width) (es : List (CrepExpHOL width)) (a : BitVec width) :
    (storesHOL e es a).all crepBinaryProg = true ↔
      (es ≠ [] → crepBinaryExp e = true) ∧ crepBinaryList es = true := by
  induction es generalizing a with
  | nil => simp [storesHOL, crepBinaryList]
  | cons v vs ih =>
      simp only [storesHOL]
      split <;> simp [List.all_cons, crepBinaryProg, crepBinaryList, crepExpsOfHOL,
        crepBinaryExp, crepExpOfHOL, crepEveryExp, crepEveryExpList, ih, and_assoc] <;>
        intro he _ _ _ <;> exact he

/-- Original shape-load input validity implication, arbitrary word offset/count. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_to_crep_load_shape"
  (words_as_type_indexed_bitvec)]
theorem everyInstOkLess_loadShape {width : Nat} [NeZero width]
    (w : BitVec width) (n : Nat) (e : CrepExpHOL width)
    (valid : crepBinaryExp e = true) :
    crepBinaryList (loadShapeBytesHOLW w n e) = true := by
  simp only [crepBinaryExp] at valid
  induction n generalizing w with
  | zero => simp [loadShapeBytesHOLW, crepBinaryList]
  | succ n ih =>
      simp only [loadShapeBytesHOLW]
      split <;> simp [crepBinaryList, crepBinaryExp, crepExpOfHOL, crepEveryExp,
        crepEveryExpList, valid, ih]


/-- Original successful head extraction preserves every nested binary condition. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_to_crep_cexp_heads"
  (words_as_type_indexed_bitvec)]
theorem everyInstOkLess_cexpHeads {width : Nat} [NeZero width]
    (ces : List (List (CrepExpHOL width))) (es : List (CrepExpHOL width))
    (valid : ces.all crepBinaryList = true) (heads : cexpHeads ces = some es) :
    crepBinaryList es = true := by
  induction ces generalizing es with
  | nil =>
      simp only [cexpHeads, Option.some.injEq] at heads
      subst es
      rfl
  | cons cs css ih =>
      cases cs with
      | nil => simp [cexpHeads] at heads
      | cons c cs =>
          cases found : cexpHeads css with
          | none => simp [cexpHeads, found] at heads
          | some rest =>
              simp only [cexpHeads, found, Option.some.injEq] at heads
              subst es
              have hs : crepBinaryList (c :: cs) = true ∧ css.all crepBinaryList = true := by
                simpa only [List.all_cons, Bool.and_eq_true] using valid
              have hcs : crepBinaryExp c = true ∧ crepBinaryList cs = true := by
                simpa only [crepBinaryList, List.all_cons, Bool.and_eq_true] using hs.1
              have hc := hcs.1
              simpa only [crepBinaryList, List.all_cons, Bool.and_eq_true] using
                And.intro hc (ih rest hs.2 found)


/-- Original field-selection result, retaining the source list guard and actual
pair equation over the exact shape carrier. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_to_crep_comp_field"
  (words_as_type_indexed_bitvec)]
theorem everyInstOkLess_compField {width : Nat} [NeZero width]
    (index : Nat) (shapes : List Flapjack.Pancake.PanLang.ShapeHOL)
    (es es' : List (CrepExpHOL width)) (sh : Flapjack.Pancake.PanLang.ShapeHOL)
    (valid : crepBinaryList es = true) (compiled : compFieldHOL index shapes es = (es', sh)) :
    crepBinaryList es' = true := by
  induction shapes generalizing index es es' sh with
  | nil =>
      simp only [compFieldHOL, Prod.mk.injEq] at compiled
      rw [← compiled.1]
      simp [crepBinaryList, crepBinaryExp, crepExpOfHOL, crepEveryExp]
  | cons shape shapes ih =>
      simp only [compFieldHOL] at compiled
      split at compiled
      · rw [← (Prod.mk.inj compiled).1]
        simp only [crepBinaryList, List.all_eq_true] at valid ⊢
        intro e he
        exact valid e (List.mem_of_mem_take he)
      · apply ih (index - 1) (es.drop _) es' sh _ compiled
        simp only [crepBinaryList, List.all_eq_true] at valid ⊢
        intro e he
        exact valid e (List.mem_of_mem_drop he)

end Flapjack
