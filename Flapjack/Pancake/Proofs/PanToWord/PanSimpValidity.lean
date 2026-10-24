import Flapjack.Pancake.Proofs.PanToWord

namespace Flapjack
open Flapjack.Pancake.PanLang

/-- The original binary-Panop condition on a program. Proof infrastructure,
not a separate HOL declaration. -/
abbrev panBinaryProg {width : Nat} [NeZero width] (p : ProgHOL width) : Bool :=
  everyExpListHOL panopArityTwoHOL (expsOfHOL p)

private theorem binary_append {width : Nat} [NeZero width]
    (xs ys : List (ExpHOL width)) :
    everyExpListHOL panopArityTwoHOL (xs ++ ys) =
      (everyExpListHOL panopArityTwoHOL xs && everyExpListHOL panopArityTwoHOL ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [everyExpListHOL, ih, Bool.and_assoc]

private theorem binary_seqCallRet {width : Nat} [NeZero width] (p : ProgHOL width) :
    panBinaryProg (seqCallRetHOL p) = panBinaryProg p := by
  unfold seqCallRetHOL
  split
  · split <;> simp [panBinaryProg, expsOfHOL, binary_append, everyExpListHOL,
      everyExpHOL, panopArityTwoHOL]
  · rfl

theorem panBinary_retToTail_eq {width : Nat} [NeZero width]
    (program : ProgHOL width) :
    everyExpListHOL panopArityTwoHOL (expsOfHOL (retToTailHOL program)) =
      everyExpListHOL panopArityTwoHOL (expsOfHOL program) := by
  fun_induction expIdsHOL program with
  | case14 info _ _ noHandler =>
      rcases info with _ | ⟨returns, _ | ⟨exception, handlerVar, handler⟩⟩
      · simp [retToTailHOL, expsOfHOL]
      · simp [retToTailHOL, expsOfHOL]
      · exact (noHandler returns exception handlerVar handler rfl).elim
  | _ =>
      grind only [retToTailHOL, binary_seqCallRet,
        expsOfHOL, binary_append, everyExpListHOL]

private theorem binary_smartSeq {width : Nat} [NeZero width] (pre p : ProgHOL width) :
    everyExpListHOL panopArityTwoHOL (expsOfHOL (smartSeqHOL pre p)) =
      (everyExpListHOL panopArityTwoHOL (expsOfHOL pre) &&
       everyExpListHOL panopArityTwoHOL (expsOfHOL p)) := by
  cases pre <;> simp [smartSeqHOL, expsOfHOL, binary_append, everyExpListHOL, Bool.and_assoc]

theorem panBinary_seqAssoc_eq {width : Nat} [NeZero width]
    (pre program : ProgHOL width) :
    (everyExpListHOL panopArityTwoHOL (expsOfHOL (seqAssocHOL pre program))) =
      ((everyExpListHOL panopArityTwoHOL (expsOfHOL pre)) &&
        (everyExpListHOL panopArityTwoHOL (expsOfHOL program))) := by
  fun_induction expIdsHOL program generalizing pre with
  | case14 info _ _ noHandler =>
      rcases info with _ | ⟨returns, _ | ⟨exception, handlerVar, handler⟩⟩
      · simp [seqAssocHOL, expsOfHOL, binary_smartSeq]
      · simp [seqAssocHOL, expsOfHOL, binary_smartSeq]
      · exact (noHandler returns exception handlerVar handler rfl).elim
  | _ =>
      simp_all only [seqAssocHOL, binary_smartSeq, expsOfHOL,
        binary_append, everyExpListHOL, Bool.and_assoc, Bool.true_and, Bool.and_true]

/-- The original EVERY/every_exp condition is preserved in both directions.
Uses exact width-indexed syntax; no additional predicate hypothesis. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_ret_to_tail"
  (words_as_type_indexed_bitvec)]
theorem everyInstOkLess_retToTail {width : Nat} [NeZero width] (p : ProgHOL width) :
    panBinaryProg (retToTailHOL p) = true ↔ panBinaryProg p = true := by
  rw [show panBinaryProg (retToTailHOL p) = panBinaryProg p from panBinary_retToTail_eq p]

/-- HOL's complete two-program equivalence, retaining the appended expression list. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_seq_assoc"
  (words_as_type_indexed_bitvec)]
theorem everyInstOkLess_seqAssoc {width : Nat} [NeZero width] (p q : ProgHOL width) :
    panBinaryProg (seqAssocHOL p q) = true ↔
      everyExpListHOL panopArityTwoHOL (expsOfHOL p ++ expsOfHOL q) = true := by
  rw [show panBinaryProg (seqAssocHOL p q) =
    (panBinaryProg p && panBinaryProg q) from panBinary_seqAssoc_eq p q]
  rw [binary_append]

/-- Original implication, composed from the two exact syntactic equivalences. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_simp_compile"
  (words_as_type_indexed_bitvec)]
theorem everyInstOkLess_panSimpCompile {width : Nat} [NeZero width] (body : ProgHOL width)
    (valid : panBinaryProg body = true) : panBinaryProg (panSimpCompileHOL body) = true := by
  unfold panSimpCompileHOL
  apply (everyInstOkLess_retToTail _).2
  apply (everyInstOkLess_seqAssoc _ _).2
  simpa only [expsOfHOL, List.nil_append] using valid

/-- Original whole declaration-list result, including non-function declarations. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_simp_compile_prog"
  (words_as_type_indexed_bitvec)]
theorem everyInstOkLess_panSimpCompileProg {width : Nat} [NeZero width]
    (code : List (DeclHOL width)) (valid : code.all goodPanopsHOL = true) :
    (panSimpDeclsHOL code).all goodPanopsHOL = true := by
  induction code with
  | nil => simp only [panSimpDeclsHOL, List.all_nil]
  | cons declaration code ih =>
      have h : goodPanopsHOL declaration = true ∧ code.all goodPanopsHOL = true := by
        simpa only [List.all_cons, Bool.and_eq_true] using valid
      cases declaration <;> simp only [panSimpDeclsHOL, List.all_cons, goodPanopsHOL, Bool.and_eq_true] at *
      · exact ⟨everyInstOkLess_panSimpCompile _ h.1, ih h.2⟩
      all_goals exact ⟨h.1, ih h.2⟩

end Flapjack
