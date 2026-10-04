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
  let rec go : (program : ProgHOL width) →
      everyExpListHOL panopArityTwoHOL (expsOfHOL (retToTailHOL program)) =
        everyExpListHOL panopArityTwoHOL (expsOfHOL program)
    | .skip => by
        simp only [retToTailHOL, expsOfHOL, everyExpListHOL]
    | .dec name shape value body => by
        simp only [retToTailHOL, expsOfHOL, everyExpListHOL]
        rw [go body]
    | .seq first second => by
        simp only [retToTailHOL]
        rw [show everyExpListHOL panopArityTwoHOL (expsOfHOL (seqCallRetHOL _)) =
          everyExpListHOL panopArityTwoHOL (expsOfHOL _) from binary_seqCallRet _]
        simp only [expsOfHOL, binary_append]
        rw [go first, go second]
    | .ite condition thenBranch elseBranch => by
        simp only [retToTailHOL, expsOfHOL, everyExpListHOL, binary_append]
        rw [go thenBranch, go elseBranch]
    | .while condition body => by
        simp only [retToTailHOL, expsOfHOL, everyExpListHOL]
        rw [go body]
    | .call info function arguments => by
        cases info with
        | none =>
            simp only [retToTailHOL, expsOfHOL]
        | some info =>
            cases info with
            | mk returns handlerInfo =>
                cases handlerInfo with
                | none =>
                    simp only [retToTailHOL, expsOfHOL]
                | some handler =>
                    cases handler with
                    | mk exception handlerInfo =>
                        cases handlerInfo with
                        | mk handlerVar handlerProgram =>
                            simp only [retToTailHOL]
                            simp only [expsOfHOL, binary_append]
                            rw [go handlerProgram]
    | .decCall name shape function arguments body => by
        simp only [retToTailHOL, expsOfHOL, binary_append]
        rw [go body]
    | .annot tag text => by
        simp only [retToTailHOL, expsOfHOL, everyExpListHOL]
    | .assign kind name value => by
        simp only [retToTailHOL, expsOfHOL, everyExpListHOL]
    | .primitive name operator args => by
        simp only [retToTailHOL, expsOfHOL]
    | .store address value => by
        simp only [retToTailHOL, expsOfHOL, everyExpListHOL]
    | .store32 address value => by
        simp only [retToTailHOL, expsOfHOL, everyExpListHOL]
    | .storeByte address value => by
        simp only [retToTailHOL, expsOfHOL, everyExpListHOL]
    | .break => by
        simp only [retToTailHOL, expsOfHOL, everyExpListHOL]
    | .continue => by
        simp only [retToTailHOL, expsOfHOL, everyExpListHOL]
    | .extCall function configuration configurationLength array arrayLength => by
        simp only [retToTailHOL, expsOfHOL, everyExpListHOL]
    | .raise exception value => by
        simp only [retToTailHOL, expsOfHOL, everyExpListHOL]
    | .return value => by
        simp only [retToTailHOL, expsOfHOL, everyExpListHOL]
    | .shMemLoad size kind name address => by
        simp only [retToTailHOL, expsOfHOL, everyExpListHOL]
    | .shMemStore size address value => by
        simp only [retToTailHOL, expsOfHOL, everyExpListHOL]
    | .tick => by
        simp only [retToTailHOL, expsOfHOL, everyExpListHOL]
    termination_by program => sizeOf program
    decreasing_by all_goals decreasing_trivial
  exact go program

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
  let rec go (pre : ProgHOL width) : (program : ProgHOL width) →
      (everyExpListHOL panopArityTwoHOL (expsOfHOL (seqAssocHOL pre program))) =
        ((everyExpListHOL panopArityTwoHOL (expsOfHOL pre)) &&
          (everyExpListHOL panopArityTwoHOL (expsOfHOL program)))
    | .skip => by
        simp [seqAssocHOL, expsOfHOL, everyExpListHOL]
    | .dec name shape value body => by
        simp only [seqAssocHOL]
        rw [binary_smartSeq]
        simp only [expsOfHOL, everyExpListHOL]
        rw [go .skip body]
        simp [expsOfHOL, everyExpListHOL]
    | .seq first second => by
        simp only [seqAssocHOL]
        rw [go (seqAssocHOL pre first) second, go pre first]
        simp [expsOfHOL, binary_append, Bool.and_assoc]
    | .ite condition thenBranch elseBranch => by
        simp only [seqAssocHOL]
        rw [binary_smartSeq]
        simp only [expsOfHOL, everyExpListHOL, binary_append]
        rw [go .skip thenBranch, go .skip elseBranch]
        simp [expsOfHOL, everyExpListHOL]
    | .while condition body => by
        simp only [seqAssocHOL]
        rw [binary_smartSeq]
        simp only [expsOfHOL, everyExpListHOL]
        rw [go .skip body]
        simp [expsOfHOL, everyExpListHOL]
    | .call info function arguments => by
        cases info with
        | none =>
            simp [seqAssocHOL, expsOfHOL,
              binary_smartSeq]
        | some info =>
            cases info with
            | mk returns handlerInfo =>
                cases handlerInfo with
                | none =>
                    simp [seqAssocHOL, expsOfHOL,
                      binary_smartSeq]
                | some handler =>
                    cases handler with
                    | mk exception handlerInfo =>
                        cases handlerInfo with
                        | mk handlerVar handlerProgram =>
                            simp only [seqAssocHOL]
                            rw [binary_smartSeq]
                            simp only [expsOfHOL, binary_append]
                            rw [go .skip handlerProgram]
                            simp [expsOfHOL, everyExpListHOL]
    | .decCall name shape function arguments body => by
        simp only [seqAssocHOL]
        rw [binary_smartSeq]
        simp only [expsOfHOL, binary_append]
        rw [go .skip body]
        simp [expsOfHOL, everyExpListHOL]
    | .annot tag text => by
        simp [seqAssocHOL, expsOfHOL, everyExpListHOL]
    | .assign kind name value => by
        simp only [seqAssocHOL]
        rw [binary_smartSeq]
    | .primitive name operator args => by
        simp only [seqAssocHOL]
        rw [binary_smartSeq]
    | .store address value => by
        simp only [seqAssocHOL]
        rw [binary_smartSeq]
    | .store32 address value => by
        simp only [seqAssocHOL]
        rw [binary_smartSeq]
    | .storeByte address value => by
        simp only [seqAssocHOL]
        rw [binary_smartSeq]
    | .break => by
        simp only [seqAssocHOL]
        rw [binary_smartSeq]
    | .continue => by
        simp only [seqAssocHOL]
        rw [binary_smartSeq]
    | .extCall function configuration configurationLength array arrayLength => by
        simp only [seqAssocHOL]
        rw [binary_smartSeq]
    | .raise exception value => by
        simp only [seqAssocHOL]
        rw [binary_smartSeq]
    | .return value => by
        simp only [seqAssocHOL]
        rw [binary_smartSeq]
    | .shMemLoad size kind name address => by
        simp only [seqAssocHOL]
        rw [binary_smartSeq]
    | .shMemStore size address value => by
        simp only [seqAssocHOL]
        rw [binary_smartSeq]
    | .tick => by
        simp only [seqAssocHOL]
        rw [binary_smartSeq]
    termination_by program => sizeOf program
    decreasing_by all_goals decreasing_trivial
  exact go pre program


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
