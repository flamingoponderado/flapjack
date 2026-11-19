module

public import Flapjack.Compiler.Backend.WordSimp
public import Flapjack.Pancake.WordConvs
public import Flapjack.Pancake.WordConvs.CodeLabels
public import Flapjack.Pancake.Proofs.WordConvs.SmartSeqLabels

@[expose] public section

namespace Flapjack.WordConvs
open Flapjack.Compiler.Backend.WordSimp

/-- Full original SmartSeq label equality for arbitrary native programs. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_SmartSeq"
  (words_as_type_indexed_bitvec)]
theorem extractLabelsSmartSeq {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width)) :
    extractLabels (smartSeqHOL first second) = extractLabels (.seq first second) := by
  cases first <;> simp [smartSeqHOL, extractLabels]

/-- Full original Seq_assoc label equality, including both actual recursive
handler families and arbitrary accumulator. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_Seq_assoc_lemma"
  (words_as_type_indexed_bitvec)]
theorem extractLabelsSeqAssocLemma {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width)) :
    extractLabels (seqAssoc first second) = extractLabels first ++ extractLabels second := by
  induction second using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction
      generalizing first with
  | h second ih =>
    fun_cases seqAssoc first second <;>
      simp only [extractLabelsSmartSeq, extractLabels, List.append_nil]

    case case2 q1 q2 =>
      rw [ih q2 (by
        change sizeOf q2 < sizeOf (.seq q1 q2 : WordLangProgHOL (BitVec width))
        simp
        omega)]
      rw [ih q1 (by
        change sizeOf q1 < sizeOf (.seq q1 q2 : WordLangProgHOL (BitVec width))
        simp
        omega)]
      simp only [List.append_assoc]
    case case3 cmp reg imm q1 q2 =>
      rw [ih q1 (by
        change sizeOf q1 < sizeOf (.ite cmp reg imm q1 q2 : WordLangProgHOL (BitVec width))
        simp
        omega)]
      rw [ih q2 (by
        change sizeOf q2 < sizeOf (.ite cmp reg imm q1 q2 : WordLangProgHOL (BitVec width))
        simp
        omega)]
      rfl
    case case4 q =>
      rw [ih q (by
        change sizeOf q < sizeOf (.mustTerminate q : WordLangProgHOL (BitVec width))
        simp)]
      rfl
    case case5 ret dest args handler =>
      cases ret with
      | none => simp only [extractLabels]
      | some ret =>
        rcases ret with ⟨ns,cuts,q,l1,l2⟩
        cases handler with
        | none =>
          simp only [extractLabels]
          rw [ih q (by
            change sizeOf q <
              sizeOf (.call (some (ns,cuts,q,l1,l2)) dest args none :
                WordLangProgHOL (BitVec width))
            simp
            omega)]
          rfl
        | some handler =>
          rcases handler with ⟨n,body,h1,h2⟩
          simp only [extractLabels]
          rw [ih q (by
            change sizeOf q <
              sizeOf (.call (some (ns,cuts,q,l1,l2)) dest args (some (n,body,h1,h2)) :
                WordLangProgHOL (BitVec width))
            simp
            omega)]
          rw [ih body (by
            change sizeOf body <
              sizeOf (.call (some (ns,cuts,q,l1,l2)) dest args (some (n,body,h1,h2)) :
                WordLangProgHOL (BitVec width))
            simp
            omega)]
          rfl
    case case6 names body exits =>
      rw [ih body (by
        change sizeOf body < sizeOf (.loop names body exits : WordLangProgHOL (BitVec width))
        simp
        omega)]
      rfl

/-- Full original `Seq_assoc` code-label equality: the reassociated program has
exactly the union of its two operands' labels, for arbitrary accumulator. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_get_code_labels_Seq_assoc" (words_as_type_indexed_bitvec)]
theorem getCodeLabels_seqAssoc {width : Nat} [NeZero width]
    (p1 p2 : WordLangProgHOL (BitVec width)) :
    getCodeLabelsHOL (seqAssoc p1 p2) = getCodeLabelsHOL p1 ∪ getCodeLabelsHOL p2 := by
  induction p2 using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction
      generalizing p1 with
  | h p2 ih =>
    fun_cases seqAssoc p1 p2 <;>
      simp_all only [getCodeLabelsHOL, getCodeLabels_smartSeqHOL]
    case h.case1 =>
      simp only [Set.union_empty]
    case h.case2 q1 q2 =>
      rw [ih q2 (by
        change sizeOf q2 < sizeOf (.seq q1 q2 : WordLangProgHOL (BitVec width))
        simp
        omega) (seqAssoc p1 q1)]
      rw [ih q1 (by
        change sizeOf q1 < sizeOf (.seq q1 q2 : WordLangProgHOL (BitVec width))
        simp
        omega) p1]
      simp only [Set.union_assoc]
    case h.case3 v n r q1 q2 =>
      rw [ih q1 (by
        change sizeOf q1 < sizeOf (.ite v n r q1 q2 : WordLangProgHOL (BitVec width))
        simp
        omega) .skip]
      rw [ih q2 (by
        change sizeOf q2 < sizeOf (.ite v n r q1 q2 : WordLangProgHOL (BitVec width))
        simp
        omega) .skip]
      simp only [getCodeLabelsHOL, Set.empty_union]
    case h.case4 q =>
      rw [ih q (by
        change sizeOf q < sizeOf (.mustTerminate q : WordLangProgHOL (BitVec width))
        simp) .skip]
      simp only [getCodeLabelsHOL, Set.empty_union]
    case h.case5 ret dest args handler =>
      cases ret with
      | none =>
        cases handler with
        | none => simp only [getCodeLabelsHOL]
        | some h =>
          obtain ⟨n, body, l1, l2⟩ := h
          simp only [getCodeLabelsHOL]
          rw [ih body (by
            change sizeOf body < sizeOf
              (.call none dest args (some (n, body, l1, l2)) :
                WordLangProgHOL (BitVec width))
            simp
            omega) .skip]
          simp only [getCodeLabelsHOL, Set.empty_union]
      | some r =>
        obtain ⟨ns, cuts, q, l1, l2⟩ := r
        cases handler with
        | none =>
          simp only [getCodeLabelsHOL]
          rw [ih q (by
            change sizeOf q < sizeOf
              (.call (some (ns, cuts, q, l1, l2)) dest args none :
                WordLangProgHOL (BitVec width))
            simp
            omega) .skip]
          simp only [getCodeLabelsHOL, Set.empty_union]
        | some h =>
          obtain ⟨n, body, h1, h2⟩ := h
          simp only [getCodeLabelsHOL]
          rw [ih q (by
            change sizeOf q < sizeOf
              (.call (some (ns, cuts, q, l1, l2)) dest args (some (n, body, h1, h2)) :
                WordLangProgHOL (BitVec width))
            simp
            omega) .skip]
          rw [ih body (by
            change sizeOf body < sizeOf
              (.call (some (ns, cuts, q, l1, l2)) dest args (some (n, body, h1, h2)) :
                WordLangProgHOL (BitVec width))
            simp
            omega) .skip]
          simp only [getCodeLabelsHOL, Set.empty_union, Set.union_assoc]
    case h.case6 names body exits =>
      rw [ih body (by
        change sizeOf body < sizeOf (.loop names body exits : WordLangProgHOL (BitVec width))
        simp
        omega) .skip]
      simp only [getCodeLabelsHOL, Set.empty_union]

/-- Full original Skip-accumulator sequence reassociation label equality. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_Seq_assoc"
  (words_as_type_indexed_bitvec)]
theorem extractLabelsSeqAssoc {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) :
    extractLabels (seqAssoc .skip program) = extractLabels program := by
  simpa only [extractLabels, List.nil_append] using extractLabelsSeqAssocLemma .skip program

/-- Full original materialized-constant program has no labels, for arbitrary
knowledge tree and register list. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_drop_consts_1"
  (words_as_type_indexed_bitvec)]
theorem extractLabelsDropConsts1 {width : Nat} [NeZero width]
    (cs : Spt (BitVec width)) (names : List Nat) :
    extractLabels (dropConsts cs names) = [] := by
  induction names with
  | nil => rfl
  | cons name names ih =>
    simp only [dropConsts]
    split <;> simp_all [extractLabelsSmartSeq, extractLabels]

/-- Full original drop-constant prefix label equality with arbitrary continuation. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_drop_consts"
  (words_as_type_indexed_bitvec)]
theorem extractLabelsDropConsts {width : Nat} [NeZero width]
    (cs : Spt (BitVec width)) (names : List Nat) (program : WordLangProgHOL (BitVec width)) :
    extractLabels (smartSeqHOL (dropConsts cs names) program) = extractLabels program := by
  simp only [extractLabelsSmartSeq, extractLabels, extractLabelsDropConsts1, List.nil_append]

/-- Full original materialized-constant program has no code labels, for
arbitrary knowledge tree and register list. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_get_code_labels_drop_consts" (words_as_type_indexed_bitvec)]
theorem getCodeLabels_dropConsts {width : Nat} [NeZero width]
    (cs : Spt (BitVec width)) (args : List Nat) :
    getCodeLabelsHOL (dropConsts cs args) = ∅ := by
  induction args with
  | nil => simp [dropConsts, getCodeLabelsHOL]
  | cons name names ih =>
    simp only [dropConsts]
    split
    · simpa using ih
    · rw [getCodeLabels_smartSeqHOL]
      simp [getCodeLabelsHOL, ih]

/-- Original generic append-permutation implication, retaining all label carriers.
There is no word-program binder in this list-only statement. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "labels_rel_append_imp"]
theorem labelsRelAppendImp {β : Type} (X Y Z : List β)
    (related : labelsRel (Y ++ X) Z) : labelsRel (X ++ Y) Z :=
  labelsRel_trans (labelsRel_of_perm (List.perm_append_comm : (Y ++ X).Perm (X ++ Y))) related

end Flapjack.WordConvs
