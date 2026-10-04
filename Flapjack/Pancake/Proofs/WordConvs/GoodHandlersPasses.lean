import Flapjack.Pancake.Proofs.WordConvs.NotCreatedPasses
import Flapjack.Pancake.WordConvs

/-!
# `wordConvsProof`: `word_good_handlers` through the word_simp and inst_select passes

The `word_good_handlers` preservation theorems of
`cakeml/compiler/backend/proofs/wordConvsProofScript.sml` for `word_simp` (657-760) and
`inst_select` (955-972). HOL's free label `n` (and the other free variables) are leading
binders; HOL's Boolean `word_good_handlers` is the tagged `goodHandlersHOL` with `= true`.
-/

namespace Flapjack.WordConvs

open Flapjack Flapjack.Compiler.Backend.WordSimp

/-- Boolean form of `word_good_handlers_SmartSeq` (Flapjack infrastructure). -/
theorem goodHandlers_smartSeq_eq {width : Nat} [NeZero width] (n : Nat)
    (p q : WordLangProgHOL (BitVec width)) :
    goodHandlersHOL n (smartSeqHOL p q) = (goodHandlersHOL n p && goodHandlersHOL n q) := by
  cases p <;> simp [smartSeqHOL, goodHandlersHOL]

/-- HOL `word_good_handlers_SmartSeq` (`wordConvsProofScript.sml:657-663`, `[local,simp]`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_SmartSeq"
  (words_as_type_indexed_bitvec)]
theorem goodHandlers_smartSeq {width : Nat} [NeZero width] (n : Nat)
    (p q : WordLangProgHOL (BitVec width)) :
    goodHandlersHOL n (smartSeqHOL p q) = true ↔
      goodHandlersHOL n p = true ∧ goodHandlersHOL n q = true := by
  rw [goodHandlers_smartSeq_eq, Bool.and_eq_true]

/-- Boolean form of `word_good_handlers_Seq_assoc` (Flapjack infrastructure). -/
theorem goodHandlers_seqAssoc_eq {width : Nat} [NeZero width] (n : Nat) :
    ∀ (p1 p2 : WordLangProgHOL (BitVec width)),
      goodHandlersHOL n (seqAssoc p1 p2) = (goodHandlersHOL n p1 && goodHandlersHOL n p2)
  | p1, .skip => by simp [seqAssoc, goodHandlersHOL]
  | p1, .seq q1 q2 => by
      rw [seqAssoc, goodHandlers_seqAssoc_eq n _ q2, goodHandlers_seqAssoc_eq n p1 q1]
      simp only [goodHandlersHOL, Bool.and_assoc]
  | p1, .ite v m r q1 q2 => by
      rw [seqAssoc, goodHandlers_smartSeq_eq]
      simp only [goodHandlersHOL, goodHandlers_seqAssoc_eq n .skip q1,
        goodHandlers_seqAssoc_eq n .skip q2, Bool.true_and]
  | p1, .mustTerminate q => by
      rw [seqAssoc, goodHandlers_smartSeq_eq]
      simp only [goodHandlersHOL, goodHandlers_seqAssoc_eq n .skip q, Bool.true_and]
  | p1, .call none dest args none => by
      rw [seqAssoc, goodHandlers_smartSeq_eq]
  | p1, .call none dest args (some (y1, q2, y2, y3)) => by
      rw [seqAssoc, goodHandlers_smartSeq_eq]
      simp only [goodHandlersHOL]
  | p1, .call (some (x1, x2, q1, x3, x4)) dest args none => by
      rw [seqAssoc, goodHandlers_smartSeq_eq]
      simp only [goodHandlersHOL, goodHandlers_seqAssoc_eq n .skip q1, Bool.true_and]
  | p1, .call (some (x1, x2, q1, x3, x4)) dest args (some (y1, q2, y2, y3)) => by
      rw [seqAssoc, goodHandlers_smartSeq_eq]
      simp only [goodHandlersHOL, goodHandlers_seqAssoc_eq n .skip q1,
        goodHandlers_seqAssoc_eq n .skip q2, Bool.true_and]
  | p1, .loop names body exitNames => by
      rw [seqAssoc, goodHandlers_smartSeq_eq]
      simp only [goodHandlersHOL, goodHandlers_seqAssoc_eq n .skip body, Bool.true_and]
  | p1, .move _ _ | p1, .inst _ | p1, .assign _ _ | p1, .get _ _ | p1, .set _ _
  | p1, .store _ _ | p1, .alloc _ _ | p1, .storeConsts _ _ _ _ _ | p1, .raise _
  | p1, .return _ _ | p1, .break _ | p1, .continue _ | p1, .tick | p1, .opCurrHeap _ _ _
  | p1, .locValue _ _ | p1, .install _ _ _ _ _ | p1, .codeBufferWrite _ _
  | p1, .dataBufferWrite _ _ | p1, .ffi _ _ _ _ _ _ | p1, .shareInst _ _ _ =>
      goodHandlers_smartSeq_eq n p1 _

/-- HOL `word_good_handlers_Seq_assoc` (`wordConvsProofScript.sml:694-702`, `[local]`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_Seq_assoc"
  (words_as_type_indexed_bitvec)]
theorem goodHandlers_seqAssoc {width : Nat} [NeZero width] (n : Nat) :
    ∀ (p1 p2 : WordLangProgHOL (BitVec width)),
      goodHandlersHOL n (seqAssoc p1 p2) = true ↔
        goodHandlersHOL n p1 = true ∧ goodHandlersHOL n p2 = true :=
  fun p1 p2 => by rw [goodHandlers_seqAssoc_eq, Bool.and_eq_true]

/-- HOL `word_good_handlers_drop_consts` (`wordConvsProofScript.sml:665-671`, `[local,simp]`);
    HOL's free `n l` are explicit. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_drop_consts"
  (words_as_type_indexed_bitvec)]
theorem goodHandlers_dropConsts {width : Nat} [NeZero width] (n : Nat) (l : Spt (BitVec width)) :
    ∀ args : List Nat, goodHandlersHOL n (dropConsts l args) = true
  | [] => by simp [dropConsts, goodHandlersHOL]
  | x :: xs => by
      simp only [dropConsts]
      split
      · exact goodHandlers_dropConsts n l xs
      · rw [goodHandlers_smartSeq_eq, goodHandlers_dropConsts n l xs]; simp [goodHandlersHOL]

/-- HOL `word_good_handlers_const_fp_loop` (`wordConvsProofScript.sml:673-692`, `[local]`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_const_fp_loop"
  (words_as_type_indexed_bitvec)]
theorem goodHandlers_constFpLoop {width : Nat} [NeZero width] (n : Nat) :
    ∀ (p : WordLangProgHOL (BitVec width)) (l : Spt (BitVec width)),
      goodHandlersHOL n p = true → goodHandlersHOL n (constFpLoop p l).1 = true := by
  intro p l
  fun_induction constFpLoop p l <;> intro h <;>
    simp_all [goodHandlersHOL, goodHandlers_smartSeq_eq, goodHandlers_dropConsts]

/-- HOL `word_good_handlers_try_if_hoist2` (`wordConvsProofScript.sml:704-722`, `[local]`). HOL's
    free `n p3` lead; HOL's universally bound `s` occurs nowhere in the statement (it is vacuous
    and has an unconstrained type), so it is omitted. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_try_if_hoist2"
  (words_as_type_indexed_bitvec)]
theorem goodHandlers_hoist2 {width : Nat} [NeZero width] (n : Nat)
    (p3 : WordLangProgHOL (BitVec width)) :
    ∀ (N : Nat) (p1 interm dummy p2 : WordLangProgHOL (BitVec width)),
      tryIfHoist2 N p1 interm dummy p2 = some p3 →
      goodHandlersHOL n p1 = true ∧ goodHandlersHOL n p2 = true ∧
        goodHandlersHOL n interm = true →
      goodHandlersHOL n p3 = true := by
  intro N p1 interm dummy p2
  fun_induction tryIfHoist2 N p1 interm dummy p2 <;> intro he ⟨h1, h2, hi⟩
  all_goals first
    | (simp at he; done)
    | skip
  case case4 =>
    obtain rfl := Option.some.inj he
    apply goodHandlers_constFpLoop
    simp only [goodHandlersHOL, Bool.and_eq_true] at h1 ⊢
    exact ⟨⟨⟨h1.1, hi⟩, h2⟩, ⟨h1.2, hi⟩, h2⟩
  case case7 =>
    obtain rfl := Option.some.inj he
    rename_i n' interm dummy p2 p3' p4 cmp lhs rhs br1 br2 hd res1 hr1 res2 hr2
    rw [destIf_some hd] at h1
    simp only [goodHandlersHOL, Bool.and_eq_true] at h1 ⊢
    refine ⟨h1.1, goodHandlers_constFpLoop n _ _ ?_⟩
    simp only [goodHandlersHOL, Bool.and_eq_true]
    exact ⟨⟨⟨h1.2.1, hi⟩, h2⟩, ⟨h1.2.2, hi⟩, h2⟩
  case case8 =>
    rename_i ih
    simp only [goodHandlersHOL, Bool.and_eq_true] at h1
    exact ih he ⟨h1.1, h2, by simp only [goodHandlersHOL, Bool.and_eq_true]; exact ⟨h1.2, hi⟩⟩

/-- HOL `word_good_handlers_simp_duplicate_if` (`wordConvsProofScript.sml:724-737`, `[local]`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_good_handlers_simp_duplicate_if" (words_as_type_indexed_bitvec)]
theorem goodHandlers_simpDuplicateIf {width : Nat} [NeZero width] (n : Nat) :
    ∀ p : WordLangProgHOL (BitVec width), goodHandlersHOL n p = true →
      goodHandlersHOL n (simpDuplicateIf p) = true := by
  intro p
  fun_induction simpDuplicateIf p <;> intro h
  case case2 ret dest args handler ih2 ih1 =>
    rcases ret with _ | ⟨x1, x2, q1, x3, x4⟩ <;> rcases handler with _ | ⟨y1, q2, y2, y3⟩ <;>
      simp_all [goodHandlersHOL]
  case case4 p1 p2 _ ih2 ih1 =>
    simp only [goodHandlersHOL, Bool.and_eq_true] at h ⊢
    exact ⟨ih2 h.1, ih1 h.2⟩
  case case5 p1 p2 p3 hh ih2 ih1 =>
    simp only [goodHandlersHOL, Bool.and_eq_true] at h
    rw [goodHandlers_seqAssoc_eq, Bool.and_eq_true]
    refine ⟨rfl, ?_⟩
    simp only [tryIfHoist1] at hh
    split at hh
    · simp at hh
    · exact goodHandlers_hoist2 n p3 _ _ _ _ _ hh ⟨ih2 h.1, ih1 h.2, rfl⟩
  case case7 => exact h
  all_goals simp_all [goodHandlersHOL]

/-- `push_out_if_aux` keeps `word_good_handlers` of the program component (Flapjack
    infrastructure for the HOL lemma below). -/
theorem goodHandlers_pushOutIfAux {width : Nat} [NeZero width] (n : Nat)
    (p : WordLangProgHOL (BitVec width)) :
    goodHandlersHOL n (pushOutIfAux p).1 = goodHandlersHOL n p := by
  fun_induction pushOutIfAux p <;>
    simp_all [goodHandlersHOL, Bool.and_comm]

/-- HOL `word_good_handlers_simp_push_out_if` (`wordConvsProofScript.sml:739-750`, `[local]`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_good_handlers_simp_push_out_if" (words_as_type_indexed_bitvec)]
theorem goodHandlers_pushOutIf {width : Nat} [NeZero width] (n : Nat) :
    ∀ p : WordLangProgHOL (BitVec width), goodHandlersHOL n p = true →
      goodHandlersHOL n (pushOutIf p) = true :=
  fun p h => (goodHandlers_pushOutIfAux n p).trans h

/-- HOL `word_good_handlers_word_simp` (`wordConvsProofScript.sml:752-760`, `[local]`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_word_simp"
  (words_as_type_indexed_bitvec)]
theorem goodHandlers_compileExp {width : Nat} [NeZero width] (n : Nat) :
    ∀ ps : WordLangProgHOL (BitVec width), goodHandlersHOL n ps = true →
      goodHandlersHOL n (compileExp ps) = true := by
  intro ps h
  simp only [compileExp]
  apply goodHandlers_pushOutIf
  apply goodHandlers_simpDuplicateIf
  apply goodHandlers_constFpLoop
  rw [goodHandlers_seqAssoc_eq, h]
  rfl

section InstSelect

open Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Encoders.Asm

/-- HOL `word_good_handlers_inst_select_exp` (`wordConvsProofScript.sml:955-962`, `[local]`);
    HOL's free `n` leads. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_good_handlers_inst_select_exp" (words_as_type_indexed_bitvec)]
theorem goodHandlers_instSelectExp {width : Nat} [NeZero width] (n : Nat) :
    ∀ (a : AsmConfigExact width) (b c : Nat) (exp : WordLangExpHOL (BitVec width)),
      goodHandlersHOL n (instSelectExp a b c exp) = true := by
  intro a b c exp
  induction exp using (measure (fun e : WordLangExpHOL (BitVec width) => sizeOf e)).wf.induction
      generalizing b c with
  | h exp ih =>
    fun_cases instSelectExp a b c exp <;>
      simp_all +zetaDelta [instSelectExp, goodHandlersHOL]
    all_goals
      repeat' first
        | (apply ih; simp_wf; omega)
        | simp_all +zetaDelta [goodHandlersHOL, isLookupCurrHeap]
        | split
        | constructor
    case case3 =>
      rename_i child notAddress
      apply ih child
      change sizeOf child < sizeOf (WordLangExpHOL.load child)
      simp

/-- Boolean form of `word_good_handlers_inst_select` (Flapjack infrastructure). -/
theorem goodHandlers_instSelect_eq {width : Nat} [NeZero width] (n : Nat)
    (ac : AsmConfigExact width) (v : Nat) (ps : WordLangProgHOL (BitVec width)) :
    goodHandlersHOL n (instSelect ac v ps) = goodHandlersHOL n ps := by
  induction ps using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction with
  | h ps ih =>
    fun_cases instSelect ac v ps <;>
      simp_all +zetaDelta [goodHandlersHOL, goodHandlers_instSelectExp]
    all_goals
      repeat' first
        | (rw [ih _ (by change sizeOf _ < sizeOf _; simp <;> omega)])
        | simp_all +zetaDelta [goodHandlersHOL]
        | split

/-- HOL `word_good_handlers_inst_select` (`wordConvsProofScript.sml:964-972`, `[local]`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_inst_select"
  (words_as_type_indexed_bitvec)]
theorem goodHandlers_instSelect {width : Nat} [NeZero width] (n : Nat) :
    ∀ (ac : AsmConfigExact width) (v : Nat) (ps : WordLangProgHOL (BitVec width)),
      goodHandlersHOL n (instSelect ac v ps) = true ↔ goodHandlersHOL n ps = true :=
  fun ac v ps => by rw [goodHandlers_instSelect_eq]

end InstSelect

end Flapjack.WordConvs
