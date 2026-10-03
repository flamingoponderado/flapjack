load "preamble";
load "lab_to_targetProofTheory";
open HolKernel Parse preamble byteTheory miscTheory lab_to_targetProofTheory;
val _ = Globals.max_print_depth := 1000;
fun emit label th = if null(hyp th) then
 (print(label ^ "="); print_term(concl th); print "\n")
 else raise Fail(label ^ " has hypotheses");
fun emit_types label th =
 (show_types := true; emit label th; show_types := false);
(* Statements of lab_to_targetProofScript.sml Inst_lemma helpers.  [local]
   theorems are not exported, so their exact unchanged statement text is
   re-elaborated and printed with inferred types (statement captures, not
   theorem replays). *)
fun stmt label tm = (print(label ^ "="); print_term tm; print "\n");
fun stmt_types label tm =
 (show_types := true; stmt label tm; show_types := false);
val _ = emit "get_byte_set_byte" get_byte_set_byte;
val _ = emit_types "get_byte_set_byte_types" get_byte_set_byte;
val _ = emit "good_dimindex_get_byte_set_byte" good_dimindex_get_byte_set_byte;
val _ = emit_types "good_dimindex_get_byte_set_byte_types" good_dimindex_get_byte_set_byte;
val _ = emit "get_byte_set_byte_diff" get_byte_set_byte_diff;
val _ = emit_types "get_byte_set_byte_diff_types" get_byte_set_byte_diff;
val MULT_ADD_LESS_MULT_tm = ``
  !m n k l j. m < l /\ n < k /\ j <= k ==> m * j + n < l * k:num
``;
val _ = stmt "MULT_ADD_LESS_MULT" MULT_ADD_LESS_MULT_tm;
val _ = stmt_types "MULT_ADD_LESS_MULT_types" MULT_ADD_LESS_MULT_tm;
val aligned_IMP_ADD_LESS_dimword_tm = ``
  aligned k (x:'a word) /\ k <= dimindex (:'a) ==>
    w2n x + (2 ** k - 1) < dimword (:'a)
``;
val _ = stmt "aligned_IMP_ADD_LESS_dimword" aligned_IMP_ADD_LESS_dimword_tm;
val _ = stmt_types "aligned_IMP_ADD_LESS_dimword_types" aligned_IMP_ADD_LESS_dimword_tm;
val aligned_2_imp_tm = ``
   aligned 2 (x:'a word) /\ dimindex (:'a) = 32 ==>
    byte_align x = x ∧
    byte_align (x + 1w) = x ∧
    byte_align (x + 2w) = x ∧
    byte_align (x + 3w) = x
``;
val _ = stmt "aligned_2_imp" aligned_2_imp_tm;
val _ = stmt_types "aligned_2_imp_types" aligned_2_imp_tm;
val aligned_2_not_eq_tm = ``
   aligned 2 (x:'a word) ∧ dimindex(:'a) = 32 ∧
    x ≠ byte_align a ⇒
    x ≠ a ∧
    x+1w ≠ a ∧
    x+2w ≠ a ∧
    x+3w ≠ a
``;
val _ = stmt "aligned_2_not_eq" aligned_2_not_eq_tm;
val _ = stmt_types "aligned_2_not_eq_types" aligned_2_not_eq_tm;
val aligned_3_imp_tm = ``
   aligned 3 (x:'a word) /\ dimindex (:'a) = 64 ==>
    byte_align x = x ∧
    byte_align (x + 1w) = x ∧
    byte_align (x + 2w) = x ∧
    byte_align (x + 3w) = x ∧
    byte_align (x + 4w) = x ∧
    byte_align (x + 5w) = x ∧
    byte_align (x + 6w) = x ∧
    byte_align (x + 7w) = x
``;
val _ = stmt "aligned_3_imp" aligned_3_imp_tm;
val _ = stmt_types "aligned_3_imp_types" aligned_3_imp_tm;
val aligned_3_not_eq_tm = ``
   aligned 3 (x:'a word) ∧ dimindex(:'a) = 64 ∧
    x ≠ byte_align a ⇒
    x ≠ a ∧
    x+1w ≠ a ∧
    x+2w ≠ a ∧
    x+3w ≠ a ∧
    x+4w ≠ a ∧
    x+5w ≠ a ∧
    x+6w ≠ a ∧
    x+7w ≠ a
``;
val _ = stmt "aligned_3_not_eq" aligned_3_not_eq_tm;
val _ = stmt_types "aligned_3_not_eq_types" aligned_3_not_eq_tm;
val dimword_eq_32_imp_or_bytes_tm = ``
  dimindex (:'a) = 32 ==>
    (w2w ((w2w (x:'a word)):word8) ||
     w2w ((w2w (x ⋙ 8)):word8) ≪ 8 ||
     w2w ((w2w (x ⋙ 16)):word8) ≪ 16 ||
     w2w ((w2w (x ⋙ 24)):word8) ≪ 24) = x
``;
val _ = stmt "dimword_eq_32_imp_or_bytes" dimword_eq_32_imp_or_bytes_tm;
val _ = stmt_types "dimword_eq_32_imp_or_bytes_types" dimword_eq_32_imp_or_bytes_tm;
val dimword_eq_64_imp_or_bytes_tm = ``
  dimindex (:'a) = 64 ==>
    (w2w ((w2w (x:'a word)):word8) ||
     w2w ((w2w (x ⋙ 8)):word8) ≪ 8 ||
     w2w ((w2w (x ⋙ 16)):word8) ≪ 16 ||
     w2w ((w2w (x ⋙ 24)):word8) ≪ 24 ||
     w2w ((w2w (x ⋙ 32)):word8) ≪ 32 ||
     w2w ((w2w (x ⋙ 40)):word8) ≪ 40 ||
     w2w ((w2w (x ⋙ 48)):word8) ≪ 48 ||
     w2w ((w2w (x ⋙ 56)):word8) ≪ 56) = x
``;
val _ = stmt "dimword_eq_64_imp_or_bytes" dimword_eq_64_imp_or_bytes_tm;
val _ = stmt_types "dimword_eq_64_imp_or_bytes_types" dimword_eq_64_imp_or_bytes_tm;
val byte_align_32_eq_tm = ``
  dimindex (:'a) = 32 ⇒
  byte_align (a:'a word) +n2w (w2n a MOD 4) = a
``;
val _ = stmt "byte_align_32_eq" byte_align_32_eq_tm;
val _ = stmt_types "byte_align_32_eq_types" byte_align_32_eq_tm;
val byte_align_64_eq_tm = ``
  dimindex (:'a) = 64 ⇒
  byte_align (a:'a word) +n2w (w2n a MOD 8) = a
``;
val _ = stmt "byte_align_64_eq" byte_align_64_eq_tm;
val _ = stmt_types "byte_align_64_eq_types" byte_align_64_eq_tm;
val byte_align_32_IMP_tm = ``
  dimindex(:'a) = 32 ⇒
  (byte_align a = a ⇒ w2n a MOD 4 = 0) ∧
  (byte_align a + (1w:'a word) = a ⇒ w2n a MOD 4 = 1) ∧
  (byte_align a + (2w:'a word) = a ⇒ w2n a MOD 4 = 2) ∧
  (byte_align a + (3w:'a word) = a ⇒ w2n a MOD 4 = 3)
``;
val _ = stmt "byte_align_32_IMP" byte_align_32_IMP_tm;
val _ = stmt_types "byte_align_32_IMP_types" byte_align_32_IMP_tm;
val MOD4_CASES_tm = ``
  ∀n. n MOD 4 = 0 ∨ n MOD 4 = 1 ∨ n MOD 4 = 2 ∨ n MOD 4 = 3
``;
val _ = stmt "MOD4_CASES" MOD4_CASES_tm;
val _ = stmt_types "MOD4_CASES_types" MOD4_CASES_tm;
val byte_align_32_CASES_tm = ``
  dimindex(:'a) = 32 ⇒
  byte_align a + (3w:'a word) = a ∨
  byte_align a + (2w:'a word) = a ∨
  byte_align a + (1w:'a word) = a ∨
  byte_align a = a
``;
val _ = stmt "byte_align_32_CASES" byte_align_32_CASES_tm;
val _ = stmt_types "byte_align_32_CASES_types" byte_align_32_CASES_tm;
val MOD8_CASES_tm = ``
  ∀n. n MOD 8 = 0 ∨ n MOD 8 = 1 ∨ n MOD 8 = 2 ∨ n MOD 8 = 3 ∨
      n MOD 8 = 4 ∨ n MOD 8 = 5 ∨ n MOD 8 = 6 ∨ n MOD 8 = 7
``;
val _ = stmt "MOD8_CASES" MOD8_CASES_tm;
val _ = stmt_types "MOD8_CASES_types" MOD8_CASES_tm;
val byte_align_64_CASES_tm = ``
  dimindex(:'a) = 64 ⇒
  byte_align a + (7w:'a word) = a ∨
  byte_align a + (6w:'a word) = a ∨
  byte_align a + (5w:'a word) = a ∨
  byte_align a + (4w:'a word) = a ∨
  byte_align a + (3w:'a word) = a ∨
  byte_align a + (2w:'a word) = a ∨
  byte_align a + (1w:'a word) = a ∨
  byte_align a = a
``;
val _ = stmt "byte_align_64_CASES" byte_align_64_CASES_tm;
val _ = stmt_types "byte_align_64_CASES_types" byte_align_64_CASES_tm;
val byte_align_64_IMP_tm = ``
  dimindex(:'a) = 64 ⇒
  (byte_align a + (7w:'a word) = a ⇒ w2n a MOD 8 = 7) ∧
  (byte_align a + (6w:'a word) = a ⇒ w2n a MOD 8 = 6) ∧
  (byte_align a + (5w:'a word) = a ⇒ w2n a MOD 8 = 5) ∧
  (byte_align a + (4w:'a word) = a ⇒ w2n a MOD 8 = 4) ∧
  (byte_align a + (3w:'a word) = a ⇒ w2n a MOD 8 = 3) ∧
  (byte_align a + (2w:'a word) = a ⇒ w2n a MOD 8 = 2) ∧
  (byte_align a + (1w:'a word) = a ⇒ w2n a MOD 8 = 1) ∧
  (byte_align a = a ⇒ w2n a MOD 8 = 0)
``;
val _ = stmt "byte_align_64_IMP" byte_align_64_IMP_tm;
val _ = stmt_types "byte_align_64_IMP_types" byte_align_64_IMP_tm;
val align2_not_align3_4w_tm = ``
  ¬ aligned 3 x ∧ aligned 2 (x:'a word) ∧ dimindex (:'a) = 64 ⇒
  x = byte_align x + 4w ∧
  x + 1w = byte_align x + 5w ∧
  x + 2w = byte_align x + 6w ∧
  x + 3w = byte_align x + 7w
``;
val _ = stmt "align2_not_align3_4w" align2_not_align3_4w_tm;
val _ = stmt_types "align2_not_align3_4w_types" align2_not_align3_4w_tm;
val arith_upd_lemma_tm = ``
  (∀r. word_loc_val p labs (read_reg r s1) = SOME (t1.regs r)) ∧ ¬(arith_upd a s1).failed ⇒
   ∀r. word_loc_val p labs (read_reg r (arith_upd a s1)) =
       SOME ((arith_upd a t1).regs r)
``;
val _ = stmt "arith_upd_lemma" arith_upd_lemma_tm;
val _ = stmt_types "arith_upd_lemma_types" arith_upd_lemma_tm;
val arith_upd_fp_regs_tm = ``
    ((arith_upd a s).fp_regs = s.fp_regs ∧
  (arith_upd a (t:'a asm_state)).fp_regs = t.fp_regs)
``;
val _ = stmt "arith_upd_fp_regs" arith_upd_fp_regs_tm;
val _ = stmt_types "arith_upd_fp_regs_types" arith_upd_fp_regs_tm;
val fp_upd_lemma_tm = ``
  (∀r. word_loc_val p labs (read_reg r s1) = SOME (t1.regs r)) ∧
  (!r. s1.fp_regs r = t1.fp_regs r) /\
   ¬(fp_upd f s1).failed ⇒
  (∀r. (fp_upd f s1).fp_regs r = (fp_upd f t1).fp_regs r) ∧
  ∀r.
    word_loc_val p labs (read_reg r (fp_upd f s1)) =
    SOME ((fp_upd f t1).regs r)
``;
val _ = stmt "fp_upd_lemma" fp_upd_lemma_tm;
val _ = stmt_types "fp_upd_lemma_types" fp_upd_lemma_tm;
val Inst_share_mem_pc_update_helper_tm = ``
  share_mem_state_rel mc_conf s1 t1 ms1 /\
  target_state_rel mc_conf.target (t1 with pc := pc') ms2 ==>
  share_mem_state_rel mc_conf (s1 with <|pc := s1.pc + 1; clock := s1.clock − 1|>)
    (t1 with pc := pc') ms2
``;
val _ = stmt "Inst_share_mem_pc_update_helper" Inst_share_mem_pc_update_helper_tm;
val _ = stmt_types "Inst_share_mem_pc_update_helper_types" Inst_share_mem_pc_update_helper_tm;
val Inst_share_mem_reg_update_helper_tm = ``
  share_mem_state_rel mc_conf s1 t1 ms1 /\
  target_state_rel mc_conf.target
    (t1 with <| regs := (n =+ c) t1.regs; pc := pc'|>) ms2 ==>
  share_mem_state_rel mc_conf (s1 with
    <| regs := (n =+ Word c) s1.regs; pc := s1.pc + 1; clock := s1.clock − 1|>)
    (t1 with <|regs := (n =+ c) t1.regs; pc := pc'|>) ms2
``;
val _ = stmt "Inst_share_mem_reg_update_helper" Inst_share_mem_reg_update_helper_tm;
val _ = stmt_types "Inst_share_mem_reg_update_helper_types" Inst_share_mem_reg_update_helper_tm;
val arith_upd_share_mem_domain_unchange_tm = ``
  (arith_upd a s1).shared_mem_domain = s1.shared_mem_domain
``;
val _ = stmt "arith_upd_share_mem_domain_unchange" arith_upd_share_mem_domain_unchange_tm;
val _ = stmt_types "arith_upd_share_mem_domain_unchange_types" arith_upd_share_mem_domain_unchange_tm;
val fp_upd_share_mem_domain_unchange_tm = ``
  (fp_upd f s1).shared_mem_domain = s1.shared_mem_domain
``;
val _ = stmt "fp_upd_share_mem_domain_unchange" fp_upd_share_mem_domain_unchange_tm;
val _ = stmt_types "fp_upd_share_mem_domain_unchange_types" fp_upd_share_mem_domain_unchange_tm;
val _ = OS.Process.exit OS.Process.success;
