load "preamble";
load "blastLib";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble wordsTheory stack_removeProofTheory stack_removeTheory stackSemTheory stackPropsTheory stackLangTheory set_sepTheory;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val word_shift_def = backend_commonTheory.word_shift_def;
val _ = Globals.linewidth := 20000;
val wa_inverse = GEN_ALL (prove(``   good_dimindex(:'a) ∧ w2n (bytes_in_word:'a word) * w2n n < dimword(:'a) ⇒
   (bytes_in_word:'a word * n) >>> word_shift (:'a) = n``,
  EVAL_TAC \\ srw_tac[][] \\ pop_assum mp_tac
  \\ blastLib.BBLAST_TAC \\ simp[]
  \\ blastLib.BBLAST_TAC \\ srw_tac[][]
  \\ match_mp_tac lsl_lsr
  \\ simp[]
  \\ Cases_on`n`\\full_simp_tac(srw_ss())[word_lsl_n2w]
  \\ full_simp_tac(srw_ss())[dimword_def]));
val _ = print("wa_inverse_statement=" ^ term_to_string(concl wa_inverse) ^ "\n");
val _ = print("wa_inverse_proved=" ^ term_to_string(rhs(concl(EQT_INTRO wa_inverse))) ^ "\n");
val wa_offset = GEN_ALL (prove(``   word_offset n = bytes_in_word * n2w n``,
  full_simp_tac(srw_ss())[word_offset_def,word_mul_n2w,bytes_in_word_def]));
val _ = print("wa_offset_statement=" ^ term_to_string(concl wa_offset) ^ "\n");
val _ = print("wa_offset_proved=" ^ term_to_string(rhs(concl(EQT_INTRO wa_offset))) ^ "\n");
val wa_forward = GEN_ALL (prove(``   good_dimindex (:'a) ==>
    w ≪ word_shift (:α) = w * bytes_in_word:'a word``,
  srw_tac[][WORD_MUL_LSL,word_shift_def,bytes_in_word_def,
      good_dimindex_def]));
val _ = print("wa_forward_statement=" ^ term_to_string(concl wa_forward) ^ "\n");
val _ = print("wa_forward_proved=" ^ term_to_string(rhs(concl(EQT_INTRO wa_forward))) ^ "\n");
