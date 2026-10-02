load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labPropsTheory labLangTheory labSemTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val _ = capture "enc_lines_again_simp_def" enc_lines_again_simp_def;
val _ = types "enc_lines_again_simp_def_types" enc_lines_again_simp_def;
val enc_lines_again_simp_EQ = prove (``∀labs ffis pos enc ls acc b.
  let (ls',flag) = enc_lines_again_simp labs ffis pos enc ls in
  enc_lines_again labs ffis pos enc ls (acc,b) = (REVERSE acc ++ ls',sec_length ls' pos,b ∧ flag)``,
  ho_match_mp_tac enc_lines_again_simp_ind >>
  fs[enc_lines_again_simp_def,enc_lines_again_def]>>rw[sec_length_def]>>
  rpt(pairarg_tac>>fs[])>>
  rw[EQ_IMP_THM,sec_length_def]);
val _ = capture "enc_lines_again_simp_EQ" enc_lines_again_simp_EQ;
val _ = types "enc_lines_again_simp_EQ_types" enc_lines_again_simp_EQ;
val enc_lines_again_simp_len = prove (``∀labs ffis pos enc lines res.
    enc_lines_again_simp labs ffis pos enc lines = (res,T) ⇒
    MAP line_len res = MAP line_len lines``,
  recInduct enc_lines_again_simp_ind
  \\ rw[enc_lines_again_simp_def]
  \\ pairarg_tac \\ fs[] \\ rveq \\ fs[]);
val _ = capture "enc_lines_again_simp_len" enc_lines_again_simp_len;
val _ = types "enc_lines_again_simp_len_types" enc_lines_again_simp_len;
val _ = (print "enc_lines_again_simp_signature="; print(type_to_string(type_of ``enc_lines_again_simp``)); print "\n");
val _ = show_types := false;
fun observe label q = (print(label ^ "=");print_term(rconc(EVAL q));print "\n");
val shrink = ``(λa:8 asm. case a of Jump w => if w = 0w then [0w;0w;0w;0w] else [1w;1w] | _ => [99w;99w]) : 8 asm -> word8 list``;
val grow = ``(λa:8 asm. case a of Jump w => if w = 0w then [0w] else [1w;1w;1w] | _ => [99w;99w]) : 8 asm -> word8 list``;
val labs = ``insert 3 (insert 4 10 LN) LN : num num_map num_map``;
val sl = ``[LabAsm (Jump (Lab 3 4)) 0w [0w;0w;0w;0w] 4] : 8 labLang$line list``;
val gl = ``[LabAsm (Jump (Lab 3 4)) 0w [0w] 1] : 8 labLang$line list``;
val acc = ``[Label 1 7 99] : 8 labLang$line list``;
val strange = ``[Label 99 0 5; Asm (Asmi (Inst Skip)) [] 77;Label 2 1 0] : 8 labLang$line list``;
val _ = observe "empty_full" ``enc_lines_again_simp ^labs [] 13 ^grow [] = ([],T)``;
val _ = observe "shrink_full" ``enc_lines_again_simp ^labs [] 0 ^shrink ^sl = ([LabAsm (Jump (Lab 3 4)) 10w [1w;1w] 4],T)``;
val _ = observe "grow_full" ``enc_lines_again_simp ^labs [] 0 ^grow ^gl = ([LabAsm (Jump (Lab 3 4)) 10w [1w;1w;1w] 3],F)``;
val _ = observe "equal_word_full" ``enc_lines_again_simp ^labs [] 0 ^grow [LabAsm (Jump (Lab 3 4)) 10w [1w;1w;1w] 3] = ([LabAsm (Jump (Lab 3 4)) 10w [1w;1w;1w] 3],T)``;
val _ = observe "shrink_acc_true" ``enc_lines_again ^labs [] 0 ^shrink ^sl (^acc,T) = ([Label 1 7 99;LabAsm (Jump (Lab 3 4)) 10w [1w;1w] 4],(4,T))``;
val _ = observe "shrink_acc_false" ``enc_lines_again ^labs [] 0 ^shrink ^sl (^acc,F) = ([Label 1 7 99;LabAsm (Jump (Lab 3 4)) 10w [1w;1w] 4],(4,F))``;
val _ = observe "grow_acc_true" ``enc_lines_again ^labs [] 0 ^grow ^gl (^acc,T) = ([Label 1 7 99;LabAsm (Jump (Lab 3 4)) 10w [1w;1w;1w] 3],(3,F))``;
val _ = observe "shrink_lengths" ``MAP line_len (FST(enc_lines_again_simp ^labs [] 0 ^shrink ^sl)) = MAP line_len ^sl``;
val _ = observe "grow_lengths_differ" ``MAP line_len (FST(enc_lines_again_simp ^labs [] 0 ^grow ^gl)) <> MAP line_len ^gl``;
val _ = observe "invalid_annotations_full" ``enc_lines_again_simp ^labs [] 3 ^grow ^strange = (^strange,T)``;
val _ = observe "invalid_acc_position_full" ``enc_lines_again ^labs [] 3 ^grow ^strange (^acc,F) = (REVERSE ^acc ++ ^strange,(85,F))``;
val _ = observe "shifted_full" ``enc_lines_again_simp ^labs [] 3 ^shrink ^sl = ([LabAsm (Jump (Lab 3 4)) 7w [1w;1w] 4],T)``;
val _ = observe "wrapped_word_full" ``enc_lines_again_simp ^labs [] 260 ^shrink ^sl = ([LabAsm (Jump (Lab 3 4)) 6w [1w;1w] 4],T)``;
val _ = observe "unbounded_position_full" ``enc_lines_again ^labs [] 260 ^shrink ^sl (^acc,T) = ([Label 1 7 99;LabAsm (Jump (Lab 3 4)) 6w [1w;1w] 4],(264,T))``;
