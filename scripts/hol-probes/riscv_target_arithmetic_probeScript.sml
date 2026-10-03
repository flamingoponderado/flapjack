(* Replay unchanged original local arithmetic proofs; not selected fixtures. *)
load "preamble"; load "riscv_targetTheory"; load "blastLib";
open HolKernel Parse bossLib preamble riscv_targetTheory;
val _ = Globals.linewidth := 1000000;

val lem5 = prove (``aligned 2 (c: word64) ==> ~c ' 1``,
simp [alignmentTheory.aligned_extract]
  \\ blastLib.BBLAST_TAC);
val _ = (print "arithmetic_lem5_statement="; print_term (concl (GEN_ALL lem5)); print "\n");
val _ = print ("arithmetic_lem5_types=" ^
  String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v))
    (#1 (strip_forall (concl (GEN_ALL lem5))))) ^ "\n");
val _ = print ("arithmetic_lem5_hypotheses=" ^ Int.toString (length (hyp lem5)) ^ "\n");
val _ = (print "arithmetic_lem5_proved="; print_term (rhs (concl (EQT_INTRO (GEN_ALL lem5)))); print "\n");

val lem8 = prove (``((if b then 1w else 0w : word64) = (v2w [x] || v2w [y])) = (b = (x \/ y))``,
rw [] \\ blastLib.BBLAST_TAC);
val _ = (print "arithmetic_lem8_statement="; print_term (concl (GEN_ALL lem8)); print "\n");
val _ = print ("arithmetic_lem8_types=" ^
  String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v))
    (#1 (strip_forall (concl (GEN_ALL lem8))))) ^ "\n");
val _ = print ("arithmetic_lem8_hypotheses=" ^ Int.toString (length (hyp lem8)) ^ "\n");
val _ = (print "arithmetic_lem8_proved="; print_term (rhs (concl (EQT_INTRO (GEN_ALL lem8)))); print "\n");

val lem9 = prove (``!r2 : word64 r3 : word64.
    (18446744073709551616 <= w2n r2 + (w2n r3 + 1) <=>
     18446744073709551616w <=+ w2w r2 + w2w r3 + 1w : 65 word) /\
    (18446744073709551616 <= w2n r2 + w2n r3 <=>
     18446744073709551616w <=+ w2w r2 + w2w r3 : 65 word)``,
Cases
   \\ Cases
   \\ imp_res_tac wordsTheory.BITS_ZEROL_DIMINDEX
   \\ fs [wordsTheory.w2w_n2w, wordsTheory.word_add_n2w,
          wordsTheory.word_ls_n2w]);
val _ = (print "arithmetic_lem9_statement="; print_term (concl (GEN_ALL lem9)); print "\n");
val _ = print ("arithmetic_lem9_types=" ^
  String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v))
    (#1 (strip_forall (concl (GEN_ALL lem9))))) ^ "\n");
val _ = print ("arithmetic_lem9_sum_type=" ^ type_to_string
  (type_of (rand (rhs (#1 (dest_conj (#2 (strip_forall (concl lem9)))))))) ^ "\n");
val _ = print ("arithmetic_lem9_hypotheses=" ^ Int.toString (length (hyp lem9)) ^ "\n");
val _ = (print "arithmetic_lem9_proved="; print_term (rhs (concl (EQT_INTRO (GEN_ALL lem9)))); print "\n");
val _ = OS.Process.exit OS.Process.success;
