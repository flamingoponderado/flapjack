(* Literal original full signed twelve-bit reconstruction proof. *)
load "preamble"; load "riscv_targetTheory"; load "blastLib";
open HolKernel Parse bossLib preamble riscv_targetTheory;
val _ = Globals.linewidth := 1000000;
val () = wordsLib.guess_lengths();
val lem4 = blastLib.BBLAST_PROVE
  ``0xFFFFFFFFFFFFF800w <= c /\ c <= 0x7FFw ==>
    (sw2sw
      (v2w [c ' 11; c ' 10; c ' 9; c ' 8; c ' 7; c ' 6; c ' 5;
            c ' 4; c ' 3; c ' 2; c ' 1; c ' 0] : word12) = c : word64)``;
val _ = (print "lem4_statement="; print_term (concl (GEN_ALL lem4)); print "\n");
val _ = print ("lem4_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (#1 (strip_forall (concl (GEN_ALL lem4))))) ^ "\n");
val _ = print ("lem4_hypotheses=" ^ Int.toString (length (hyp lem4)) ^ "\n");
val _ = (print "lem4_proved="; print_term (rhs (concl (EQT_INTRO (GEN_ALL lem4)))); print "\n");
val lem12b = blastLib.BBLAST_PROVE
  ``0xFFFFFFFF80000000w <= c /\ c <= 0x7FFFF7FFw /\
      ((1 >< 0) c = 0w : word64) ==>
      (sw2sw (((31 >< 12) (c + -1w * sw2sw ((11 >< 0) c)) : word20) @@
              (0w : word12)) +
       sw2sw ((11 >< 0) c && ~2w) = c : word64)``;
val _ = (print "lem12b_statement="; print_term (concl (GEN_ALL lem12b)); print "\n");
val _ = print ("lem12b_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (#1 (strip_forall (concl (GEN_ALL lem12b))))) ^ "\n");
val _ = print ("lem12b_hypotheses=" ^ Int.toString (length (hyp lem12b)) ^ "\n");
val _ = (print "lem12b_proved="; print_term (rhs (concl (EQT_INTRO (GEN_ALL lem12b)))); print "\n");
val _ = print ("lem12b_intermediate_types=" ^ String.concatWith "; " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (find_terms (fn v => wordsSyntax.is_word_extract v orelse wordsSyntax.is_sw2sw v orelse wordsSyntax.is_word_concat v) (concl lem12b))) ^ "\n");
val _ = OS.Process.exit OS.Process.success;
