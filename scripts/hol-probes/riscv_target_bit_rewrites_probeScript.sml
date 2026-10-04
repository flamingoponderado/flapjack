load "preamble"; load "riscv_targetProofTheory"; load "blastLib";
open HolKernel Parse bossLib preamble riscv_targetProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val word_bit_0_add4_replay = GEN_ALL (prove (``word_bit 0 (w +  4w:word64) = word_bit 0 w /\
    word_bit 0 (w +  8w:word64) = word_bit 0 w /\
    word_bit 0 (w + 12w:word64) = word_bit 0 w /\
    word_bit 0 (w + 16w:word64) = word_bit 0 w /\
    word_bit 0 (w + 20w:word64) = word_bit 0 w /\
    word_bit 0 (w + 24w:word64) = word_bit 0 w /\
    word_bit 0 (w + 28w:word64) = word_bit 0 w /\
    word_bit 0 (w + 32w:word64) = word_bit 0 w``, blastLib.BBLAST_TAC));
val _ = (print "word_bit_0_add4_statement="; print_term (concl word_bit_0_add4_replay); print "\n");
val _ = print ("word_bit_0_add4_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (#1 (strip_forall (concl word_bit_0_add4_replay)))) ^ "\n");
val _ = print ("word_bit_0_add4_hypotheses=" ^ Int.toString (length (hyp word_bit_0_add4_replay)) ^ "\n");
val _ = (print "word_bit_0_add4_proved="; print_term (rhs (concl (EQT_INTRO word_bit_0_add4_replay))); print "\n");
val word_bit_0_lemmas_replay = GEN_ALL (prove (``!w. ¬word_bit 0 (0xFFFFFFFFFFFFFFFEw && w:word64) /\
      word_bit 0 ((0xFFFFFFFFFFFFFFFEw && w:word64) + v) = word_bit 0 v``, blastLib.BBLAST_TAC));
val _ = (print "word_bit_0_lemmas_statement="; print_term (concl word_bit_0_lemmas_replay); print "\n");
val _ = print ("word_bit_0_lemmas_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (#1 (strip_forall (concl word_bit_0_lemmas_replay)))) ^ "\n");
val _ = print ("word_bit_0_lemmas_hypotheses=" ^ Int.toString (length (hyp word_bit_0_lemmas_replay)) ^ "\n");
val _ = (print "word_bit_0_lemmas_proved="; print_term (rhs (concl (EQT_INTRO word_bit_0_lemmas_replay))); print "\n");
val _ = OS.Process.exit OS.Process.success;
