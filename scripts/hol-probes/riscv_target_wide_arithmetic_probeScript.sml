(* Replay unchanged original high-product and bounded rotate proofs. *)
load "preamble"; load "riscv_targetTheory"; load "wordsLib"; load "fcpLib";
open HolKernel Parse bossLib preamble riscv_targetTheory;
val _ = Globals.linewidth := 1000000;

val mul_long = prove (``!a : word64 b : word64.
    n2w ((w2n a * w2n b) DIV 18446744073709551616) =
    (127 >< 64) (w2w a * w2w b : word128) : word64``,
Cases
  \\ Cases
  \\ fs [wordsTheory.w2w_n2w, wordsTheory.word_mul_n2w,
         wordsTheory.word_extract_n2w, bitTheory.BITS_THM]);
val _ = (print "wide_mul_long_statement="; print_term (concl (GEN_ALL mul_long)); print "\n");
val _ = print ("wide_mul_long_types=" ^
  String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v))
    (#1 (strip_forall (concl (GEN_ALL mul_long))))) ^ "\n");
val _ = print ("wide_mul_long_hypotheses=" ^ Int.toString (length (hyp mul_long)) ^ "\n");
val _ = (print "wide_mul_long_proved="; print_term (rhs (concl (EQT_INTRO (GEN_ALL mul_long)))); print "\n");
val product = rand (rhs (#2 (strip_forall (concl mul_long))));
val _ = print ("wide_product_type=" ^ type_to_string (type_of product) ^ "\n");
val _ = print ("wide_slice_type=" ^ type_to_string (type_of (rhs (#2 (strip_forall (concl mul_long))))) ^ "\n");

val ror = prove (``!w : word64 n. n < 64n ==> ((w << (64 - n) || w >>> n) = w #>> n)``,
srw_tac [fcpLib.FCP_ss]
    [wordsTheory.word_or_def, wordsTheory.word_ror, wordsTheory.word_bits_def,
     wordsTheory.word_lsl_def, wordsTheory.word_lsr_def,
     GSYM arithmeticTheory.NOT_LESS]
  \\ `i - (64 - n) < 64` by decide_tac
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] []
  \\ Cases_on `i + n < 64`
  \\ simp []);
val _ = (print "wide_ror_statement="; print_term (concl (GEN_ALL ror)); print "\n");
val _ = print ("wide_ror_types=" ^
  String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v))
    (#1 (strip_forall (concl (GEN_ALL ror))))) ^ "\n");
val _ = print ("wide_ror_hypotheses=" ^ Int.toString (length (hyp ror)) ^ "\n");
val _ = (print "wide_ror_proved="; print_term (rhs (concl (EQT_INTRO (GEN_ALL ror)))); print "\n");
val _ = OS.Process.exit OS.Process.success;
