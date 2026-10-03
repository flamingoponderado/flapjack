load "preamble"; load "stack_rawcallProofTheory";
open HolKernel Parse bossLib preamble stack_rawcallProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "jumplower_full_statement="; print_term(concl comp_correct));
val _ = print("jumplower_full_hypotheses=" ^ Int.toString(length(hyp comp_correct)) ^ "\n");
val _ = (print "jumplower_case_statement="; print_term(concl(ISPEC ``stackLang$JumpLower jumpR1 jumpR2 jumpDest:64 stackLang$prog`` comp_correct)));

(* Original evaluate_ind has already been rewritten by fix_clock_evaluate
at stackSemScript1111. Its body post-state therefore matches the actual run. *)
val (_, induction_body) = strip_forall (concl stackSemTheory.evaluate_ind);
val (obligations, _) = dest_imp induction_body;
fun is_jumplower_obligation tm =
  let val (_, body) = strip_forall tm;
      val (_, conclusion) = strip_imp body;
      val (_, args) = strip_comb conclusion;
      val (program, _) = pairSyntax.dest_pair (hd args);
      val (constructor, _) = strip_comb program;
      val {Thy,Name,...} = dest_thy_const constructor
  in Thy = "stackLang" andalso Name = "JumpLower" end
  handle HOL_ERR _ => false;
val jumplower_obligations = List.filter is_jumplower_obligation (strip_conj obligations);
val _ = if length jumplower_obligations = 1 then () else raise Fail "expected one original JumpLower induction obligation";
val _ = if null(hyp stackSemTheory.evaluate_ind) then () else raise Fail "open induction theorem";
val _ = (print "jumplower_evaluate_ind_obligation="; print_term(hd jumplower_obligations));

fun row label tm = (print(label ^ "="); print_term(rhs(concl(EVAL tm))));
val _ = row "jumplower_unsigned_1" ``asm$word_cmp asm$Lower (0w:word1) 1w``;
val _ = row "jumplower_unsigned_2" ``asm$word_cmp asm$Lower (1w:word1) 0w``;
val _ = row "jumplower_unsigned_3" ``asm$word_cmp asm$Lower (255w:word8) 1w``;
val _ = row "jumplower_unsigned_4" ``asm$word_cmp asm$Lower (0w:word64) (n2w (2 ** 63))``;
val _ = row "jumplower_unsigned_5" ``asm$word_cmp asm$Lower (n2w (2 ** 63):word64) 0w``;
val _ = row "jumplower_unsigned_6" ``asm$word_cmp asm$Lower (0w:80 word) (n2w (2 ** 79))``;
