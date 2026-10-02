load "wordsTheory"; load "wordsLib"; load "blastLib";
open HolKernel Parse bossLib wordsTheory Tactical boolSyntax;
val _ = Globals.linewidth := 100000;
val _ = computeLib.add_funs [word_replicate_def];
fun out label q = let val th = if String.isSubstring "word_replicate 0" (term_to_string q) then
 prove(mk_eq(q, numSyntax.mk_numeral Arbnum.zero),
   op THEN (rw [word_replicate_def], blastLib.BBLAST_TAC))
 else wordsLib.WORD_EVAL_CONV q in
 if null(hyp th) then (print(label ^ "="); print_term(snd(boolSyntax.dest_eq(concl th))); print "\n")
 else raise Fail "undischarged assumptions" end;
val _ = out "replicate_0" ``w2n (word_replicate 0 (1w:1 word):1 word)``;
val _ = out "replicate_1" ``w2n (word_replicate 5 (1w:1 word):1 word)``;
val _ = out "replicate_2" ``w2n (word_replicate 1 (5w:3 word):7 word)``;
val _ = out "replicate_3" ``w2n (word_replicate 2 (5w:3 word):7 word)``;
val _ = out "replicate_4" ``w2n (word_replicate 3 (5w:3 word):7 word)``;
val _ = out "replicate_5" ``w2n (word_replicate 3 (5w:3 word):8 word)``;
val _ = out "replicate_6" ``w2n (word_replicate 2 (165w:8 word):16 word)``;
val _ = out "replicate_7" ``w2n (word_replicate 8 (165w:8 word):64 word)``;
val _ = out "replicate_8" ``w2n (word_replicate 10 (165w:8 word):80 word)``;
val _ = out "replicate_9" ``w2n (word_replicate 2 (65535w:16 word):80 word)``;
val _ = out "replicate_10" ``w2n (word_replicate 2 (4660w:16 word):8 word)``;
val _ = out "replicate_11" ``w2n (word_replicate 0 (7w:3 word):16 word)``;
val _ = out "replicate_12" ``w2n (word_replicate 1 (7w:3 word):16 word)``;
val _ = out "replicate_13" ``w2n (word_replicate 20 (5w:3 word):16 word)``;
val _ = out "replicate_14" ``w2n (word_replicate 8 (1w:1 word):8 word)``;
val _ = out "replicate_15" ``w2n (word_replicate 3 (1w:1 word):8 word)``;
