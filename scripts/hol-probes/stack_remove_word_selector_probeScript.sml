load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory relationTheory;
val _ = Globals.linewidth := 20000;
val _ = print ("sw_type=" ^ type_to_string (type_of ``stack_removeProof$the_SOME_Word``) ^ "\n");
val _ = print ("sw_def=" ^ term_to_string (concl the_SOME_Word_def) ^ "\n");
val _ = print ("sw_primitive=" ^ term_to_string (concl the_SOME_Word_def_primitive) ^ "\n");
val wf = SELECT_RULE (prove (``?R:'a word_loc option -> 'a word_loc option -> bool. WF R``,
  qexists_tac `EMPTY_REL` >> simp [WF_EMPTY_REL]));
val full = MATCH_MP (MATCH_MP WFREC_COROLLARY the_SOME_Word_def_primitive) wf;
val _ = print ("sw_full=" ^ term_to_string (concl full) ^ "\n");
fun check label q = let val th = prove (q, simp [full,the_SOME_Word_def])
  in print (label ^ "=" ^ term_to_string (rhs (concl (EQT_INTRO th))) ^ "\n") end;
val _ = check "sw_word_generic" ``!w:'a word. the_SOME_Word (SOME (Word w)) = w``;
val _ = check "sw_none_generic" ``the_SOME_Word (NONE:'a word_loc option) = (ARB:'a word)``;
val _ = check "sw_loc_generic" ``!label offset. the_SOME_Word (SOME (Loc label offset):'a word_loc option) = (ARB:'a word)``;
val _ = check "sw_none_loc" ``!label offset. the_SOME_Word (SOME (Loc label offset):'a word_loc option) = the_SOME_Word NONE``;
val _ = check "sw_all_loc" ``!a b c d. the_SOME_Word (SOME (Loc a b):'a word_loc option) = the_SOME_Word (SOME (Loc c d))``;
val _ = check "sw_word1" ``the_SOME_Word (SOME (Word (1w:word1))) = 1w``;
val _ = check "sw_word8" ``the_SOME_Word (SOME (Word (255w:word8))) = 255w``;
val _ = check "sw_word64" ``the_SOME_Word (SOME (Word (0w:word64))) = 0w``;
val _ = check "sw_word80" ``the_SOME_Word (SOME (Word ((n2w (2 EXP 79)):80 word))) = n2w (2 EXP 79)``;
