load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stack_removeTheory stackSemTheory;
val _ = Globals.linewidth := 20000;
val sp = GEN_ALL (prove(``state_rel jump off k s t ⇒
   ∃c:α word.
   get_var (k+1) t = SOME (Word c) ∧
   dimindex (:α) DIV 8 * max_stack_alloc ≤ w2n c ∧
   w2n c + w2n (bytes_in_word:'a word) * LENGTH s.stack < dimword (:'a) ∧
   get_var k t = SOME (Word (c + bytes_in_word * n2w s.stack_space)) ∧
   (memory s.memory s.mdomain *
     word_list
       (the_SOME_Word (FLOOKUP s.store BitmapBase) ≪ word_shift (:α))
       (MAP Word s.bitmaps ++ MAP Word s.data_buffer.buffer) *
     word_list_exists
       (the_SOME_Word (FLOOKUP s.store BitmapBase) ≪ word_shift (:α) +
        bytes_in_word *
        n2w (LENGTH s.data_buffer.buffer + LENGTH s.bitmaps))
       s.data_buffer.space_left * word_store c s.store *
     word_list c s.stack) (fun2set (t.memory,t.mdomain))``,
  rw[state_rel_def]
  \\ pop_assum mp_tac
  \\ CASE_TAC \\ fs[]
  \\ CASE_TAC \\ fs[]
  \\ simp[get_var_def]));
val _ = print("sp_statement=" ^ term_to_string(concl sp) ^ "\n");
val _ = print("sp_proved=" ^ term_to_string(rhs(concl(EQT_INTRO sp))) ^ "\n");
