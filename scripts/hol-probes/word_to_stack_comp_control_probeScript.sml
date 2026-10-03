load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory word_to_stackTheory
  wordSemTheory stackSemTheory wordLangTheory stackLangTheory wordConvsTheory
  miscTheory sptreeTheory finite_mapTheory;
val _ = Globals.linewidth := 1000000;
val th = GEN_ALL(prove(``∀(s:('a,num # 'c,'ffi)wordSem$state).
∀k f f' res s1 t bs n bs' n' sprog lens.
     (wordSem$evaluate (wordLang$Skip,s) = (res,s1)) /\ res <> SOME Error /\
     state_rel ac k f f' s t lens 0 /\
     post_alloc_conventions k wordLang$Skip /\
     flat_exp_conventions wordLang$Skip /\
     comp ac F wordLang$Skip (bs,n) (k,f,f') = (sprog, (bs',n')) /\
     LENGTH (append bs) ≤ n ∧ n - LENGTH (append bs) ≤ LENGTH t.bitmaps ∧
     isPREFIX (append bs') (DROP (n - LENGTH (append bs)) t.bitmaps) ∧
     get_labels sprog SUBSET loc_check t.code /\
     max_var wordLang$Skip < 2 * f' + 2 * k ==>
     ?ck t1:('a,'c,'ffi) stackSem$state res1.
       (stackSem$evaluate (sprog,t with clock := t.clock + ck) = (res1,t1)) /\
       if OPTION_MAP compile_result res <> res1
       then res1 = SOME (Halt (Word 2w)) /\
            t1.ffi.io_events ≼ s1.ffi.io_events /\
            the (s1.stack_limit + 1) s1.stack_max > s1.stack_limit
       else
         case res of
         | NONE => state_rel ac k f f' s1 t1 lens 0
         | SOME (Result _ ys) =>
            state_rel ac k 0 0 s1 t1 lens (LENGTH ys - (k - 1)) /\
            (∀i. i < LENGTH ys ==> (if i + 1 < k then
              (FLOOKUP t1.regs (i+1) = SOME (EL i ys)) else
            (LLOOKUP (DROP t1.stack_space t1.stack) (LENGTH ys - (i + 1)) = SOME (EL i ys))))
         | SOME (Exception _ y) =>
           ∃l0 l.
           state_rel ac k 0 0 (push_locals l0 l s1) t1 (LASTN (s.handler+1) lens) 0 /\
           s1.locals = union (fromAList l) (fromAList l0) ∧
           FLOOKUP t1.regs 1 = SOME y
         | SOME (Break _) => state_rel ac k f f' s1 t1 lens 0
         | SOME (Continue _) => state_rel ac k f f' s1 t1 lens 0
         | SOME _ => s1.ffi = t1.ffi /\ s1.clock = t1.clock``,
REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  qexists_tac `0` \\
  fs[comp_def] \\ rw[] \\
  fs [wordSemTheory.evaluate_def,
                         stackSemTheory.evaluate_def,comp_def] \\ rw []));
val _ = if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail "open case";
val _ = (print "comp_correct_skip_statement="; print_term(concl th));
val _ = print("comp_correct_skip_proved=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n");
val _ = print("comp_correct_skip_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val th = GEN_ALL(prove(``∀(s:('a,num # 'c,'ffi)wordSem$state).
∀k f f' res s1 t bs n bs' n' sprog lens.
     (wordSem$evaluate ((wordLang$Break label),s) = (res,s1)) /\ res <> SOME Error /\
     state_rel ac k f f' s t lens 0 /\
     post_alloc_conventions k (wordLang$Break label) /\
     flat_exp_conventions (wordLang$Break label) /\
     comp ac F (wordLang$Break label) (bs,n) (k,f,f') = (sprog, (bs',n')) /\
     LENGTH (append bs) ≤ n ∧ n - LENGTH (append bs) ≤ LENGTH t.bitmaps ∧
     isPREFIX (append bs') (DROP (n - LENGTH (append bs)) t.bitmaps) ∧
     get_labels sprog SUBSET loc_check t.code /\
     max_var (wordLang$Break label) < 2 * f' + 2 * k ==>
     ?ck t1:('a,'c,'ffi) stackSem$state res1.
       (stackSem$evaluate (sprog,t with clock := t.clock + ck) = (res1,t1)) /\
       if OPTION_MAP compile_result res <> res1
       then res1 = SOME (Halt (Word 2w)) /\
            t1.ffi.io_events ≼ s1.ffi.io_events /\
            the (s1.stack_limit + 1) s1.stack_max > s1.stack_limit
       else
         case res of
         | NONE => state_rel ac k f f' s1 t1 lens 0
         | SOME (Result _ ys) =>
            state_rel ac k 0 0 s1 t1 lens (LENGTH ys - (k - 1)) /\
            (∀i. i < LENGTH ys ==> (if i + 1 < k then
              (FLOOKUP t1.regs (i+1) = SOME (EL i ys)) else
            (LLOOKUP (DROP t1.stack_space t1.stack) (LENGTH ys - (i + 1)) = SOME (EL i ys))))
         | SOME (Exception _ y) =>
           ∃l0 l.
           state_rel ac k 0 0 (push_locals l0 l s1) t1 (LASTN (s.handler+1) lens) 0 /\
           s1.locals = union (fromAList l) (fromAList l0) ∧
           FLOOKUP t1.regs 1 = SOME y
         | SOME (Break _) => state_rel ac k f f' s1 t1 lens 0
         | SOME (Continue _) => state_rel ac k f f' s1 t1 lens 0
         | SOME _ => s1.ffi = t1.ffi /\ s1.clock = t1.clock``,
REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs [wordSemTheory.evaluate_def,comp_def] \\ rveq \\
  qexists_tac `0` \\
  simp [stackSemTheory.evaluate_def]));
val _ = if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail "open case";
val _ = (print "comp_correct_break_statement="; print_term(concl th));
val _ = print("comp_correct_break_proved=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n");
val _ = print("comp_correct_break_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val th = GEN_ALL(prove(``∀(s:('a,num # 'c,'ffi)wordSem$state).
∀k f f' res s1 t bs n bs' n' sprog lens.
     (wordSem$evaluate ((wordLang$Continue label),s) = (res,s1)) /\ res <> SOME Error /\
     state_rel ac k f f' s t lens 0 /\
     post_alloc_conventions k (wordLang$Continue label) /\
     flat_exp_conventions (wordLang$Continue label) /\
     comp ac F (wordLang$Continue label) (bs,n) (k,f,f') = (sprog, (bs',n')) /\
     LENGTH (append bs) ≤ n ∧ n - LENGTH (append bs) ≤ LENGTH t.bitmaps ∧
     isPREFIX (append bs') (DROP (n - LENGTH (append bs)) t.bitmaps) ∧
     get_labels sprog SUBSET loc_check t.code /\
     max_var (wordLang$Continue label) < 2 * f' + 2 * k ==>
     ?ck t1:('a,'c,'ffi) stackSem$state res1.
       (stackSem$evaluate (sprog,t with clock := t.clock + ck) = (res1,t1)) /\
       if OPTION_MAP compile_result res <> res1
       then res1 = SOME (Halt (Word 2w)) /\
            t1.ffi.io_events ≼ s1.ffi.io_events /\
            the (s1.stack_limit + 1) s1.stack_max > s1.stack_limit
       else
         case res of
         | NONE => state_rel ac k f f' s1 t1 lens 0
         | SOME (Result _ ys) =>
            state_rel ac k 0 0 s1 t1 lens (LENGTH ys - (k - 1)) /\
            (∀i. i < LENGTH ys ==> (if i + 1 < k then
              (FLOOKUP t1.regs (i+1) = SOME (EL i ys)) else
            (LLOOKUP (DROP t1.stack_space t1.stack) (LENGTH ys - (i + 1)) = SOME (EL i ys))))
         | SOME (Exception _ y) =>
           ∃l0 l.
           state_rel ac k 0 0 (push_locals l0 l s1) t1 (LASTN (s.handler+1) lens) 0 /\
           s1.locals = union (fromAList l) (fromAList l0) ∧
           FLOOKUP t1.regs 1 = SOME y
         | SOME (Break _) => state_rel ac k f f' s1 t1 lens 0
         | SOME (Continue _) => state_rel ac k f f' s1 t1 lens 0
         | SOME _ => s1.ffi = t1.ffi /\ s1.clock = t1.clock``,
REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs [wordSemTheory.evaluate_def,comp_def] \\ rveq \\
  qexists_tac `0` \\
  simp [stackSemTheory.evaluate_def]));
val _ = if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail "open case";
val _ = (print "comp_correct_continue_statement="; print_term(concl th));
val _ = print("comp_correct_continue_proved=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n");
val _ = print("comp_correct_continue_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
