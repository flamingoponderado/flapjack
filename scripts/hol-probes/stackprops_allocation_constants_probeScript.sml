load "bossLib";
load "preamble";
load "stackPropsTheory";
open bossLib HolKernel Parse preamble stackPropsTheory stackSemTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun captureTypes label th = (print(label ^ "="); app (fn v =>
 print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";"))
 (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val alloc_const_source = prove (``alloc w s = (r,t) ⇒ t.ffi = s.ffi ∧
    t.clock = s.clock ∧
    t.use_alloc = s.use_alloc ∧
    t.use_store = s.use_store ∧
    t.use_stack = s.use_stack ∧
    t.code = s.code ∧
    t.be = s.be ∧
    t.gc_fun = s.gc_fun ∧
    t.mdomain = s.mdomain ∧
    t.sh_mdomain = s.sh_mdomain ∧
    t.bitmaps = s.bitmaps ∧
    t.compile = s.compile ∧
    t.data_buffer = s.data_buffer ∧
    t.code_buffer = s.code_buffer ∧
    t.compile_oracle = s.compile_oracle``,
  srw_tac[][alloc_def,gc_def,LET_THM] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]);
val _ = capture "alloc_const" alloc_const_source;
val _ = captureTypes "alloc_const_types" alloc_const_source;
val store_const_sem_const_source = prove (``store_const_sem t1 t2 s = (r,t) ⇒ t.ffi = s.ffi ∧
    t.clock = s.clock ∧
    t.use_alloc = s.use_alloc ∧
    t.use_store = s.use_store ∧
    t.use_stack = s.use_stack ∧
    t.code = s.code ∧
    t.be = s.be ∧
    t.gc_fun = s.gc_fun ∧
    t.mdomain = s.mdomain ∧
    t.sh_mdomain = s.sh_mdomain ∧
    t.bitmaps = s.bitmaps ∧
    t.compile = s.compile ∧
    t.store = s.store ∧
    t.data_buffer = s.data_buffer ∧
    t.code_buffer = s.code_buffer ∧
    t.compile_oracle = s.compile_oracle``,
  gvs[store_const_sem_def,gc_def,LET_THM,AllCaseEqs()]
  \\ rw [] \\ gvs [unset_var_def,set_var_def]);
val _ = capture "store_const_sem_const" store_const_sem_const_source;
val _ = captureTypes "store_const_sem_const_types" store_const_sem_const_source;
val gc_with_const_source = prove (``gc (x with clock := k) = OPTION_MAP (λs. s with clock := k) (gc x)``,
   srw_tac[][gc_def] >> every_case_tac >> full_simp_tac(srw_ss())[]);
val _ = capture "gc_with_const" gc_with_const_source;
val _ = captureTypes "gc_with_const_types" gc_with_const_source;
val alloc_with_const_source = prove (``alloc x (y with clock := z) = (I ## (λs. s with clock := z))(alloc x y)``,
  srw_tac[][alloc_def] >> every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]);
val _ = capture "alloc_with_const" alloc_with_const_source;
val _ = captureTypes "alloc_with_const_types" alloc_with_const_source;
val store_const_sem_with_const_source = prove (``store_const_sem t1 t2 (y with clock := z) =
   (I ## (λs. s with clock := z))(store_const_sem t1 t2 y)``,
  srw_tac[][store_const_sem_def,get_var_def] >> every_case_tac >>
  fs [unset_var_def,set_var_def]);
val _ = capture "store_const_sem_with_const" store_const_sem_with_const_source;
val _ = captureTypes "store_const_sem_with_const_types" store_const_sem_with_const_source;
val _ = capture "store_const_sem_def" (DB.fetch "stackSem" "store_const_sem_def");
val _ = captureTypes "store_const_sem_def_types" (DB.fetch "stackSem" "store_const_sem_def");
val _ = show_types := false;
fun observe label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
fun checked label q tac = let val th=prove(q,tac) in
 if null(hyp th) andalso aconv (concl th) q then print(label ^ "=T\n")
 else raise Fail "proof has hypotheses or changed conclusion" end;
val s8 = ``s:(8,'c,'ffi) stackSem$state``;
val allocation = ``^s8 with <| stack := [Word 0w]; stack_space := 0; bitmaps := [];
 regs := FEMPTY |+ (9,Word 2w); memory := (λa. Word 0w); mdomain := UNIV;
 store := FEMPTY |+ (AllocSize,Word 4w) |+ (NextFree,Word 5w) |+ (TriggerGC,Word 20w);
 gc_fun := (λ(wl,m,d,st). SOME(wl,m,st)) |>``;
val s64 = ``s:(64,'c,'ffi) stackSem$state``;
val copy = ``^s64 with <| regs := FEMPTY |+ (0,Word 0xAAw) |+ (1,Word 0w) |+ (2,Word 0x100w) |+ (3,Word 0x10w) |+ (4,Word 0xDEADw) |+ (5,Word 0xBEEFw); memory := (λa. Word 0w); mdomain := UNIV; bitmaps := [3w;0x55w]; use_alloc := T |>``;
fun alloc_frame label q state = checked label
 ``let (res,t)=^q in t.ffi = (^state).ffi /\ t.clock = (^state).clock /\ t.use_alloc = (^state).use_alloc /\ t.use_store = (^state).use_store /\ t.use_stack = (^state).use_stack /\ t.code = (^state).code /\ t.be = (^state).be /\ t.gc_fun = (^state).gc_fun /\ t.mdomain = (^state).mdomain /\ t.sh_mdomain = (^state).sh_mdomain /\ t.bitmaps = (^state).bitmaps /\ t.compile = (^state).compile /\ t.data_buffer = (^state).data_buffer /\ t.code_buffer = (^state).code_buffer /\ t.compile_oracle = (^state).compile_oracle``
 (Cases_on `^q` >> imp_res_tac alloc_const_source >> fs[]);
fun store_frame label q state = checked label
 ``let (res,t)=^q in t.ffi = (^state).ffi /\ t.clock = (^state).clock /\ t.use_alloc = (^state).use_alloc /\ t.use_store = (^state).use_store /\ t.use_stack = (^state).use_stack /\ t.code = (^state).code /\ t.be = (^state).be /\ t.gc_fun = (^state).gc_fun /\ t.mdomain = (^state).mdomain /\ t.sh_mdomain = (^state).sh_mdomain /\ t.bitmaps = (^state).bitmaps /\ t.compile = (^state).compile /\ t.store = (^state).store /\ t.data_buffer = (^state).data_buffer /\ t.code_buffer = (^state).code_buffer /\ t.compile_oracle = (^state).compile_oracle``
 (Cases_on `^q` >> imp_res_tac store_const_sem_const_source >> fs[]);
val alloc_success_state = allocation;
val _ = alloc_frame "alloc_success_frame" ``stackSem$alloc 10w ^alloc_success_state`` alloc_success_state;
val _ = checked "alloc_success_clock" ``stackSem$alloc 10w (^alloc_success_state with clock := 37) = (I ## (λt. t with clock := 37)) (stackSem$alloc 10w ^alloc_success_state)`` (simp[alloc_with_const_source]);
val _ = observe "alloc_success_outcome" ``case FST(stackSem$alloc 10w ^alloc_success_state) of NONE => 0 | SOME Error => 1 | SOME(Halt _) => 2 | _ => 3``;
val alloc_halt_state = allocation;
val _ = alloc_frame "alloc_halt_frame" ``stackSem$alloc 16w ^alloc_halt_state`` alloc_halt_state;
val _ = checked "alloc_halt_clock" ``stackSem$alloc 16w (^alloc_halt_state with clock := 37) = (I ## (λt. t with clock := 37)) (stackSem$alloc 16w ^alloc_halt_state)`` (simp[alloc_with_const_source]);
val _ = observe "alloc_halt_outcome" ``case FST(stackSem$alloc 16w ^alloc_halt_state) of NONE => 0 | SOME Error => 1 | SOME(Halt _) => 2 | _ => 3``;
val alloc_gc_failure_state = ``^allocation with gc_fun := (λx. NONE)``;
val _ = alloc_frame "alloc_gc_failure_frame" ``stackSem$alloc 10w ^alloc_gc_failure_state`` alloc_gc_failure_state;
val _ = checked "alloc_gc_failure_clock" ``stackSem$alloc 10w (^alloc_gc_failure_state with clock := 37) = (I ## (λt. t with clock := 37)) (stackSem$alloc 10w ^alloc_gc_failure_state)`` (simp[alloc_with_const_source]);
val _ = observe "alloc_gc_failure_outcome" ``case FST(stackSem$alloc 10w ^alloc_gc_failure_state) of NONE => 0 | SOME Error => 1 | SOME(Halt _) => 2 | _ => 3``;
val alloc_missing_state = ``^allocation with gc_fun := (λ(wl,m,d,st). SOME(wl,m,FEMPTY))``;
val _ = alloc_frame "alloc_missing_frame" ``stackSem$alloc 10w ^alloc_missing_state`` alloc_missing_state;
val _ = checked "alloc_missing_clock" ``stackSem$alloc 10w (^alloc_missing_state with clock := 37) = (I ## (λt. t with clock := 37)) (stackSem$alloc 10w ^alloc_missing_state)`` (simp[alloc_with_const_source]);
val _ = observe "alloc_missing_outcome" ``case FST(stackSem$alloc 10w ^alloc_missing_state) of NONE => 0 | SOME Error => 1 | SOME(Halt _) => 2 | _ => 3``;
val alloc_bad_amount_state = ``^allocation with gc_fun := (λ(wl,m,d,st). SOME(wl,m,st |+ (AllocSize,Loc 1 0)))``;
val _ = alloc_frame "alloc_bad_amount_frame" ``stackSem$alloc 10w ^alloc_bad_amount_state`` alloc_bad_amount_state;
val _ = checked "alloc_bad_amount_clock" ``stackSem$alloc 10w (^alloc_bad_amount_state with clock := 37) = (I ## (λt. t with clock := 37)) (stackSem$alloc 10w ^alloc_bad_amount_state)`` (simp[alloc_with_const_source]);
val _ = observe "alloc_bad_amount_outcome" ``case FST(stackSem$alloc 10w ^alloc_bad_amount_state) of NONE => 0 | SOME Error => 1 | SOME(Halt _) => 2 | _ => 3``;
val alloc_bad_space_state = ``^allocation with gc_fun := (λ(wl,m,d,st). SOME(wl,m,FEMPTY |+ (AllocSize,Word 10w) |+ (TriggerGC,Word 20w)))``;
val _ = alloc_frame "alloc_bad_space_frame" ``stackSem$alloc 10w ^alloc_bad_space_state`` alloc_bad_space_state;
val _ = checked "alloc_bad_space_clock" ``stackSem$alloc 10w (^alloc_bad_space_state with clock := 37) = (I ## (λt. t with clock := 37)) (stackSem$alloc 10w ^alloc_bad_space_state)`` (simp[alloc_with_const_source]);
val _ = observe "alloc_bad_space_outcome" ``case FST(stackSem$alloc 10w ^alloc_bad_space_state) of NONE => 0 | SOME Error => 1 | SOME(Halt _) => 2 | _ => 3``;
val store_duplicate_state = copy;
val _ = store_frame "store_duplicate_frame" ``stackSem$store_const_sem 1 5 ^store_duplicate_state`` store_duplicate_state;
val _ = checked "store_duplicate_clock" ``stackSem$store_const_sem 1 5 (^store_duplicate_state with clock := 37) = (I ## (λt. t with clock := 37)) (stackSem$store_const_sem 1 5 ^store_duplicate_state)`` (simp[store_const_sem_with_const_source]);
val _ = observe "store_duplicate_outcome" ``case FST(stackSem$store_const_sem 1 5 ^store_duplicate_state) of NONE => 0 | SOME Error => 1 | _ => 3``;
val store_nonword_state = ``^copy with regs := (^copy).regs |+ (1,Loc 9 9)``;
val _ = store_frame "store_nonword_frame" ``stackSem$store_const_sem 4 5 ^store_nonword_state`` store_nonword_state;
val _ = checked "store_nonword_clock" ``stackSem$store_const_sem 4 5 (^store_nonword_state with clock := 37) = (I ## (λt. t with clock := 37)) (stackSem$store_const_sem 4 5 ^store_nonword_state)`` (simp[store_const_sem_with_const_source]);
val _ = observe "store_nonword_outcome" ``case FST(stackSem$store_const_sem 4 5 ^store_nonword_state) of NONE => 0 | SOME Error => 1 | _ => 3``;
val store_copy_failure_state = ``^copy with bitmaps := []``;
val _ = store_frame "store_copy_failure_frame" ``stackSem$store_const_sem 4 5 ^store_copy_failure_state`` store_copy_failure_state;
val _ = checked "store_copy_failure_clock" ``stackSem$store_const_sem 4 5 (^store_copy_failure_state with clock := 37) = (I ## (λt. t with clock := 37)) (stackSem$store_const_sem 4 5 ^store_copy_failure_state)`` (simp[store_const_sem_with_const_source]);
val _ = observe "store_copy_failure_outcome" ``case FST(stackSem$store_const_sem 4 5 ^store_copy_failure_state) of NONE => 0 | SOME Error => 1 | _ => 3``;
val store_success_alloc_state = copy;
val _ = store_frame "store_success_alloc_frame" ``stackSem$store_const_sem 4 5 ^store_success_alloc_state`` store_success_alloc_state;
val _ = checked "store_success_alloc_clock" ``stackSem$store_const_sem 4 5 (^store_success_alloc_state with clock := 37) = (I ## (λt. t with clock := 37)) (stackSem$store_const_sem 4 5 ^store_success_alloc_state)`` (simp[store_const_sem_with_const_source]);
val _ = observe "store_success_alloc_outcome" ``case FST(stackSem$store_const_sem 4 5 ^store_success_alloc_state) of NONE => 0 | SOME Error => 1 | _ => 3``;
val store_success_noalloc_state = ``^copy with use_alloc := F``;
val _ = store_frame "store_success_noalloc_frame" ``stackSem$store_const_sem 4 5 ^store_success_noalloc_state`` store_success_noalloc_state;
val _ = checked "store_success_noalloc_clock" ``stackSem$store_const_sem 4 5 (^store_success_noalloc_state with clock := 37) = (I ## (λt. t with clock := 37)) (stackSem$store_const_sem 4 5 ^store_success_noalloc_state)`` (simp[store_const_sem_with_const_source]);
val _ = observe "store_success_noalloc_outcome" ``case FST(stackSem$store_const_sem 4 5 ^store_success_noalloc_state) of NONE => 0 | SOME Error => 1 | _ => 3``;
val _ = checked "gc_success_clock" ``stackSem$gc (^alloc_success_state with clock := 37) = OPTION_MAP (λt. t with clock := 37) (stackSem$gc ^alloc_success_state)`` (simp[gc_with_const_source]);
val _ = checked "gc_gc_failure_clock" ``stackSem$gc (^alloc_gc_failure_state with clock := 37) = OPTION_MAP (λt. t with clock := 37) (stackSem$gc ^alloc_gc_failure_state)`` (simp[gc_with_const_source]);
val _ = checked "gc_missing_clock" ``stackSem$gc (^alloc_missing_state with clock := 37) = OPTION_MAP (λt. t with clock := 37) (stackSem$gc ^alloc_missing_state)`` (simp[gc_with_const_source]);
val _ = checked "gc_bad_amount_clock" ``stackSem$gc (^alloc_bad_amount_state with clock := 37) = OPTION_MAP (λt. t with clock := 37) (stackSem$gc ^alloc_bad_amount_state)`` (simp[gc_with_const_source]);

val _ = observe "mixed_state1_result80" ``FST (stackSem$store_const_sem 1 5 (s:(1,'c,'ffi)stackSem$state) : 80 stackSem$result option # (1,'c,'ffi)stackSem$state)``;
val _ = observe "mixed_state80_result1" ``FST (stackSem$store_const_sem 1 5 (s:(80,'c,'ffi)stackSem$state) : 1 stackSem$result option # (80,'c,'ffi)stackSem$state)``;
