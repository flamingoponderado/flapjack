(* Full original StackProps shared-memory clock proofs replayed literally;
source/type captures and concrete observations are review evidence only. *)
load "bossLib";
load "preamble";
load "stackPropsTheory";
open bossLib HolKernel Parse preamble stackPropsTheory stackSemTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun captureTypes label th = (print(label ^ "="); app (fn v =>
 print (term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";"))
 (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val sh_mem_load_with_const_source = prove (``(sh_mem_load r x (y with clock := k)) = (I ## (\s. s with clock := k)) (sh_mem_load r x y)``,
  simp[sh_mem_load_def,ffiTheory.call_FFI_def]>>every_case_tac>>
  fs[]);
val _ = capture "sh_mem_load_with_const" sh_mem_load_with_const_source;
val _ = captureTypes "sh_mem_load_with_const_types" sh_mem_load_with_const_source;
val sh_mem_store_with_const_source = prove (``(sh_mem_store x y (z with clock := k)) = (I ## (\s. s with clock := k)) (sh_mem_store x y z)``,
  gs[sh_mem_store_def,ffiTheory.call_FFI_def]>>every_case_tac>>
  gs[]);
val _ = capture "sh_mem_store_with_const" sh_mem_store_with_const_source;
val _ = captureTypes "sh_mem_store_with_const_types" sh_mem_store_with_const_source;
val sh_mem_load32_with_const_source = prove (``(sh_mem_load32 r x (y with clock := k)) = (I ## (\s. s with clock := k)) (sh_mem_load32 r x y)``,
  simp[sh_mem_load32_def,ffiTheory.call_FFI_def]>>every_case_tac>>
  fs[]);
val _ = capture "sh_mem_load32_with_const" sh_mem_load32_with_const_source;
val _ = captureTypes "sh_mem_load32_with_const_types" sh_mem_load32_with_const_source;
val sh_mem_store32_with_const_source = prove (``(sh_mem_store32 x y (z with clock := k)) = (I ## (\s. s with clock := k)) (sh_mem_store32 x y z)``,
  gs[sh_mem_store32_def,ffiTheory.call_FFI_def]>>every_case_tac>>
  gs[]);
val _ = capture "sh_mem_store32_with_const" sh_mem_store32_with_const_source;
val _ = captureTypes "sh_mem_store32_with_const_types" sh_mem_store32_with_const_source;
val sh_mem_load16_with_const_source = prove (``(sh_mem_load16 r x (y with clock := k)) = (I ## (\s. s with clock := k)) (sh_mem_load16 r x y)``,
  simp[sh_mem_load16_def,ffiTheory.call_FFI_def]>>every_case_tac>>
  fs[]);
val _ = capture "sh_mem_load16_with_const" sh_mem_load16_with_const_source;
val _ = captureTypes "sh_mem_load16_with_const_types" sh_mem_load16_with_const_source;
val sh_mem_store16_with_const_source = prove (``(sh_mem_store16 x y (z with clock := k)) = (I ## (\s. s with clock := k)) (sh_mem_store16 x y z)``,
  gs[sh_mem_store16_def,ffiTheory.call_FFI_def]>>every_case_tac>>
  gs[]);
val _ = capture "sh_mem_store16_with_const" sh_mem_store16_with_const_source;
val _ = captureTypes "sh_mem_store16_with_const_types" sh_mem_store16_with_const_source;
val sh_mem_load_byte_with_const_source = prove (``(sh_mem_load_byte r x (y with clock := k)) = (I ## (\s. s with clock := k)) (sh_mem_load_byte r x y)``,
  simp[sh_mem_load_byte_def,ffiTheory.call_FFI_def]>>every_case_tac>>
  fs[]);
val _ = capture "sh_mem_load_byte_with_const" sh_mem_load_byte_with_const_source;
val _ = captureTypes "sh_mem_load_byte_with_const_types" sh_mem_load_byte_with_const_source;
val sh_mem_store_byte_with_const_source = prove (``(sh_mem_store_byte x y (z with clock := k)) = (I ## (\s. s with clock := k)) (sh_mem_store_byte x y z)``,
  gs[sh_mem_store_byte_def,ffiTheory.call_FFI_def]>>every_case_tac>>
  gs[]);
val _ = capture "sh_mem_store_byte_with_const" sh_mem_store_byte_with_const_source;
val _ = captureTypes "sh_mem_store_byte_with_const_types" sh_mem_store_byte_with_const_source;
val sh_mem_op_with_const_source = prove (``(sh_mem_op op x y (z with clock := k)) = (I ## (\s. s with clock := k)) (sh_mem_op op x y z)``,
  gs[oneline sh_mem_op_def] >>
  TOP_CASE_TAC >> gs[]);
val _ = capture "sh_mem_op_with_const" sh_mem_op_with_const_source;
val _ = captureTypes "sh_mem_op_with_const_types" sh_mem_op_with_const_source;
val sh_mem_op_const_source = prove (``sh_mem_op op a r s = (res,t) ⇒
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
    t.compile_oracle = s.compile_oracle``,
  strip_tac>>Cases_on`op` >>
  fs[sh_mem_op_def,sh_mem_load_def,sh_mem_store_def,
     sh_mem_load_byte_def,sh_mem_store_byte_def,
     sh_mem_load16_def,sh_mem_store16_def,
     sh_mem_load32_def,sh_mem_store32_def,
     ffiTheory.call_FFI_def] >>
  every_case_tac >> gvs[get_var_def]);
val _ = capture "sh_mem_op_const" sh_mem_op_const_source;
val _ = captureTypes "sh_mem_op_const_types" sh_mem_op_const_source;
val _ = show_types := false;
fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rhs (concl th));
    print "\n"
  end;

val s = ``s:(64,'c,num) stackSem$state``;
val inc = ``<| oracle := (\n (st:num) conf bytes. Oracle_return (st + 1) (MAP (\b. b + 1w) bytes));
               ffi_state := 0; io_events := [] |>``;
val divffi = ``<| oracle := (\n (st:num) conf bytes. Oracle_final FFI_diverged);
               ffi_state := 0; io_events := [] |>``;
val st = ``^s with <| sh_mdomain := {8w}; ffi := ^inc;
                      regs := (FEMPTY |+ (3, Word 0x1122w) |+ (4, Loc 1 0));
                      stack := []; clock := 37 |>``;
val proj = ``\(r:(64) stackSem$result option, t:(64,'c,num) stackSem$state).
 ((case r of NONE => 0 | SOME Error => 1 | SOME(FinalFFI _) => 2 | _ => 3),
 t.clock,t.ffi.ffi_state,LENGTH t.ffi.io_events,
 (case FLOOKUP t.regs 5 of SOME (Word w) => w2n w | _ => 0))``;
val _ = print_eval "store" ``^proj (stackSem$sh_mem_op Store 3 8w ^st)``;
val _ = print_eval "load" ``^proj (stackSem$sh_mem_op Load 5 8w ^st)``;
val _ = print_eval "store8" ``^proj (stackSem$sh_mem_op Store8 3 9w ^st)``;
val _ = print_eval "load8" ``^proj (stackSem$sh_mem_op Load8 5 9w ^st)``;
val _ = print_eval "store16" ``^proj (stackSem$sh_mem_op Store16 3 10w ^st)``;
val _ = print_eval "load16" ``^proj (stackSem$sh_mem_op Load16 5 10w ^st)``;
val _ = print_eval "store32" ``^proj (stackSem$sh_mem_op Store32 3 12w ^st)``;
val _ = print_eval "load32" ``^proj (stackSem$sh_mem_op Load32 5 12w ^st)``;
val _ = print_eval "load_outside" ``^proj (stackSem$sh_mem_op Load 5 16w ^st)``;
val _ = print_eval "store8_outside" ``^proj (stackSem$sh_mem_op Store8 3 17w ^st)``;
val _ = print_eval "load_word_unaligned" ``^proj (stackSem$sh_mem_op Load 5 9w ^st)``;
val _ = print_eval "store_word_unaligned" ``^proj (stackSem$sh_mem_op Store 3 9w ^st)``;
val _ = print_eval "load_final" ``^proj (stackSem$sh_mem_op Load 5 8w (^st with ffi := ^divffi))``;
val _ = print_eval "store_final" ``^proj (stackSem$sh_mem_op Store 3 8w (^st with ffi := ^divffi))``;
val _ = print_eval "store_loc" ``^proj (stackSem$sh_mem_op Store 4 8w ^st)``;
fun frame label q state =
 let val tm = ``let (res,t) = ^q in t.clock = (^state).clock /\ t.use_alloc = (^state).use_alloc /\ t.use_store = (^state).use_store /\ t.use_stack = (^state).use_stack /\ t.code = (^state).code /\ t.be = (^state).be /\ t.gc_fun = (^state).gc_fun /\ t.mdomain = (^state).mdomain /\ t.sh_mdomain = (^state).sh_mdomain /\ t.bitmaps = (^state).bitmaps /\ t.compile = (^state).compile /\ t.compile_oracle = (^state).compile_oracle``;
     val th = prove(tm, Cases_on `^q` >> imp_res_tac sh_mem_op_const >> fs[])
 in if null(hyp th) andalso aconv (concl th) tm then print(label ^ "=T\n") else raise Fail "native frame proof has hypotheses or changed conclusion" end;
val _ = frame "store_frame" ``stackSem$sh_mem_op Store 3 8w ^st`` st;
val _ = frame "load_frame" ``stackSem$sh_mem_op Load 5 8w ^st`` st;
val _ = frame "store8_frame" ``stackSem$sh_mem_op Store8 3 9w ^st`` st;
val _ = frame "load8_frame" ``stackSem$sh_mem_op Load8 5 9w ^st`` st;
val _ = frame "store16_frame" ``stackSem$sh_mem_op Store16 3 10w ^st`` st;
val _ = frame "load16_frame" ``stackSem$sh_mem_op Load16 5 10w ^st`` st;
val _ = frame "store32_frame" ``stackSem$sh_mem_op Store32 3 12w ^st`` st;
val _ = frame "load32_frame" ``stackSem$sh_mem_op Load32 5 12w ^st`` st;
val _ = frame "load_outside_frame" ``stackSem$sh_mem_op Load 5 16w ^st`` st;
val _ = frame "store8_outside_frame" ``stackSem$sh_mem_op Store8 3 17w ^st`` st;
val _ = frame "load_word_unaligned_frame" ``stackSem$sh_mem_op Load 5 9w ^st`` st;
val _ = frame "store_word_unaligned_frame" ``stackSem$sh_mem_op Store 3 9w ^st`` st;
val _ = frame "load_final_frame" ``stackSem$sh_mem_op Load 5 8w (^st with ffi := ^divffi)`` ``^st with ffi := ^divffi``;
val _ = frame "store_final_frame" ``stackSem$sh_mem_op Store 3 8w (^st with ffi := ^divffi)`` ``^st with ffi := ^divffi``;
val _ = frame "store_loc_frame" ``stackSem$sh_mem_op Store 4 8w ^st`` st;
