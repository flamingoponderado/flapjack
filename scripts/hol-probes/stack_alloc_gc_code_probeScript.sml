load "preamble"; load "stack_allocTheory";
open bossLib; open HolKernel Parse; open preamble; open stack_allocTheory;

val _ = Globals.linewidth := 1000000;
val print_eval = fn label => fn q =>
  (print label; print "="; print (term_to_string (rconc (EVAL q))); print "\n");

fun conf k = ``<| tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16;
                  has_div := F; has_longdiv := F; has_fp_ops := F; has_fp_tern := F;
                  be := F; call_empty_ffi := F; gc_kind := ^k |>``;

val _ = print_eval "sa_memcpy_code" ``(memcpy_code : 64 stackLang$prog)``;
val _ = print_eval "sa_clear_top" ``(clear_top_inst 5 3 : 64 stackLang$prog)``;
val _ = print_eval "sa_set_new_trigger_32" ``(SetNewTrigger 8 3 [10] : 32 stackLang$prog)``;
val _ = print_eval "sa_gc_code_none" ``(word_gc_code ^(conf ``None``) : 64 stackLang$prog)``;
val _ = print_eval "sa_gc_code_simple" ``(word_gc_code ^(conf ``Simple``) : 64 stackLang$prog)``;
val _ = print_eval "sa_gc_code_gen" ``(word_gc_code ^(conf ``Generational [10]``) : 64 stackLang$prog)``;
val _ = print_eval "sa_gc_code_gen_nil" ``(word_gc_code ^(conf ``Generational []``) : 64 stackLang$prog)``;
val _ = print_eval "sa_gc_code_gen_32" ``(word_gc_code ^(conf ``Generational [10]``) : 32 stackLang$prog)``;
val prog1 = ``(Seq (Alloc 3) (Call (SOME (Alloc 1,0,5,7)) (INL 9)
   (SOME (StoreConsts 1 2 (SOME 3),4,6))) : 64 stackLang$prog)``;
val prog2 = ``(If Equal 1 (Reg 2) (Loop (Seq (StoreConsts 1 2 NONE) (Alloc 4)))
   (Call NONE (INR 3) (SOME (Alloc 2,1,8))) : 64 stackLang$prog)``;
val _ = print_eval "sa_prog_comp_1" ``prog_comp (10, ^prog1)``;
val _ = print_eval "sa_prog_comp_2" ``prog_comp (11, ^prog2)``;
val _ = print_eval "sa_compile_none" ``compile ^(conf ``None``) [(10, ^prog1); (12, Alloc 5 : 64 stackLang$prog)]``;
