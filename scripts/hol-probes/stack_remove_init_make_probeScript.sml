load "preamble"; load "helperLib"; load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib stack_removeProofTheory
 stack_removeTheory stackLangTheory stackSemTheory stackPropsTheory set_sepTheory
 miscTheory wordsTheory listTheory addressTheory;
val _ = Globals.linewidth := 1000000;

(* stack_removeProofScript.sml:3053-3089, 3839-3854, 4007-4067 *)
val _ = (print "get_stack_heap_limit_prime_def_statement="; print_term (concl get_stack_heap_limit'_def); print "\n");
val _ = print ("get_stack_heap_limit_prime_def_type=" ^ type_to_string (type_of ``get_stack_heap_limit'``) ^ "\n");
val _ = (print "get_stack_heap_limit_def_statement="; print_term (concl get_stack_heap_limit_def); print "\n");
val _ = print ("get_stack_heap_limit_def_type=" ^ type_to_string (type_of ``get_stack_heap_limit``) ^ "\n");
val _ = (print "read_pointers_def_statement="; print_term (concl read_pointers_def); print "\n");
val _ = print ("read_pointers_def_type=" ^ type_to_string (type_of ``read_pointers``) ^ "\n");
val _ = (print "make_init_opt_def_statement="; print_term (concl make_init_opt_def); print "\n");
val _ = print ("make_init_opt_def_type=" ^ type_to_string (type_of ``make_init_opt``) ^ "\n");
val _ = (print "init_pre_def_statement="; print_term (concl init_pre_def); print "\n");
val _ = print ("init_pre_def_type=" ^ type_to_string (type_of ``init_pre``) ^ "\n");
val _ = (print "make_init_any_def_statement="; print_term (concl make_init_any_def); print "\n");
val _ = print ("make_init_any_def_type=" ^ type_to_string (type_of ``make_init_any``) ^ "\n");
val _ = (print "discharge_these_def_statement="; print_term (concl discharge_these_def); print "\n");
val _ = print ("discharge_these_def_type=" ^ type_to_string (type_of ``discharge_these``) ^ "\n");
val _ = (print "propagate_these_def_statement="; print_term (concl propagate_these_def); print "\n");
val _ = print ("propagate_these_def_type=" ^ type_to_string (type_of ``propagate_these``) ^ "\n");

fun ev tm = term_to_string (rhs (concl (EVAL tm)));
val _ = print ("limit_prime_64_a=" ^ ev ``get_stack_heap_limit' 1000 (0x1000w:word64) (0x5000w:word64) (0x9000w:word64)`` ^ "\n");
val _ = print ("limit_prime_64_b=" ^ ev ``get_stack_heap_limit' (2 ** 62) (0x1000w:word64) (0x5000w:word64) (0x9000w:word64)`` ^ "\n");
val _ = print ("limit_prime_64_c=" ^ ev ``get_stack_heap_limit' 3 (0x1000w:word64) (0x5000w:word64) (0x9000w:word64)`` ^ "\n");
val _ = print ("limit_prime_64_d=" ^ ev ``get_stack_heap_limit' 1000 (0x9000w:word64) (0x1000w:word64) (0x5000w:word64)`` ^ "\n");
val _ = print ("limit_prime_32_a=" ^ ev ``get_stack_heap_limit' 100 (0x100w:word32) (0x900w:word32) (0x2000w:word32)`` ^ "\n");
val _ = print ("limit_prime_32_b=" ^ ev ``get_stack_heap_limit' (2 ** 30) (0x100w:word32) (0x900w:word32) (0x2000w:word32)`` ^ "\n");
val _ = print ("limit_prime_mixed_a=" ^ ev ``get_stack_heap_limit' 1000 (0x1000w:word32) (0x5000w:word16) (0x9000w:word64)`` ^ "\n");
val _ = print ("limit_prime_mixed_b=" ^ ev ``get_stack_heap_limit' 3 (0xFFFF1000w:word32) (0x5000w:word64) (0x2000w:word32)`` ^ "\n");
val _ = let val (_, body) = strip_forall (concl get_stack_heap_limit'_def)
            val (_, args) = strip_comb (lhs body)
        in print ("get_stack_heap_limit_prime_arg_types=" ^
             String.concatWith ", " (map (type_to_string o type_of) args) ^ "\n") end;
val _ = print ("limit_64_a=" ^ ev ``get_stack_heap_limit 1000 (0x1000w:word64, 0x5000w, 0x9000w)`` ^ "\n");
val _ = print ("limit_64_b=" ^ ev ``get_stack_heap_limit 1000 (0x1000w:word64, 0x1100w, 0x9000w)`` ^ "\n");
val _ = print ("limit_64_c=" ^ ev ``get_stack_heap_limit 7 (0xFFFFFFFFFFFFF000w:word64, 0x10w, 0x2000w)`` ^ "\n");
val _ = print ("limit_32_a=" ^ ev ``get_stack_heap_limit 50 (0x1000w:word32, 0x1004w, 0x3000w)`` ^ "\n");
val _ = print ("limit_32_b=" ^ ev ``get_stack_heap_limit 5000 (0x1000w:word32, 0x2000w, 0x8000w)`` ^ "\n");
