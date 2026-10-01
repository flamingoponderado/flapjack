(* Original flatten fallback and section convention observations.
   The Flapjack guard is untagged infrastructure with no HOL original. *)
load "bossLib";
load "preamble";
load "stack_to_labTheory";
open bossLib HolKernel Parse preamble;
val _ = Globals.linewidth := 10000;
fun emit label tm = print (label ^ "=" ^ term_to_string (rconc (EVAL tm)) ^ "\n");
val _ = emit "guard_source_get_drop" ``stack_to_lab$flatten T (Get 2 EndOfHeap : 64 stackLang$prog) 7 2 [] []``;
val _ = emit "guard_source_alloc_drop" ``stack_to_lab$flatten T (Alloc 17 : 64 stackLang$prog) 7 2 [] []``;
val _ = emit "guard_source_stackstore_drop" ``stack_to_lab$flatten T (StackStore 17 2 : 64 stackLang$prog) 7 2 [] []``;
val _ = emit "guard_source_datawrite_drop" ``stack_to_lab$flatten T (DataBufferWrite 2 3 : 64 stackLang$prog) 7 2 [] []``;
val _ = emit "guard_source_skip_section" ``stack_to_lab$prog_to_section (7, Skip : 64 stackLang$prog)``;
val _ = emit "guard_source_seq_section" ``stack_to_lab$prog_to_section (7, Seq Tick Skip : 64 stackLang$prog)``;
val _ = emit "guard_source_loc_section" ``stack_to_lab$prog_to_section (7, LocValue 2 17 29 : 64 stackLang$prog)``;
