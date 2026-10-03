load "preamble"; load "stack_to_labProofTheory";
open HolKernel Parse bossLib preamble stack_to_labProofTheory stack_namesProofTheory
 stack_allocProofTheory stack_removeProofTheory stack_to_labTheory stackSemTheory
 stackPropsTheory stack_allocTheory labSemTheory labPropsTheory semanticsPropsTheory;
val _ = Globals.linewidth := 1000000;
(* The script-local simpset changes of stack_to_labProofScript.sml:14-22. *)
val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]
val _ = temp_delsimps ["fromAList_def", "domain_union",
                       "domain_inter", "domain_difference",
                       "domain_map", "sptree.map_def", "sptree.lookup_rwts",
                       "sptree.insert_notEmpty", "sptree.isEmpty_union"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1
fun checked label th =
  (if null (hyp th) then () else raise Fail "open HOL hypotheses";
   print (label ^ "="); print_term (concl th); print "\n");
fun typed_statement label th =
  (show_types := true;
   print (label ^ "="); print_term (concl th); print "\n";
   show_types := false);
fun type_list label th =
  (show_types := true;
   print (label ^ "=");
   app (fn v => print (term_to_string v ^ ":" ^ type_to_string (type_of v) ^ ";"))
     (fst (strip_forall (concl th)) @ free_vars (concl th));
   print "\n";
   show_types := false);

(* Exported originals and local replays of stack_to_labProofScript.sml:3027-3192. *)
val _ = checked "make_init_def_statement" stack_to_labProofTheory.make_init_def;
val _ = typed_statement "make_init_def_statement_typed" stack_to_labProofTheory.make_init_def;
val _ = type_list "make_init_def_statement_types" stack_to_labProofTheory.make_init_def;

(* stack_to_labProofScript.sml:3047-3049, replayed. *)
val make_init_semantics = flatten_semantics
  |> Q.INST [`s1`|->`make_init code coracle regs save_regs (s:('a,'c,'ffi)labSem$state)`,`s2`|->`s`]
  |> SIMP_RULE std_ss [EVAL ``(make_init code coracle regs save_regs s).code``];
val _ = checked "make_init_semantics_statement" make_init_semantics;
val _ = typed_statement "make_init_semantics_statement_typed" make_init_semantics;
val _ = type_list "make_init_semantics_statement_types" make_init_semantics;

val _ = checked "memory_assumption_def_statement" memory_assumption_def;
val _ = typed_statement "memory_assumption_def_statement_typed" memory_assumption_def;
val _ = type_list "memory_assumption_def_statement_types" memory_assumption_def;

(* stack_to_labProofScript.sml:3132-3150, replayed. *)
val halt_assum_lemma = Q.prove(
  `  halt_assum (:'ffi#'c)
     (fromAList (stack_names$compile f
       (compile jump off gen max_heap k l code)))`,
  fs [halt_assum_def] \\ rw []
  \\ fs [stackSemTheory.evaluate_def,
         stackSemTheory.find_code_def]
  \\ fs [stack_namesTheory.compile_def,
         stack_namesTheory.prog_comp_def,
         stack_removeTheory.compile_def,
         stack_removeTheory.init_stubs_def,
         subspt_def,
         lookup_fromAList,domain_fromAList,
         EVAL ``stack_names$comp f (halt_inst 0w)``]
  \\ first_x_assum(qspec_then`1`mp_tac) \\ simp[]
  \\ fs [stackSemTheory.evaluate_def,EVAL ``inst (Const n 0w) (dec_clock s)``,
         get_var_def,FLOOKUP_UPDATE]);
val _ = checked "halt_assum_lemma_statement" halt_assum_lemma;
val _ = typed_statement "halt_assum_lemma_statement_typed" halt_assum_lemma;
val _ = type_list "halt_assum_lemma_statement_types" halt_assum_lemma;

(* stack_to_labProofScript.sml:3152-3159, replayed. *)
val FLOOKUP_regs = Q.prove(
  `  !regs n v f s.
      FLOOKUP (FEMPTY |++ MAP (λr. (r,read_reg r s)) regs) n = SOME v ==>
      read_reg n s = v`,
  recInduct SNOC_INDUCT \\ fs [FUPDATE_LIST,FOLDL_SNOC,MAP_SNOC]
  \\ fs [FLOOKUP_UPDATE] \\ rw [] \\ Cases_on `x = n` \\ fs []);
val _ = checked "FLOOKUP_regs_statement" FLOOKUP_regs;
val _ = typed_statement "FLOOKUP_regs_statement_typed" FLOOKUP_regs;
val _ = type_list "FLOOKUP_regs_statement_types" FLOOKUP_regs;

val _ = checked "state_rel_make_init_statement" state_rel_make_init;
val _ = typed_statement "state_rel_make_init_statement_typed" state_rel_make_init;
val _ = type_list "state_rel_make_init_statement_types" state_rel_make_init;
