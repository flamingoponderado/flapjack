load "preamble";
load "loop_to_wordProofTheory";
open bossLib HolKernel Parse preamble loop_to_wordProofTheory loop_to_wordTheory sptreeTheory;
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = temp_delsimps ["fromAList_def", "domain_union", "domain_inter", "domain_difference", "domain_map", "sptree.map_def", "sptree.lookup_rwts", "sptree.insert_notEmpty", "sptree.isEmpty_union"];
val first_compile_prog_all_distinct = GEN_ALL(prove(``!prog. ALL_DISTINCT (MAP FST prog) ==>
    ALL_DISTINCT (MAP FST (compile_prog prog))``, rw [] >>
  fs [loop_to_wordTheory.compile_prog_def] >>
  fs [MAP_MAP_o] >>
  qmatch_goalsub_abbrev_tac ‘MAP ls _’ >>
  ‘MAP ls prog = MAP FST prog’ by (
    fs [Abbr ‘ls’] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    rw [] >>
    cases_on ‘EL n prog’ >> fs [] >>
    cases_on ‘r’ >> fs []) >>
  fs []));
val _ = (print "first_compile_prog_all_distinct_source_replay="; print_thm first_compile_prog_all_distinct; print "\n");
val first_compile_all_distinct = GEN_ALL(prove(``!prog. ALL_DISTINCT (MAP FST prog) ==>
    ALL_DISTINCT (MAP FST (compile prog))``, rw [compile_def] >>
  match_mp_tac first_compile_prog_all_distinct >> fs []));
val _ = (print "first_compile_all_distinct_source_replay="; print_thm first_compile_all_distinct; print "\n");
val mem_prog_mem_compile_prog = GEN_ALL(prove(``!prog name params body.
     MEM (name,params,body) prog ==>
     MEM (name,LENGTH params + 1,comp_func name params body)
         (compile_prog prog)``, rw [] >>
  fs [MEM_EL] >>
  qexists_tac ‘n’ >>
  fs [compile_prog_def] >>
  qmatch_goalsub_abbrev_tac ‘MAP ls _’ >>
  ‘EL n (MAP ls prog) = ls (EL n prog)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [Abbr ‘ls’] >>
  cases_on ‘EL n prog’ >> fs [] >>
  cases_on ‘r’ >> fs []));
val _ = (print "mem_prog_mem_compile_prog_source_replay="; print_thm mem_prog_mem_compile_prog; print "\n");
val lookup_prog_some_lookup_compile_prog = GEN_ALL(prove(``!prog name params body. lookup name (fromAList prog) = SOME (params,body) ==>
  lookup name (fromAList (compile_prog prog)) =
  SOME (LENGTH params + 1,comp_func name params body)``, Induct >> rw []
  >- fs [compile_prog_def, fromAList_def, lookup_def] >>
  fs [compile_prog_def] >>
  cases_on ‘h’ >> fs [] >>
  cases_on ‘r’ >> fs [] >>
  fs [fromAList_def] >>
  fs [lookup_insert] >>
  TOP_CASE_TAC >> fs []));
val _ = (print "lookup_prog_some_lookup_compile_prog_source_replay="; print_thm lookup_prog_some_lookup_compile_prog; print "\n");
fun out label th = (print(label ^ "="); print_term(rconc th); print "\n");
val rows = ``[(7:num,[1]:num list,loopLang$Skip);(7:num,[]:num list,loopLang$Tick)] : (num # num list # 64 word loopLang$prog) list``;
val distinct = ``[(7:num,[1]:num list,loopLang$Skip);(8:num,[]:num list,loopLang$Tick)] : (num # num list # 64 word loopLang$prog) list``;
val _ = out "pn_duplicate_result" (EVAL ``compile_prog ^rows``);
val _ = out "pn_distinct_result" (EVAL ``compile_prog ^distinct``);
val _ = out "pn_duplicate_names" (EVAL ``ALL_DISTINCT (MAP FST (compile_prog ^rows))``);
val _ = out "pn_distinct_names" (EVAL ``ALL_DISTINCT (MAP FST (compile_prog ^distinct))``);
val _ = out "pn_first_lookup" (EVAL ``lookup 7 (fromAList (compile_prog ^rows))``);
val _ = out "pn_missing_lookup" (EVAL ``lookup 9 (fromAList (compile_prog ^rows))``);
val distinctGuard = EQT_ELIM (EVAL ``ALL_DISTINCT (MAP FST ^distinct)``);
val _ = out "pn_distinct_theorem" (EQT_INTRO (MATCH_MP (ISPEC distinct first_compile_prog_all_distinct) distinctGuard));
val _ = out "pn_compile_theorem" (EQT_INTRO (MATCH_MP (ISPEC distinct first_compile_all_distinct) distinctGuard));
val memberGuard = EQT_ELIM (EVAL ``MEM (7:num,[1]:num list,loopLang$Skip) ^rows``);
val memberResult = MATCH_MP (ISPECL [rows,``7:num``,``[1]:num list``,``loopLang$Skip:64 word loopLang$prog``] mem_prog_mem_compile_prog) memberGuard;
val _ = out "pn_member_theorem" (EQT_INTRO memberResult);
val lookupGuard = EVAL ``lookup 7 (fromAList ^rows)``;
val lookupResult = MATCH_MP (ISPECL [rows,``7:num``,``[1]:num list``,``loopLang$Skip:64 word loopLang$prog``] lookup_prog_some_lookup_compile_prog) lookupGuard;
val _ = out "pn_lookup_theorem" (EQT_INTRO lookupResult);
