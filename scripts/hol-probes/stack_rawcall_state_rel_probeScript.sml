load "preamble"; load "stack_rawcallProofTheory";
open HolKernel Parse bossLib preamble stack_rawcallProofTheory stackSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "state_rel_type="; print_type(type_of ``state_rel``); print "\n");
val _ = (print "state_rel_definition="; print_term(concl state_rel_def));
val self = prove(``state_ok i s.code ==> state_rel i s s``,
  PURE_REWRITE_TAC[state_rel_def] >> strip_tac >> qexists_tac `s.code` >> conj_tac >- simp[] >>
  conj_tac >- simp[state_component_equality] >>
  conj_tac >- asm_rewrite_tac[] >>
  rpt strip_tac >> qexists_tac `LN` >>
  simp[state_ok_def,sptreeTheory.lookup_def,comp_LN]);
val _ = (print "state_rel_self="; print_term(concl self));
val oracle = prove(``state_rel i s t ==> t.compile_oracle = s.compile_oracle``,
  rw[state_rel_def] >> simp[]);
val _ = (print "state_rel_oracle="; print_term(concl oracle));
