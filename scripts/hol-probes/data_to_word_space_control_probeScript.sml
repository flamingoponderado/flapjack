load "preamble"; load "dataSemTheory"; load "data_to_word_gcProofTheory"; load "data_to_word_assignProofTheory";
open HolKernel Parse boolLib bossLib preamble dataSemTheory data_to_word_gcProofTheory
  data_to_wordTheory data_to_word_assignProofTheory sptreeTheory;
val _ = new_theory "flapjack_data_to_word_space_control_replay";
val _ = Globals.linewidth := 1000000;
(* Literal replays of data_to_wordProofScript.sml lemmas. *)
Theorem do_space_code_const:
  do_space op vs (s:('a,'b) dataSem$state) = SOME s1 ==>
  s1.code = s.code /\ s1.compile_oracle = s.compile_oracle
Proof
  strip_tac \\ gvs[do_space_def,AllCaseEqs(),consume_space_def]
QED

Theorem MEM_join_env_cut_env:
  ∀(a:v # α word_loc) t r s.
    MEM a (join_env x (toAList (inter t (adjust_set x)))) ∧
    dataSem$cut_env r s = SOME x ⇒
    MEM a (join_env s (toAList (inter t (adjust_set s))))
Proof
  fs [join_env_def,MEM_MAP,EXISTS_PROD,MEM_FILTER]
  \\ rw [] \\ gvs [cut_env_def]
  \\ fs [MEM_toAList]
  \\ last_assum $ irule_at Any \\ simp []
  \\ fs [lookup_inter_alt,IN_domain_adjust_set_inter]
  \\ rw [] \\ fs []
  \\ imp_res_tac IN_adjust_set_IN
QED

Theorem cut_state_opt_ffi:
  dataSem$cut_state_opt names_opt r = SOME v1 ==> v1.ffi = r.ffi
Proof
  rw [] \\ gvs [cut_state_def,cut_env_def,cut_state_opt_def,AllCaseEqs()]
QED

fun show label th =
  if null (hyp th) then
    (print label; print "="; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "do_space_code_const_typed" do_space_code_const;
val _ = show "cut_state_opt_ffi_typed" cut_state_opt_ffi;
val _ = show "MEM_join_env_cut_env_typed" MEM_join_env_cut_env;
