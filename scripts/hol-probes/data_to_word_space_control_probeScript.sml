load "preamble"; load "dataSemTheory";
open HolKernel Parse boolLib bossLib preamble dataSemTheory;
val _ = new_theory "flapjack_data_to_word_space_control_replay";
val _ = Globals.linewidth := 1000000;
(* Literal replays of data_to_wordProofScript.sml's two lemmas. *)
Theorem do_space_code_const:
  do_space op vs (s:('a,'b) dataSem$state) = SOME s1 ==>
  s1.code = s.code /\ s1.compile_oracle = s.compile_oracle
Proof
  strip_tac \\ gvs[do_space_def,AllCaseEqs(),consume_space_def]
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
